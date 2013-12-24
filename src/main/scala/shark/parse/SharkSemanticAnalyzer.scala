/*
 * Copyright (C) 2012 The Regents of The University California.
 * All rights reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package shark.parse

import org.apache.hadoop.fs.Path
import org.apache.hadoop.hive.conf.HiveConf
import org.apache.hadoop.hive.metastore.api.{FieldSchema, MetaException}
import org.apache.hadoop.hive.metastore.Warehouse
import org.apache.hadoop.hive.ql.exec.{ColumnStatsTask, DDLTask, FetchTask, MoveTask, TaskFactory}
import org.apache.hadoop.hive.ql.exec.{FileSinkOperator => HiveFileSinkOperator, Operator => HiveOp}
import org.apache.hadoop.hive.ql.metadata.HiveException
import org.apache.hadoop.hive.ql.parse._
import org.apache.hadoop.hive.ql.plan._
import org.apache.hadoop.hive.ql.session.SessionState

import shark.{CachedTableRecovery, LogHelper, SharkConfVars, SharkEnv, SharkOptimizer, Utils}
import shark.execution.{HiveOperator, Operator, OperatorFactory, RDDUtils, ReduceSinkOperator,
  SparkWork, TerminalOperator}
import shark.optimizer.{SharkOptimizerStatistics, JoinOptimizer}

import shark.memstore2.{CacheType, ColumnarSerDe, MemoryMetadataManager}
import org.apache.hadoop.hive.ql.parse.PTFInvocationSpec.PartitionedTableFunctionSpec
import org.apache.hadoop.hive.ql.QueryProperties

import java.util.{ArrayList => JavaArrayList, List => JavaList, Map => JavaMap, HashMap => JavaHashMap, HashSet => JavaHashSet }
import scala.collection.JavaConversions._

/**
 * Shark's version of Hive's SemanticAnalyzer. In SemanticAnalyzer,
 * genMapRedTasks() breaks the query plan down to different stages because of
 * mapreduce. We want our query plan to stay intact as a single tree. Since
 * genMapRedTasks is private, we have to overload analyzeInternal() to use our
 * own genMapRedTasks().
 */
class SharkSemanticAnalyzer(conf: HiveConf) extends SemanticAnalyzer(conf) with LogHelper {

  var _resSchema: JavaList[FieldSchema] = null

  /**
   * This is used in driver to get the result schema.
   */
  override def getResultSchema() = _resSchema

  /**
   * Override SemanticAnalyzer.analyzeInternal to handle CTAS caching.
   */
  override def analyzeInternal(ast: ASTNode): Unit = {
    val qb = getQB()
    var pctx = getParseContext()
    pctx.setQB(qb)
    pctx.setParseTree(ast)
    initParseCtx(pctx)
    var child: ASTNode = ast

    logInfo("Starting Shark Semantic Analysis")

    //TODO: can probably reuse Hive code for this
    // analyze create table command
    var cacheMode = CacheType.NONE
    var isCTAS = false
    var shouldReset = false

    if (ast.getToken().getType() == HiveParser.TOK_CREATETABLE) {
      init()
      super.analyzeInternal(ast)
      for (ch <- ast.getChildren) {
        ch.asInstanceOf[ASTNode].getToken.getType match {
          case HiveParser.TOK_QUERY => {
            isCTAS = true
            child = ch.asInstanceOf[ASTNode]
          }
          case _ =>
            Unit
        }
      }

      // The table descriptor can be null if the CTAS has an
      // "if not exists" condition.
      val createTableDesc = getParseContext.getQB.getTableDesc
      if (!isCTAS || createTableDesc == null) {
        return
      } else {
        val checkTableName = SharkConfVars.getBoolVar(conf, SharkConfVars.CHECK_TABLENAME_FLAG)
        // Note: the CreateTableDesc's table properties are Java Maps, but the TableDesc's table
        //       properties, which are used during execution, are Java Properties.
        val createTableProperties: JavaMap[String, String] = createTableDesc.getTblProps()

        // There are two cases that will enable caching:
        // 1) Table name includes "_cached" or "_tachyon".
        // 2) The "shark.cache" table property is "true", or the string representation of a supported
        //   cache mode (heap, Tachyon).
        cacheMode = CacheType.fromString(createTableProperties.get("shark.cache"))
        // Continue planning based on the 'cacheMode' read.
        if (cacheMode == CacheType.HEAP ||
            (createTableDesc.getTableName.endsWith("_cached") && checkTableName)) {
          cacheMode = CacheType.HEAP
          createTableProperties.put("shark.cache", cacheMode.toString)
        } else if (cacheMode == CacheType.TACHYON ||
          (createTableDesc.getTableName.endsWith("_tachyon") && checkTableName)) {
          cacheMode = CacheType.TACHYON
          createTableProperties.put("shark.cache", cacheMode.toString)
        }

        if (CacheType.shouldCache(cacheMode)) {
          createTableDesc.setSerName(classOf[ColumnarSerDe].getName)
        }

        qb.setTableDesc(createTableDesc)
        shouldReset = true
      }
    } else {
      SessionState.get().setCommandType(HiveOperation.QUERY)
    }

    // Delegate create view to Hive.
    if (ast.getToken().getType() == HiveParser.TOK_CREATEVIEW) {
      return super.analyzeInternal(ast)
    }

    // Continue analyzing from the child ASTNode.
    if (!doPhase1(child, qb, initPhase1Ctx())) {
      return
    }

    // Used to protect against recursive views in getMetaData().
    SharkSemanticAnalyzer.viewsExpandedField.set(this, new JavaArrayList[String]())

    // TODO: Figure out why ast is not set for ANALYZE TABLE .. COMPUTE STATISTICS
    // causing null ptr exception
    val astField = classOf[SemanticAnalyzer].getDeclaredField("ast")
    astField.setAccessible(true)
    astField.set(this, ast)

    logInfo("Completed phase 1 of Shark Semantic Analysis")
    getMetaData(qb)
    logInfo("Completed getting MetaData in Shark Semantic Analysis")

    // Reset makes sure we don't run the mapred jobs generated by Hive.
    if (shouldReset) reset()

    val optimizerStats = new SharkOptimizerStatistics()
    optimizerStats.initializeStats(qb, pctx, conf, db.getCurrentDatabase())

    // Save the result schema derived from the sink operator produced
    // by genPlan. This has the correct column names, which clients
    // such as JDBC would prefer instead of the c0, c1 we'll end
    // up with later.
    val hiveSinkOp = sharkGenPlan(qb, optimizerStats, conf)

    // Use reflection to invoke convertRowSchemaToViewSchema.
    _resSchema = SharkSemanticAnalyzer.convertRowSchemaToViewSchemaMethod.invoke(
      this, pctx.getOpParseCtx.get(hiveSinkOp).getRowResolver()
      ).asInstanceOf[JavaList[FieldSchema]]

    // Run Hive optimization.
    val optm = new SharkOptimizer()
    optm.setPctx(pctx)
    optm.initialize(conf)
    pctx = optm.optimize()

    // Replace Hive physical plan with Shark plan. This needs to happen after
    // Hive optimization.
    val hiveSinkOps = SharkSemanticAnalyzer.findAllHiveFileSinkOperators(
      pctx.getTopOps().values().head)

    // TODO: clean the following code. It's too messy to understand...
    val terminalOpSeq = {
      if (qb.getParseInfo.isInsertToTable && !qb.isCTAS) {
        hiveSinkOps.map { hiveSinkOp =>
          val tableName = hiveSinkOp.asInstanceOf[HiveFileSinkOperator].getConf().getTableInfo()
            .getTableName()

          if (tableName == null || tableName == "") {
            // If table name is empty, it is an INSERT (OVERWRITE) DIRECTORY.
            OperatorFactory.createSharkFileOutputPlan(hiveSinkOp)
          } else {
            // Otherwise, check if we are inserting into a table that was cached.
            val cachedTableName = tableName.split('.')(1)
            val cachedDbName = tableName.split('.')(0)
            SharkEnv.memoryMetadataManager.get(cachedTableName) match {
              case Some(rdd) => {
                if (hiveSinkOps.size == 1) {
                  // If useUnionRDD is false, the sink op is for INSERT OVERWRITE.
                  val useUnionRDD = qb.getParseInfo.isInsertIntoTable(cachedDbName, cachedTableName)
                  val storageLevel = RDDUtils.getStorageLevelOfCachedTable(rdd)
                  OperatorFactory.createSharkMemoryStoreOutputPlan(
                    hiveSinkOp,
                    cachedTableName,
                    storageLevel,
                    _resSchema.size,                // numColumns
                    cacheMode == CacheType.TACHYON, // use tachyon
                    useUnionRDD)
                } else {
                  throw new SemanticException(
                    "Shark does not support updating cached table(s) with multiple INSERTs")
                }
              }
              case None => OperatorFactory.createSharkFileOutputPlan(hiveSinkOp)
            }
          }
        }
      } else if (hiveSinkOps.size == 1) {
        // For a single output, we have the option of choosing the output
        // destination (e.g. CTAS with table property "shark.cache" = "true").
        Seq {
          if (qb.isCTAS && qb.getTableDesc != null && CacheType.shouldCache(cacheMode)) {
            val storageLevel = MemoryMetadataManager.getStorageLevelFromString(
              qb.getTableDesc().getTblProps.get("shark.cache.storageLevel"))
            qb.getTableDesc().getTblProps().put(CachedTableRecovery.QUERY_STRING, ctx.getCmd())
            OperatorFactory.createSharkMemoryStoreOutputPlan(
              hiveSinkOps.head,
              qb.getTableDesc.getTableName,
              storageLevel,
              _resSchema.size,                // numColumns
              cacheMode == CacheType.TACHYON, // use tachyon
              false)
          } else if (pctx.getContext().asInstanceOf[QueryContext].useTableRddSink && !qb.isCTAS) {
            OperatorFactory.createSharkRddOutputPlan(hiveSinkOps.head)
          } else {
            OperatorFactory.createSharkFileOutputPlan(hiveSinkOps.head)
          }
        }

        // A hack for the query plan dashboard to get the query plan. This was
        // done for SIGMOD demo. Turn it off by default.
        //shark.dashboard.QueryPlanDashboardHandler.terminalOperator = terminalOp

      } else {
        // For non-INSERT commands, if there are multiple file outputs, we always use file outputs.
        hiveSinkOps.map(OperatorFactory.createSharkFileOutputPlan(_))
      }
    }


    SharkSemanticAnalyzer.breakHivePlanByStages(terminalOpSeq)
    genMapRedTasks(qb, pctx, terminalOpSeq)


    logInfo("Completed plan generation")
  }

  /**
   * Generate tasks for executing the query, including the SparkTask to do the
   * select, the MoveTask for updates, and the DDLTask for CTAS.
   */
  def genMapRedTasks(qb: QB, pctx: ParseContext, terminalOps: Seq[TerminalOperator]) {

    // Create the spark task.
    terminalOps.foreach { terminalOp =>
      val task = TaskFactory.get(new SparkWork(pctx, terminalOp, _resSchema), conf)
      rootTasks.add(task)
    }

    val isCStats = qb.isAnalyzeRewrite()

    if (qb.getIsQuery && !isCStats) {
      // Configure FetchTask (used for fetching results to CLIDriver).
      val loadWork = getParseContext.getLoadFileWork.get(0)
      val cols = loadWork.getColumns
      val colTypes = loadWork.getColumnTypes

      val resFileFormat = HiveConf.getVar(conf, HiveConf.ConfVars.HIVEQUERYRESULTFILEFORMAT)
      val resultTab = PlanUtils.getDefaultQueryOutputTableDesc(cols, colTypes, resFileFormat)

      val fetchWork = new FetchWork(
        new Path(loadWork.getSourceDir).toString, resultTab, qb.getParseInfo.getOuterQueryLimit)

      val fetchTask = TaskFactory.get(fetchWork, conf).asInstanceOf[FetchTask]
      setFetchTask(fetchTask)

    } else if (!isCStats) {
      // Configure MoveTasks for table updates (e.g. CTAS, INSERT).
      val mvTasks = new JavaArrayList[MoveTask]()

      val fileWork = getParseContext.getLoadFileWork
      val tableWork = getParseContext.getLoadTableWork
      tableWork.foreach { ltd =>
        mvTasks.add(TaskFactory.get(
          new MoveWork(null, null, ltd, null, false), conf).asInstanceOf[MoveTask])
      }

      fileWork.foreach { lfd =>
        if (qb.isCTAS) {
          var location = qb.getTableDesc.getLocation
          if (location == null) {
            try {
              val dumpTable = db.newTable(qb.getTableDesc.getTableName)
              val wh = new Warehouse(conf)
              location = wh.getTablePath(db.getDatabase(dumpTable.getDbName()), dumpTable
                  .getTableName()).toString;
            } catch {
              case e: HiveException => throw new SemanticException(e)
              case e: MetaException => throw new SemanticException(e)
            }
          }
          lfd.setTargetDir(location)
        }

        mvTasks.add(TaskFactory.get(
          new MoveWork(null, null, null, lfd, false), conf).asInstanceOf[MoveTask])
      }

      // The move task depends on all root tasks. In the case of multi outputs,
      // the moves are only started once all outputs are executed.
      val hiveFileSinkOp = terminalOps.head.hiveOp
      mvTasks.foreach { moveTask =>
        rootTasks.foreach { rootTask =>
          rootTask.addDependentTask(moveTask)
        }

        // Add StatsTask's. See GenMRFileSink1.addStatsTask().
        /*
        if (conf.getBoolVar(HiveConf.ConfVars.HIVESTATSAUTOGATHER)) {
          println("Adding a StatsTask for MoveTask " + moveTask)
          //addStatsTask(fsOp, mvTask, currTask, parseCtx.getConf())
          val statsWork = new StatsWork(moveTask.getWork().getLoadTableWork())
          statsWork.setAggKey(hiveFileSinkOp.getConf().getStatsAggPrefix())
          val statsTask = TaskFactory.get(statsWork, conf)
          hiveFileSinkOp.getConf().setGatherStats(true)
          moveTask.addDependentTask(statsTask)
          statsTask.subscribeFeed(moveTask)
        }
        */
      }
    }

    // If the query was the result of analyze table column compute statistics rewrite, create
    // a column stats task and persist stats to the metastore.
    if (isCStats) {
      genColumnStatsTask(qb)
    }

    // For CTAS, generate a DDL task to create the table. This task should be a
    // dependent of the main SparkTask.
    if (qb.isCTAS) {
      val crtTblDesc: CreateTableDesc = qb.getTableDesc
      crtTblDesc.validate()

      // Clear the output for CTAS since we don't need the output from the
      // mapredWork, the DDLWork at the tail of the chain will have the output.
      getOutputs.clear()

      // CTAS assumes only single output.
      val crtTblTask = TaskFactory.get(
        new DDLWork(getInputs, getOutputs, crtTblDesc),conf).asInstanceOf[DDLTask]
      rootTasks.head.addDependentTask(crtTblTask)
    }
  }

  /* This is from ColumnStatsSemanticAnalyzer */
  def genColumnStatsTask(qb: QB): Unit = {
    val qbParseInfo = qb.getParseInfo()
    var cStatsTask: ColumnStatsTask = null
    var cStatsWork: ColumnStatsWork = null
    var fetch: FetchWork = null
    val tableName = qbParseInfo.getTableName()
    val partName = qbParseInfo.getPartName()
    val colName = qbParseInfo.getColName()
    val colType = qbParseInfo.getColType()
    val isTblLevel = qbParseInfo.isTblLvl()

    val loadFileWorkField = classOf[SemanticAnalyzer].getDeclaredField(
      "loadFileWork")
    loadFileWorkField.setAccessible(true)
    val loadFileDesc = loadFileWorkField.get(this).asInstanceOf[JavaList[LoadFileDesc]](0)
    val cols = loadFileDesc.getColumns()
    val colTypes = loadFileDesc.getColumnTypes()
    

    val resFileFormat = HiveConf.getVar(conf, 
      HiveConf.ConfVars.HIVEQUERYRESULTFILEFORMAT)
    val resultTab = PlanUtils.getDefaultQueryOutputTableDesc(
      cols, colTypes, resFileFormat)

    fetch = new FetchWork(new Path(loadFileDesc.getSourceDir()).toString, 
      resultTab, qb.getParseInfo().getOuterQueryLimit())

    val cStatsDesc = new ColumnStatsDesc(tableName, partName, colName, 
      colType, isTblLevel)
    cStatsWork = new ColumnStatsWork(fetch, cStatsDesc)
    cStatsTask = TaskFactory.get(cStatsWork, conf).asInstanceOf[ColumnStatsTask]
    rootTasks.add(cStatsTask)
  }
  /**
   * Override Hive SemAnalyzer's genPlan to let the optimizer manipulate the join tree before the
   * individual operators are created.
   */
  def sharkGenPlan(qb: QB, optimizerStats: SharkOptimizerStatistics, conf: HiveConf): HiveOp[_] = {

    // Make private methods accessible
    val genPlanMethod = classOf[SemanticAnalyzer].getDeclaredMethod("genPlan", classOf[QBExpr])
    genPlanMethod.setAccessible(true)

    val genTablePlanMethod = classOf[SemanticAnalyzer].getDeclaredMethod("genTablePlan", classOf[String], classOf[QB])
    genTablePlanMethod.setAccessible(true)

    val genPTFPlanMethod = classOf[SemanticAnalyzer].getDeclaredMethod("genPTFPlan", classOf[PTFInvocationSpec],
      classOf[HiveOp[_]])
    genPTFPlanMethod.setAccessible(true)

    val genLateralViewPlansMethod = classOf[SemanticAnalyzer].getDeclaredMethod("genLateralViewPlans",
      classOf[JavaMap[String, HiveOp[_]]], classOf[QB])
    genLateralViewPlansMethod.setAccessible(true)

    val genUniqueJoinTreeMethod = classOf[SemanticAnalyzer].getDeclaredMethod("genUniqueJoinTree",
      classOf[QB], classOf[ASTNode], classOf[JavaMap[String, HiveOp[_]]])
    genUniqueJoinTreeMethod.setAccessible(true)

    val genJoinTreeMethod = classOf[SemanticAnalyzer].getDeclaredMethod("genJoinTree",
      classOf[QB], classOf[ASTNode], classOf[JavaMap[String, HiveOp[_]]])
    genJoinTreeMethod.setAccessible(true)

    val mergeJoinTreeMethod = classOf[SemanticAnalyzer].getDeclaredMethod("mergeJoinTree", classOf[QB])
    mergeJoinTreeMethod.setAccessible(true)

    val pushJoinFiltersMethod = classOf[SemanticAnalyzer].getDeclaredMethod("pushJoinFilters",
      classOf[QB], classOf[QBJoinTree], classOf[JavaMap[String, HiveOp[_]]])
    pushJoinFiltersMethod.setAccessible(true)

    val genJoinPlanMethod = classOf[SemanticAnalyzer].getDeclaredMethod("genJoinPlan",
      classOf[QB], classOf[JavaMap[String, HiveOp[_]]])
    genJoinPlanMethod.setAccessible(true)

    val genBodyPlanMethod = classOf[SemanticAnalyzer].getDeclaredMethod("genBodyPlan", classOf[QB], classOf[HiveOp[_]])
    genBodyPlanMethod.setAccessible(true)

    val qbField = classOf[SemanticAnalyzer].getDeclaredField("qb")
    qbField.setAccessible(true)

    val queryPropertiesField = classOf[BaseSemanticAnalyzer].getDeclaredField("queryProperties")
    queryPropertiesField.setAccessible(true)

    val opParseCtxField = classOf[SemanticAnalyzer].getDeclaredField("opParseCtx")
    opParseCtxField.setAccessible(true)

    // First generate all the opInfos for the elements in the from clause
    val aliasToOpInfo = new JavaHashMap[String, HiveOp[_ <: OperatorDesc]]()

    // Recurse over the subqueries to fill the subquery part of the plan
    qb.getSubqAliases().foreach( alias => {
      val qbexpr = qb.getSubqForAlias(alias)
      aliasToOpInfo.put(alias, genPlanMethod.invoke(this, qbexpr).asInstanceOf[HiveOp[_ <: OperatorDesc]])
      qbexpr.asInstanceOf[QBExpr].setAlias(alias)
    })

    // Recurse over all the source tables
    qb.getTabAliases().foreach( alias => {
      val op = genTablePlanMethod.invoke(this, alias, qb).asInstanceOf[HiveOp[_ <: OperatorDesc]]
      aliasToOpInfo.put(alias, op)
    })

    var srcOpInfo: HiveOp[_ <: OperatorDesc] = null
    var lastPTFOp: HiveOp[_ <: OperatorDesc] = null

    if (queryPropertiesField.get(this).asInstanceOf[QueryProperties].hasPTF()) {

      // After processing subqueries and source tables, process partitioned table functions
      val ptfNodeToSpec = qb.getPTFNodeToSpec()
      if (ptfNodeToSpec != null) {
        ptfNodeToSpec.entrySet().foreach( entry => {
          val ast = entry.getKey()
          val spec = entry.getValue()
          val inputAlias = spec.getQueryInputName()
          val inOp = aliasToOpInfo.get(inputAlias)

          if (inOp == null) {
            throw new SemanticException(SemanticAnalyzer.generateErrorMessage(ast,
              "Cannot resolve input Operator for PTF invocation"))
          }
          lastPTFOp = genPTFPlanMethod.invoke(this, spec, inOp).asInstanceOf[HiveOp[_ <: OperatorDesc]]
          val ptfAlias = spec.getFunction().asInstanceOf[PartitionedTableFunctionSpec].getAlias()
          if (ptfAlias != null) {
            aliasToOpInfo.put(ptfAlias, lastPTFOp)
          }
        })
      }
    }

    // For all the source tables that have a lateral view, attach the
    // appropriate operators to the TS
    genLateralViewPlansMethod.invoke(this, aliasToOpInfo, qb)

    // process join
    if (qb.getParseInfo().getJoinExpr() != null) {
      val joinExpr = qb.getParseInfo().getJoinExpr()

      if (joinExpr.getToken().getType() == HiveParser.TOK_UNIQUEJOIN) {
        val joinTree = genUniqueJoinTreeMethod.invoke(this, qb, joinExpr, aliasToOpInfo).asInstanceOf[QBJoinTree]
        qb.setQbJoinTree(joinTree)
      } else {
        val joinTree = genJoinTreeMethod.invoke(this, qb, joinExpr, aliasToOpInfo).asInstanceOf[QBJoinTree]
        qb.setQbJoinTree(joinTree)

        // Note: we invoke this *after* optimizing tree instead
        //mergeJoinTreeMethod.invoke(this, qb)
      }

      // If any filters are present in the join tree, push them on top of the table
      pushJoinFiltersMethod.invoke(this, qb, qb.getQbJoinTree(), aliasToOpInfo)


      val opParseCtxs = opParseCtxField.get(this)
              .asInstanceOf[java.util.LinkedHashMap[HiveOp[_ <: OperatorDesc], OpParseContext]]


      // Manipulate the join tree using Shark's cost-based optimizer
      val joinOptimizer = new JoinOptimizer()
      joinOptimizer.initialize(this, qb, aliasToOpInfo, optimizerStats, opParseCtxs, conf)
      joinOptimizer.optimizeJoinTree()

      // Merge join tree levels, where possible.
      mergeJoinTreeMethod.invoke(this, qb)

      srcOpInfo = genJoinPlanMethod.invoke(this, qb, aliasToOpInfo).asInstanceOf[HiveOp[_ <: OperatorDesc]]
    } else {
      // If there is more than 1 source, we have a join case.
      // Later, this can be extended to the 'union all' case as well.
      srcOpInfo = aliasToOpInfo.values().iterator().next();

      // With PTFs, there may be more (note for PTFChains:
      // 1 PTF invocation may entail multiple PTF operators)
      if (lastPTFOp != null) {
        srcOpInfo = lastPTFOp
      }
    }

    val bodyOpInfo = genBodyPlanMethod.invoke(this, qb, srcOpInfo).asInstanceOf[HiveOp[_ <: OperatorDesc]]

    logInfo("Created Plan for Query Block " + qb.getId())

    qbField.set(this, qb)
    return bodyOpInfo
  }
}


object SharkSemanticAnalyzer extends LogHelper {

  /**
   * The reflection object used to invoke convertRowSchemaToViewSchema.
   */
  private val convertRowSchemaToViewSchemaMethod = classOf[SemanticAnalyzer].getDeclaredMethod(
    "convertRowSchemaToViewSchema", classOf[RowResolver])
  convertRowSchemaToViewSchemaMethod.setAccessible(true)

  /**
   * The reflection object used to get a reference to SemanticAnalyzer.viewsExpanded,
   * so we can initialize it.
   */
  private val viewsExpandedField = classOf[SemanticAnalyzer].getDeclaredField("viewsExpanded")
  viewsExpandedField.setAccessible(true)

  /**
   * Given a Hive top operator (e.g. TableScanOperator), find all the file sink
   * operators (aka file output operator).
   */
  private def findAllHiveFileSinkOperators(op: HiveOperator): Seq[HiveOperator] = {
    if (op.getChildOperators() == null || op.getChildOperators().size() == 0) {
      Seq[HiveOperator](op)
    } else {
      op.getChildOperators().flatMap(findAllHiveFileSinkOperators(_)).distinct
    }
  }

  /**
   * Break the Hive operator tree into multiple stages, separated by Hive
   * ReduceSink. This is necessary because the Hive operators after ReduceSink
   * cannot be initialized using ReduceSink's output object inspector. We
   * craft the struct object inspector (that has both KEY and VALUE) in Shark
   * ReduceSinkOperator.initializeDownStreamHiveOperators().
   */
  private def breakHivePlanByStages(terminalOps: Seq[TerminalOperator]) = {
    val reduceSinks = new scala.collection.mutable.HashSet[ReduceSinkOperator]
    val queue = new scala.collection.mutable.Queue[Operator[_]]
    queue ++= terminalOps

    while (!queue.isEmpty) {
      val current = queue.dequeue()
      current match {
        case op: ReduceSinkOperator => reduceSinks += op
        case _ => Unit
      }
      // This is not optimal because operators can be added twice. But the
      // operator tree should not be too big...
      queue ++= current.parentOperators
    }

    logDebug("Found %d ReduceSinkOperator's.".format(reduceSinks.size))

    reduceSinks.foreach { op =>
      val hiveOp = op.asInstanceOf[Operator[HiveOperator]].hiveOp
      if (hiveOp.getChildOperators() != null) {
        hiveOp.getChildOperators().foreach { child =>
          logDebug("Removing child %s from %s".format(child, hiveOp))
          hiveOp.removeChild(child)
        }
      }
    }
  }
}
