/*
 * Copyright (C) 2013 The Regents of The University California.
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

package shark.optimizer

import java.util.{ArrayList => JavaArrayList, HashMap => JavaHashMap,
  HashSet => JavaHashSet, LinkedHashMap => JavaLinkedHashMap }

import scala.Tuple2
import scala.collection.JavaConversions._
import scala.collection.mutable.{ArrayBuffer, HashMap}

import org.apache.hadoop.hive.conf.HiveConf
import org.apache.hadoop.hive.ql.exec.{Operator => HiveOp, FilterOperator}
import org.apache.hadoop.hive.ql.parse._
import org.apache.hadoop.hive.ql.plan._
import org.apache.hadoop.hive.ql.udf.generic._

import shark.{SharkConfVars, LogHelper}
import shark.parse.SharkSemanticAnalyzer

class JoinOptimizer extends LogHelper {
  var qb: QB = _
  var aliasToOpInfo: JavaHashMap[String, HiveOp[_ <: OperatorDesc]] = _
  var optimizerStats: SharkOptimizerStatistics = _
  var opParseCtxs: JavaLinkedHashMap[HiveOp[_ <: OperatorDesc], OpParseContext] = _
  var sharkSemanticAnalyzer: SharkSemanticAnalyzer = _
  var conf: HiveConf = _

  val allAliases = new scala.collection.mutable.HashSet[String]()
  val originalOrder = new ArrayBuffer[String]()

  val bestJoinPlans = new HashMap[Set[String], Array[String]]()
  val bestJoinCardinality = new HashMap[Set[String], Long]()

  val aliasToAliasesWithJoinPredicate = new HashMap[String, JavaHashSet[String]]()
  val aliasPairToExpressions = new HashMap[Tuple2[String, String], JavaArrayList[ASTNode]]()

  def initialize(sharkSA: SharkSemanticAnalyzer,
                  qb: QB,
                  aliasToOpInfo: JavaHashMap[String, HiveOp[_ <: OperatorDesc]],
                  optimizerStats: SharkOptimizerStatistics,
                  opParseCtxs: JavaLinkedHashMap[HiveOp[_ <: OperatorDesc], OpParseContext],
                  conf: HiveConf) {
    this.qb = qb
    this.aliasToOpInfo = aliasToOpInfo
    this.optimizerStats = optimizerStats
    this.opParseCtxs = opParseCtxs
    this.sharkSemanticAnalyzer = sharkSA
    this.conf = conf
  }

  /**
   * Take the current join tree and apply cost-based optimization to get a new
   * join ordering. Create a new join tree based on the new ordering and save to
   * the current query block.
   */
  def optimizeJoinTree(): Unit =  {
    val optimizeJoins = SharkConfVars.getBoolVar(conf, SharkConfVars.OPTIMIZE_JOINS)

    logInfo("Beginning join optimization")
    initializeAliasInfo(qb.getQbJoinTree())
    logInfo("Hive's join order is: " + originalOrder.mkString(", "))

    if (optimizeJoins && isOptimizable(qb.getQbJoinTree())) {
      // Get new join ordering
      val newJoinPlan = getBestJoinPlan(allAliases.toSet)
      logInfo("Replacing with better join order: " + newJoinPlan.mkString(", "))

      // Convert join ordering into a new join tree
      val optimizedJoinTree = getNewJoinTree(newJoinPlan)

      // Save optimized join tree
      qb.setQbJoinTree(optimizedJoinTree)
    } else {
      logInfo("Not optimizing join operator execution plan.")
    }
    logInfo("Printing final join tree: ")
    printJoinTree(qb.getQbJoinTree)
    logInfo("Join optimization complete")
  }

  /** Filter predicate comparison type */
  object PredComparisonType extends Enumeration {
    type PredComparisonType = Value
    val EQ, LT, GT, LTE, GTE = Value
  }

  /** Filter op predicate information for the source of a join relation */
  class JoinFilterPredInfo(
    val predCompType: PredComparisonType.PredComparisonType,
    val colName: String,
    val expr: ExprNodeDesc) {}

  /**
   * Get predicate pushdown columns for a given table alias
   */
  def getFilters (tabAlias: String): Seq[JoinFilterPredInfo] = {
    val filters = new ArrayBuffer[JoinFilterPredInfo]()
    var op = aliasToOpInfo(tabAlias)
    while (op.isInstanceOf[FilterOperator]) {
      val pred = op.getConf.asInstanceOf[FilterDesc].getPredicate
      val comparisonType = pred.asInstanceOf[ExprNodeGenericFuncDesc].getGenericUDF match {
        case _:GenericUDFOPEqual => PredComparisonType.EQ
        case _:GenericUDFOPEqualOrGreaterThan => PredComparisonType.GTE
        case _:GenericUDFOPEqualOrLessThan => PredComparisonType.LTE
        case _:GenericUDFOPGreaterThan => PredComparisonType.GT
        case _:GenericUDFOPLessThan => PredComparisonType.LT
      }
      val filter = new JoinFilterPredInfo(comparisonType, pred.getCols()(0),
        pred.asInstanceOf[ExprNodeGenericFuncDesc].getChildExprs()(1))
      filters += filter
      // In case we have multiple chained filter operators, traverse up the tree
      op = op.getParentOperators()(0)
    }
    filters
  }

  /**
   * Compute the selectivity of a particular predicate, as per System R.
   * Only consider constants for now.
   *  col = value: 1/card(col)
   *  col > value, col >= value: 1/((max(col) - value) / (max(col) - min(col)))
   *  col < value, col <= value: 1/((value - min(col)) / (max(col) - min(col)))
   *
   *  TODO: support BETWEEN, IN, OR
   */
  def computeFilterSelectivity (joinFilter: JoinFilterPredInfo, tabAlias: String): Double = {
    if (joinFilter.predCompType == PredComparisonType.EQ) {
      val filterColCard: Long = optimizerStats.getColumnCardinality(
        qb.getTabNameForAlias(tabAlias), joinFilter.colName).getOrElse(1)
      logInfo("Found EQ filter for "+tabAlias+"."+joinFilter.colName+", SF *= 1/"+filterColCard)
      1.0 / filterColCard
    } else if (joinFilter.predCompType == PredComparisonType.GT ||
      joinFilter.predCompType == PredComparisonType.GTE ||
      joinFilter.predCompType == PredComparisonType.LT ||
      joinFilter.predCompType == PredComparisonType.LTE) {
      // TODO: Use expressions in top comment (as in System R)
      // For now, naively assume that >,>=,<=,< will reduce output by half
      0.5
    }  else {
      1
    }
  }

  /**
   * Compute the join cost.
   * For our purposes,
   *  cost = cardinality of the output of the join the two relations given
   *          +
   *         sum of costs of each previous join
   *
   * TODO:
   *  - Cases with more than one join predicate between the relations
   */
  def computeJoinCost (leftPlan: Array[String], rightAlias: String): Long = {

    val leftAlias = getJoinableLeftAlias(leftPlan, rightAlias)
    val useAccumulatedCost = SharkConfVars.getBoolVar(conf, SharkConfVars.OPTIMIZE_JOIN_IO)
    if (useAccumulatedCost) {
      logInfo("Using accumulated cost function")
    } else {
      logInfo("Using traditional cost function")
    }

    // Get the join column names for right and left relations
    val rightRelJoinCol = aliasPairToExpressions(rightAlias, leftAlias)
      .map(exprToExprNodeDesc(_, rightAlias).getColumn).head
    val leftRelJoinCol = aliasPairToExpressions(leftAlias, rightAlias)
      .map(exprToExprNodeDesc(_, leftAlias).getColumn).head

    // Get the cardinality for the join column on each side
    // TODO: Pick default cardinality if we don't have it computed. Leaving 1 for now.
    val rightColCard: Long = optimizerStats.getColumnCardinality(
      qb.getTabNameForAlias(rightAlias), rightRelJoinCol).getOrElse(1)
    val leftColCard: Long  = optimizerStats.getColumnCardinality(
      qb.getTabNameForAlias(leftAlias), leftRelJoinCol).getOrElse(1)

    // Selectivity factor is 1 / max(leftColCard, rightColCard)
    var selectivityFactor = 1.0 / (
      if (rightColCard > leftColCard) rightColCard else leftColCard).toDouble

    // Get the predicates that have been pushed down and include coefficients in the SF.
    val leftFilters = getFilters(leftAlias)
    val rightFilters = getFilters(rightAlias)
    selectivityFactor *=
      leftFilters.foldLeft(1.0)(_ * computeFilterSelectivity(_, leftAlias)) *
      rightFilters.foldLeft(1.0)(_ * computeFilterSelectivity(_, leftAlias))

    logInfo("Calculating cost of joining ["+leftPlan.mkString(", ")+"] with ["+rightAlias+"]")
    logInfo("Join column cardinalities. Left: "+leftColCard+", Right: "+rightColCard)
    logInfo("Selectivity factor: "+selectivityFactor)

    // Left relation cardinality = Cached cost of left plan = num rows of left relation
    val leftCard: Long =
    if (leftPlan.length == 1) {
      // Todo: What should the defult be if we don't have number of rows? 999999999 for now
      optimizerStats.getNumRows(qb.getTabNameForAlias(leftAlias)).getOrElse(999999999)
    } else {
      bestJoinCardinality(leftPlan.toSet)
    }

    // Right relation cardinality = num rows of right table
    // todo: consider selectivity of local predicates / pushdowns
    val rightCard: Long = optimizerStats.getNumRows(
      qb.getTabNameForAlias(rightAlias)).getOrElse(999999999)

    logInfo("Relation cardinalities (numRows). Left: " + leftCard + ", Right: " + rightCard)

    val joinCost = selectivityFactor * leftCard * rightCard
    logInfo("Computed join cost: " + joinCost)

    // Sum with cost of previous joins if we have at least 3 relations
    // (2 on the left side, one on the right)
    if (leftPlan.length > 1 && useAccumulatedCost) {
      leftCard + joinCost.toLong
    } else {
      joinCost.toLong
    }
  }

  /**
   * Determine whether a relation can be joined to a set of relations. This is true only
   * when they have a join predicate in common. (For simplicity, we're not allowing
   * cartesian / cross joins for now.)
   *
   * TODO: change left alias set to array and consider non-rightmost elements only if
   * they share key?
   */
  def canJoinRelations (leftAliases: Set[String], rightAlias: String): Boolean = {
    var i = 0
    var commonPredicateFound = false

    val numMatches = leftAliases.filter(alias => {
      aliasToAliasesWithJoinPredicate(alias).contains(rightAlias) ||
      aliasToAliasesWithJoinPredicate(rightAlias).contains(alias)
    })
    if (numMatches.size > 0) {
      commonPredicateFound = true
    }

    commonPredicateFound
  }

  /**
   * Get the cheapest join plan for a given set of relations.
   *
   * For a set of size n, we do this as follows:
   *  - Save each relation and its cost
   *  - For each 1 < level <= n, enumerate all (n-1)-sized combinations and compute the
   *    cost of joining them to the each n'th relation. For each set of size n, save the
   *    cheapest plan and its cost.
   *
   * This is the dynamic programming algorithm described by System R, but we ignore
   * physical access methods (e.g. index vs. file scan, etc.) and "interesting" orders.
   *
   * Todo:
   *  - Try greedy algorithm, esp for high numbers of join relations
   *  - Consider whether tables are already cached in memory or not
   */
  def getBestJoinPlan(input: Set[String]): Array[String] = {

    val levels = input.size
    var curLevel = 1

    val pickWorstOrder = SharkConfVars.getBoolVar(conf, SharkConfVars.OPTIMIZER_PICK_WORST_ORDER)
    if (pickWorstOrder) logInfo("WORST join order") else logInfo("BEST join order")

    while (curLevel <= levels) {
      // At the first level, we save each relation
      if (curLevel == 1) {
        input.foreach(relation => {
          logInfo("Retaining plan: " + relation + " with cost 0")
          bestJoinPlans.put(Set(relation), Array(relation))
          bestJoinCardinality.put(Set(relation), 0)
        })
      } else {
        // Iterate through full set, computing join cost of joining each relation
        // to the best plan of each possible subset of size level - 1.
        input.view.zipWithIndex.foreach { case(relation, index) =>  {

          // Get all previous level (n-1) sets, omitting relation at current index
          val subset = input.toBuffer
          subset.remove(index)
          val prevLevel = curLevel - 1
          val subsets = subset.combinations(prevLevel).map(_.toSet)

          subsets.foreach { leftRelations => {
            // Check if current relation can be joined (as outer rel) with best plan
            // for previous level subset
            if (bestJoinPlans.containsKey(leftRelations) &&
              canJoinRelations(leftRelations, relation)) {
              val leftBestPlan = bestJoinPlans(leftRelations)
              val joinCost = computeJoinCost(leftBestPlan, relation)

              // Retain this plan and cost, but only if cheapest so far (for current set)
              val curSet = leftRelations + relation
              // xxx temporarily allowing worst join orders to be picked
              //if ( ! bestJoinCardinality.containsKey(curSet) ||  joinCost < bestJoinCardinality(curSet)) {
              if ( ! bestJoinCardinality.containsKey(curSet) ||
                (pickWorstOrder && joinCost > bestJoinCardinality(curSet)) ||
                (!pickWorstOrder && joinCost < bestJoinCardinality(curSet))) {

                // Plan = best n-1 subset's plan joined to current relation
                val plan = bestJoinPlans(leftRelations) ++ Array(relation)
                logInfo("Retaining plan: " + plan.mkString(" ") + "; Cost: " + joinCost)
                bestJoinPlans(curSet) = plan
                bestJoinCardinality.put(curSet, joinCost)
              }
            }
          }}
        }}
      }
      curLevel += 1
    }

    bestJoinPlans(input)
  }

  /**
   * Get the alias from the list of left aliases that shares a join condition with right alias.
   * This just gets the right-most one. Todo: consider transitivity
   */
  def getJoinableLeftAlias(leftPlan: Array[String], rightAlias: String): String = {
    var leftAlias:String = null
    var matchFound:Boolean = false
    // TODO: check column, equivalences
    leftPlan.reverse.foreach(alias => {
      if (aliasToAliasesWithJoinPredicate(alias).contains(rightAlias)) {
        matchFound = true
        leftAlias = alias
      }
    })
    leftAlias
  }

  /**
   * Take a join tree and get an array of join tree nodes. First element is
   * right-most join tree node.
   */
  def joinTreeToArray(joinTree: QBJoinTree): Array[QBJoinTree] = {
    val joinTreeNodes = new ArrayBuffer[QBJoinTree]
    var curTree = joinTree
    while (curTree != null) {
      joinTreeNodes.add(curTree)
      curTree = curTree.getJoinSrc()
    }
    joinTreeNodes.toArray
  }

  /**
   * Gather alias to expression info and which aliases are linked by join conditions.
   */
  def initializeAliasInfo (rightmostJoinTree: QBJoinTree): Unit = {

    var curNode = rightmostJoinTree
    while (curNode != null) {
      val baseSrc = curNode.getBaseSrc()
      val leftAlias = curNode.getLeftAlias
      val rightAlias = curNode.getBaseSrc()(1)

      // Since this left-deep join tree has not yet been merged, there will be
      // at most one alias at each node, except for the left-most, which has two.
      if (baseSrc.size != 2) {
        throw new SemanticException("Join tree baseSrc should have exactly 2 relations")
      }

      // Pairs of relations that have mutual join predicates
      if (!aliasToAliasesWithJoinPredicate.containsKey(leftAlias)) {
        aliasToAliasesWithJoinPredicate.put(leftAlias, new JavaHashSet[String]())
      }
      if (!aliasToAliasesWithJoinPredicate.containsKey(rightAlias)) {
        aliasToAliasesWithJoinPredicate.put(rightAlias, new JavaHashSet[String]())
      }
      aliasToAliasesWithJoinPredicate(leftAlias).add(rightAlias)
      aliasToAliasesWithJoinPredicate(rightAlias).add(leftAlias)

      // For each pair of relations above, save the join expression
      if (!aliasPairToExpressions.containsKey(Tuple2(leftAlias, rightAlias))) {
        aliasPairToExpressions.put(Tuple2(leftAlias, rightAlias), new JavaArrayList[ASTNode]())
      }
      if (!aliasPairToExpressions.containsKey(Tuple2(rightAlias, leftAlias))) {
        aliasPairToExpressions.put(Tuple2(rightAlias, leftAlias), new JavaArrayList[ASTNode]())
      }
      aliasPairToExpressions(Tuple2(leftAlias, rightAlias)).addAll(curNode.getExpressions()(0))
      aliasPairToExpressions(Tuple2(rightAlias, leftAlias)).addAll(curNode.getExpressions()(1))

      // Get full set of aliases
      baseSrc.view.zipWithIndex foreach {
        case (baseSrcAlias, index) => {
          val alias = if (baseSrcAlias == null) curNode.getLeftAlias else baseSrcAlias
          if (alias != null) {
            allAliases.add(alias)
          }
        }
      }

      // Get Hive's original join order. baseSrc(1) is right side, (0) is left.
      if (baseSrc(1) != null) {
        originalOrder += baseSrc(1)
      }
      if (baseSrc(0) != null) {
        originalOrder += baseSrc(0)
      }

      curNode = curNode.getJoinSrc
    }
  }

  /**
   * Determine if the join optimizer currently supports all of the types of joins contained
   * in this join tree.
   */
  def isOptimizable(joinTree: QBJoinTree): Boolean = {

    var t = joinTree
    var optimizable = true

    // Traverse the join tree and identify any conditions that we do not yet support
    while (optimizable && t != null) {
      // Todo: Check if we have stats for all tables
      // ...

      // For now: don't optimize join trees that aren't exclusively inner joins.
      t.getJoinCond().foreach(jCond => {
        if (jCond.getJoinType != JoinType.INNER) {
          logInfo("Join found non-INNER join condition type. Not optimizing join plan.")
          optimizable = false
        }
      })
      t = t.getJoinSrc
    }
    optimizable
  }

  /**
   * Create a new expression node descriptor for a given expression. This makes
   * it easier to get the correct column name.
   */
  def exprToExprNodeDesc (expr: ASTNode, tabAlias: String): ExprNodeColumnDesc = {
    val op = aliasToOpInfo.get(tabAlias)
    val inputRS = opParseCtxs.get(op).getRowResolver()
    sharkSemanticAnalyzer.genExprNodeDesc(expr, inputRS).asInstanceOf[ExprNodeColumnDesc]
  }

  /**
   * Create a new join tree based on a new join ordering. Hive will convert this to operators.
   *
   * This is modeled on Hive SemanticAnalyzer's genJoinTree() and genUniqueJoinTree()
   */
  def getNewJoinTree(plan: Array[String]): QBJoinTree = {
    val oldJoinTree = qb.getQbJoinTree()
    val joinTreeNodes = joinTreeToArray(oldJoinTree)

    val newJoinTreeNodes = new ArrayBuffer[QBJoinTree]()
    var i = 1
    while (i < plan.size) {
      val t = new QBJoinTree()

      // Only support inner joins for now
      val condn = Array(new JoinCond(0, 1, JoinType.INNER))
      t.setJoinCond(condn)

      val rightAlias = plan(i)
      t.setLeftAliases(plan.slice(0, i))
      t.setRightAliases(Array(rightAlias))
      val leftAlias = getJoinableLeftAlias(t.getLeftAliases(), rightAlias)
      t.setLeftAlias(leftAlias)

      // Set baseSrc. This includes all aliases (not including output of
      // previous joins) that are joined at this node.
      val baseSrc = new Array[String](2)
      if (i == 1) {
        baseSrc(0) = plan(0)
      }
      baseSrc(1) = plan(i)
      t.setBaseSrc(baseSrc)

      // Save resulting tree
      newJoinTreeNodes.add(t)
      i += 1

      val expressions = new JavaArrayList[JavaArrayList[ASTNode]]()
      expressions.add(aliasPairToExpressions(Tuple2(leftAlias, rightAlias)))
      expressions.add(aliasPairToExpressions(Tuple2(rightAlias, leftAlias)))
      t.setExpressions(expressions)

      val filters = new JavaArrayList[JavaArrayList[ASTNode]]()
      filters.add(new JavaArrayList[ASTNode]())
      filters.add(new JavaArrayList[ASTNode]())
      t.setFilters(filters)

      val filtersForPushing = new JavaArrayList[JavaArrayList[ASTNode]]()
      filtersForPushing.add(new JavaArrayList[ASTNode]())
      filtersForPushing.add(new JavaArrayList[ASTNode]())
      t.setFiltersForPushing(filtersForPushing)

      t.setNullSafes(new JavaArrayList[java.lang.Boolean]())
      t.setFilterMap(new Array[Array[Int]](2))

      val tAliasToOpInfo = new JavaHashMap[String, HiveOp[_ <: OperatorDesc]]()
      t.getBaseSrc().foreach{ alias =>
        if (alias != null) {
          tAliasToOpInfo.put(alias, aliasToOpInfo.get(alias))
        }
      }
      t.setAliasToOpInfo(tAliasToOpInfo)

      joinTreeNodes.foreach{ node =>
        node.getBaseSrc().view.zipWithIndex.foreach { case(alias, index) => {
          t.getBaseSrc().view.zipWithIndex.foreach { case(alias2, index2) => {
            if (alias != null && alias == alias2) {
              val filters = t.getFilters()
              filters.set(index2, node.getFilters()(index))
              t.setFilters(filters)

              val filtersFP = t.getFiltersForPushing()
              filtersFP.set(index2, node.getFiltersForPushing()(index))
              t.setFiltersForPushing(filtersFP)
              t.setNullSafes(node.getNullSafes())
            }
          }}

        }}
      }
    }

    // Link the tree nodes together
    i = 0
    while (i < newJoinTreeNodes.size) {
      if (i == 0) {
        newJoinTreeNodes(i).setJoinSrc(null)
      } else {
        newJoinTreeNodes(i).setJoinSrc(newJoinTreeNodes(i-1))
      }
      i += 1
    }

    val newTree = newJoinTreeNodes.last
    newTree
  }

  def printJoinTree (joinTree: QBJoinTree): Unit = {

    logInfo("------------------------------")
    logInfo("Join Tree ID: "+joinTree.getId)
    logInfo("Base Src: " + joinTree.getBaseSrc().view.zipWithIndex
      .map { case (alias, index) => index+":"+alias } .mkString(", "))
    logInfo("Left alias: " + joinTree.getLeftAlias)
    logInfo("Left aliases: " + joinTree.getLeftAliases().view.zipWithIndex
      .map { case (alias, index) => index+":"+alias } .mkString(", "))
    logInfo("Right aliases: " + joinTree.getRightAliases().view.zipWithIndex
      .map { case (alias, index) => index+":"+alias } .mkString(", "))
    logInfo("Left expressions: "+ joinTree.getExpressions()(0).view.zipWithIndex
      .map { case (exp, index) => {
        val expNodeDesc = exprToExprNodeDesc(exp, joinTree.getLeftAlias)
        "("+index+": "+expNodeDesc.getExprString()+")"
      }}.mkString(", "))

    logInfo("------------------------------")

    if (joinTree.getJoinSrc() != null) {
      printJoinTree(joinTree.getJoinSrc())
    }
  }
}
