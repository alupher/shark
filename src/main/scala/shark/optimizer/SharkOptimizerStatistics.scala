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

import scala.collection.JavaConversions._
import scala.collection.mutable.HashMap
import java.util.{HashMap => JHashMap, List => JList, ArrayList => JArrayList}

import org.apache.hadoop.hive.metastore.api._
import org.apache.hadoop.hive.conf.HiveConf
import org.apache.hadoop.hive.ql.parse._
import org.apache.hadoop.hive.metastore.HiveMetaStoreClient
import shark.memstore2.CacheType
import shark.{SharkEnv, LogHelper}

class SharkOptimizerStatistics() extends LogHelper {

  var tabToHiveColStats: HashMap[String, HashMap[String, ColumnStatistics]] = _
  var tabToSharkCardStats: HashMap[String, collection.Map[Int, Long]] = _
  var schemas: HashMap[String, JList[FieldSchema]] = _

  val colToCard = new HashMap[String, Option[Long]]()
  val tabToNumRows = new HashMap[String, Long]()
  val tabToSharkNumRows = new HashMap[String, Long]()
  var tabToHiveNumRows = new HashMap[String, Long]()

  /**
   * Get preliminary table info and column info for the tables in the given database
   */
  def initializeStats (qb: QB, pctx: ParseContext, conf: HiveConf, dbName: String): Unit ={

    // Get table stats from Hive metastore. This only works if an "ANALYZE ... COMPUTE STATISTICS
    // FOR COLUMNS ..." query has been run on the tables.

    val metaClient = new HiveMetaStoreClient(conf)
    val aliases = qb.getTabAliases().toArray
    val tables = new JArrayList[String]
    aliases.foreach(alias => tables.add(qb.getTabNameForAlias(alias.asInstanceOf[String])))

    // Get schema (with column info) for each table
    schemas = new HashMap[String, JList[FieldSchema]]
    tables.foreach(tableName => {
      schemas(tableName) = metaClient.getSchema(dbName, tableName)
    })

    // Get table sizes from Hive metadata for tables which have stats calculated
    tables.foreach(tableName => {
      val table = metaClient.getTable(dbName, tableName)
      val tParams = table.getParameters()

      // XXX Row count on ANALYZE TABLE ... COMPUTE STATISTICS is broken when running from shark.
      // Must run from Hive for now to save to table metadata
      if (tParams.containsKey("numRows")) {
        val tNumRows = Integer.parseInt(tParams.get("numRows"))
        tabToHiveNumRows.put(tableName, tNumRows)
        logInfo("Got table numRows [" + tNumRows + "] for table " + dbName + "." + tableName)
      }
    })

    tabToHiveColStats = new HashMap[String, HashMap[String, ColumnStatistics]]
    tables.foreach(tableName => {
      val colToStats = new HashMap[String, ColumnStatistics]
      schemas(tableName).foreach(schema => {
        val colName = schema.getName()
        try {
          colToStats(colName) = metaClient.getTableColumnStatistics(dbName, tableName, colName)
        } catch {
          case e: NoSuchObjectException =>
            logInfo("No column stats available for "+tableName+"."+colName)
            colToStats(colName) = null
        }
      })
      tabToHiveColStats(tableName) = colToStats
    })

    // Get statistics for in-memory tables
    tabToSharkCardStats = new HashMap[String, collection.Map[Int, Long]]
    val tableNameToTable = new HashMap[String, Table]
    tables.foreach(tableName =>
      tableNameToTable(tableName) = metaClient.getTable(dbName, tableName)
    )

    tableNameToTable.foreach{ case(tableName, table) =>
      val cacheMode = CacheType.fromString(table.getParameters().get("shark.cache"))

      if (cacheMode == CacheType.HEAP) {
        // This is an in-memory table
        println("Heap cache type for table "+tableName)

        // Get table-level cardinality
        val colToCardinality = SharkEnv.memoryMetadataManager.getCardinality(tableName).getOrElse(null)
        tabToSharkCardStats(tableName) = colToCardinality
        val stats = SharkEnv.memoryMetadataManager.getStats(tableName).getOrElse(null)
        tabToSharkNumRows(tableName) = stats.values.toSeq.map(_.numRows).max

        // Get table stats
        val tableStats = SharkEnv.memoryMetadataManager.getStats(tableName).getOrElse(null)
      }
    }
  }

  def getColumnCardinality (tableName: String, columnName: String): Option[Long] = {
    var colCard: Long = 0

    if (colToCard.containsKey(tableName+"."+columnName)) {
      colToCard(tableName+"."+columnName)
    } else {
      // Get column cardinality from Shark stats
      if (tabToSharkCardStats.containsKey(tableName)) {

        // Shark stats don't have column name, so we need to get this from the field schema
        val schema = schemas(tableName)
        var colIndex =  schema.view.zipWithIndex.filter (
          (fieldTuple: Tuple2[FieldSchema, Int]) =>
            (fieldTuple._1.getName() == columnName)).unzip._2(0)
        colCard = tabToSharkCardStats(tableName)(colIndex)
      }

      // Get column cardinality from Hive stats only if we can't get it from Shark
      if (colCard == 0 && tabToHiveColStats.containsKey(tableName)) {
        val tableColStats = tabToHiveColStats.get(tableName)
        if (tableColStats != null) {
          val colStats = tableColStats.get(columnName)
          if (colStats != null) {
            // why (0)?
            val statsObjList = colStats.getStatsObj()
            if (statsObjList.size > 0) {
              val statsData = statsObjList(0).getStatsData()
              // We ignore boolean and binary fields
              if (statsData.isSetLongStats) {
                colCard = statsData.getLongStats().getNumDVs()
              } else if (statsData.isSetDoubleStats()) {
                colCard = statsData.getDoubleStats().getNumDVs()
              } else if (statsData.isSetStringStats()) {
                colCard = statsData.getStringStats().getNumDVs()
              }
            }
          }
        }
      }

      val card = if (colCard > 0) Some(colCard) else None
      colToCard(tableName+"."+columnName) = card
      card
    }
  }

  def getNumRows (tableName: String): Option[Long] = {
    if (tabToSharkNumRows.containsKey(tableName)) {
      Some(tabToSharkNumRows(tableName))
    } else if (tabToHiveNumRows.containsKey(tableName)) {
      Some(tabToHiveNumRows(tableName))
    } else {
      None
    }
  }
}