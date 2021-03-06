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

package shark.memstore2

import shark.memstore2.column.ColumnStats


/**
 * Stores column statistics for a table partition.
 */
class TablePartitionStats(val stats: Array[ColumnStats[_]], val numRows: Long)
  extends Serializable {

  override def toString =
    numRows + " rows\n" +
    stats.zipWithIndex.map { case (column, index) =>
      "  column " + index + " " +
      { if (column != null) column.toString else "no column statistics" }
    }.mkString("\n")

  def estimateCardinality() {
    stats.foreach(_.estimateCardinality())
  }
}
