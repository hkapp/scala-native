package scala.scalanative
package optimizer
package analysis

import ControlFlow.Block
import nir.Shows._

object Shows {

  private def blockToString(block: Block): String =
    showLocal(block.name).toString

  def showCFG(cfg: ControlFlow.Graph): String = {
    cfg.all.map { block =>
      val succStr =
        block.succ.map(blockToString).mkString("(", ",", ")")
      val predStr =
        block.pred.map(blockToString).mkString("(", ",", ")")
      s"${blockToString(block)} -> ${succStr}, pred = ${predStr}"
    }.mkString("\n")
  }

  def showDominatorTree(domination: Map[Block, Set[Block]]): String = {
    domination.toSeq
      .sortBy(_._1.name.id)
      .map {
        case (block, set) =>
          s"${blockToString(block)} -> ${set.map(blockToString).mkString("(", ",", ")")}"
      }
      .mkString("\n")
  }

  def cfgToDot(cfg: ControlFlow.Graph): String = {
    def blockToDot(block: Block): String = {
      val successors = block.succ
      val blockID    = block.name.id
      if (successors.nonEmpty)
        successors
          .map(succ => succ.name.id.toString)
          .mkString(s"${blockID} -> {", " ", "};")
      else
        s"${blockID} [ shape=doublecircle ];"
    }

    s"""
       |digraph {
       | node [shape=circle, width=0.6, fixedsize=true];
       |${cfg.map(blockToDot).mkString("\n")}
       |}
    """.stripMargin
  }

  def codeFlowDot(cfg: ControlFlow.Graph): String = {

    val lineLength = 50

    def chopLine(line: String): String = {
      if (line.length > lineLength)
        line.take(lineLength - 1) + "#"
      else
        line
    }

    def codeString(block: Block): String = {
      val allInsts = block.label +: block.insts
      val codeLines = allInsts.map(i => showInst(i).toString)
      val formattedLines = codeLines.head +: codeLines.tail.map("  " + _)
      val choppedLines = formattedLines.map(chopLine)
      choppedLines.mkString("\n")
    }

    def blockToDot(block: Block): String = {
      val successors = block.succ
      val blockID    = block.name.id
      val nodeLabel = codeString(block).replace("\n", "\\l").replace("\"", "\\\"") + "\\l" // the \l is not a mistake !

      if (successors.nonEmpty) {
        val arrowPart = successors
                        .map(succ => succ.name.id.toString)
                        .mkString(s"${blockID} -> {", " ", "};")
        val stylePart = s"""${blockID} [ label="${nodeLabel}" ]"""
        arrowPart + "\n" + stylePart
      }
      else
        s"""${blockID} [ style=bold, label="${nodeLabel}" ];"""
    }

    s"""
       |digraph {
       | node [shape=box, fontname="Courier"];
       |${cfg.map(blockToDot).mkString("\n")}
       |}
    """.stripMargin
  }
}
