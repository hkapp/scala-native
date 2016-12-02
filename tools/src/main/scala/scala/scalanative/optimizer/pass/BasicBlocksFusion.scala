package scala.scalanative
package optimizer
package pass

import analysis.ControlFlow
import analysis.ControlFlow.Block
import analysis.UseDef
import analysis.ClassHierarchy.Top
import analysis.Shows._

import nir._
import Inst._
import Shows._
import util.sh

class BasicBlocksFusion(implicit fresh: Fresh, top: Top) extends Pass {
  import BasicBlocksFusion._
  import Debug._

  private var maxBlocks = 0
  private var maxRemoved = 0

  override def preDefn = {
    case defn: Defn.Define =>

      val methodName = showGlobal(defn.name).toString
      Debug.scope = methodName

      val cfg        = ControlFlow.Graph(defn.insts)

      val debugMethod = "@deltablue.BinaryConstraint::chooseMethod_i32_unit"
      //Debug.verbose = (methodName == debugMethod)
      Debug.verbose = false

      //println(s"${methodName}")

      val noDeadBlocksCode = cfg.map { b =>
        b.label +: b.insts
      }.flatten
      val noDeadBlocksCfg = ControlFlow.Graph(noDeadBlocksCode)

      val newInsts = fuseBlocks(noDeadBlocksCode, noDeadBlocksCfg)

      Seq(defn.copy(insts = newInsts))
  }

  def fuseBlocks(insts: Seq[Inst], cfg: ControlFlow.Graph): Seq[Inst] = {
    val workList = scala.collection.mutable.Stack.empty[Block]
    val visited = scala.collection.mutable.Set.empty[Block]
    var result = Seq.empty[Inst]

    workList.push(cfg.entry)
    while(workList.nonEmpty) {
      val block = workList.pop()
      visited += block
      val (addedCode, addedWork) = fusedBlockCode(block, cfg.entry)
      result ++= addedCode
      workList.pushAll(addedWork.filterNot(visited))
    }

    result
  }

  def fusedBlockCode(block: Block, entryBlock: Block) : (Seq[Inst], Seq[Block]) = {
    val (blockCode, blockCf) = (block.insts.dropRight(1), block.insts.last)

    val (codeEnding, succWork) =
      if (block.succ.size == 1 && block.succ.head.pred.size == 1 && block.succ.head.name != entryBlock.name) {
        val nextBlock = block.succ.head
        val (recCode, recWork) = fusedBlockCode(nextBlock, entryBlock)
        val paramDef = blockCf match {
          case Jump(Next.Label(_, args)) =>
            val params = nextBlock.params.map(_.name)
            params.zip(args).map { case (param, arg) =>
              Let(param, Op.Copy(arg))
            }

          case _ => Seq.empty
        }

        (paramDef ++ recCode.tail, recWork)
      }
      else {
        (Seq(blockCf), block.succ)
      }

    ((block.label +: blockCode) ++ codeEnding, succWork)
  }

}

object BasicBlocksFusion extends PassCompanion {
  def apply(config: tools.Config, top: Top) =
    new BasicBlocksFusion()(top.fresh, top)

  object Debug {

    var verbose = false
    var scope   = ""

    def showMap[A, B](map: Map[A, B]): String = {
      map.toList.map {
        case (k, v) => s"($k -> $v)"
      }.mkString("\n")
    }

    private def cfgSize(cfg: ControlFlow.Graph): Int = {
      cfg.map(_ => 1).sum
    }

  }


}
