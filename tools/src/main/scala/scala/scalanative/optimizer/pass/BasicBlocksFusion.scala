package scala.scalanative
package optimizer
package pass

import analysis.ControlFlow
import analysis.ControlFlow.Block

import nir._
import Inst._
import Shows.showInst

class BasicBlocksFusion extends Pass {
  import BasicBlocksFusion._

  override def preDefn = {
    case defn: Defn.Define =>
      val cfg = ControlFlow.Graph(defn.insts)

      /* This is an ugly trick to ensure that there are no unreachable blocks.
       * This pass is very dependent on that, and does not really require DCE
       * before it, except for that
       */
      val noDeadBlocksCode = cfg.map { b =>
        b.label +: b.insts
      }.flatten

      val noDeadBlocksCfg = ControlFlow.Graph(noDeadBlocksCode)

      val newInsts = fuseBlocks(noDeadBlocksCode, noDeadBlocksCfg)

      Seq(defn.copy(insts = newInsts))
  }

  private def fuseBlocks(insts: Seq[Inst], cfg: ControlFlow.Graph): Seq[Inst] = {
    val workList = scala.collection.mutable.Stack.empty[Block]
    val visited  = scala.collection.mutable.Set.empty[Block]
    var result   = Seq.empty[Inst]

    workList.push(cfg.entry)
    while (workList.nonEmpty) {
      val block = workList.pop()

      if (!visited(block)) {
        visited += block

        val (addedCode, addedWork) = fusedBlockCode(block, cfg.entry)

        result ++= addedCode
        workList.pushAll(addedWork)
      }
    }

    result
  }

  /* This produces the fused block code, starting from the given block.
   * It also returns what are the next blocks, because fused blocks can't be
   * re-processed (it would create multiple definitions for the same variable)
   */
  private def fusedBlockCode(block: Block,
                             entryBlock: Block): (Seq[Inst], Seq[Block]) = {
    val (blockCode, blockCf) = (block.insts.dropRight(1), block.insts.last)

    val (codeEnding, succWork) = blockCf match {
      // We only fuse if we have a Jump instruction
      // All other cases should reduce to a Jump after CfChainsSimplification
      case Jump(Next.Label(_, args))
          if (block.succ.size == 1 && block.succ.head.pred.size == 1 && block.succ.head.name != entryBlock.name) =>
        val nextBlock          = block.succ.head
        val (recCode, recWork) = fusedBlockCode(nextBlock, entryBlock)
        val params             = nextBlock.params.map(_.name)

        // Replace the parameters of the fused block with the supplied arguments
        val paramDef = params.zip(args).map {
          case (param, arg) =>
            Let(param, Op.Copy(arg))
        }

        // need to drop the first instruction of recCode, as it is the block label
        (paramDef ++ recCode.tail, recWork)

      // Any other case can't be fused
      case _ => (Seq(blockCf), block.succ)
    }

    // Rebuild the code from the label, followed by the code of the block,
    // and then the ending (either fusion or normal Cf)
    ((block.label +: blockCode) ++ codeEnding, succWork)
  }

}

object BasicBlocksFusion extends PassCompanion {
  def apply(config: tools.Config, top: analysis.ClassHierarchy.Top) =
    new BasicBlocksFusion
}
