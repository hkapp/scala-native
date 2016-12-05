package scala.scalanative
package optimizer
package pass

import scala.collection.mutable
import analysis.ClassHierarchy.Top
import nir._, Shows._
import util.sh

/** Eliminates pure computations that are not being used. */
class DeadCodeElimination(implicit top: Top) extends Pass {
  import DeadCodeElimination._

  override def preDefn = {
    case defn: Defn.Define =>
      //println(s"DCE: ${showGlobal(defn.name)}")

      val insts    = defn.insts
      val cfg      = analysis.ControlFlow.Graph(insts)
      val usedef   = analysis.UseDef(cfg)
      val newinsts = mutable.UnrolledBuffer.empty[Inst]
      val paramChanges = buildParamChanges(cfg, usedef)
      val changeCf = new ChangeApplier(paramChanges)

      cfg.all.foreach { block =>
        if (usedef(block.name).alive) {
          //val newLabel = changeLabel(block.label, paramChanges(block.name))
          val newParams = applyChanges(block.label.params, paramChanges(block.name))
          //val newLabel = block.label.copy(params = )
          newinsts += block.label.copy(params = newParams)
          block.insts.foreach {
            case inst @ Inst.Let(n, op) =>
              if (usedef(n).alive) newinsts += inst
            case inst: Inst.Cf =>
              newinsts ++= changeCf(inst)
            case _ =>
              ()
          }
        }
      }

      Seq(defn.copy(insts = newinsts))
  }

  private def buildParamChanges(cfg: analysis.ControlFlow.Graph, usedef: Map[Local, analysis.UseDef.Def]): Map[Local, Seq[Boolean]] = {
    cfg.all.map { block =>
      val isEntryBlock = (block.name == cfg.entry.name)
      val paramsKept = block.params.map { param =>
        (isEntryBlock || usedef(param.name).alive)
      }
      (block.name, paramsKept)
    }.toMap
  }

  //private def changeLabel(label: Inst.Label, paramChanges: Seq[Boolean]): Inst.Label = {
    //label.copy(params = applyChanges(label.params, paramChanges))
  //}

  //private def changeCf(cfInst: Inst.Cf, paramChanges: Map[Local, Seq[Boolean]]): Inst.Cf = {
    //cfInst match {
      //case Inst.Jump(next) => Inst.Jump(changeNext(next, paramChanges))
      //case Inst.If(cond, thenp, elsep) => Inst.If(cond, changeNext(thenp, paramChanges), changeNext(elsep, paramChanges))
      //case _ => cfInst // the other cf insts can't have args in their next
    //}
  //}

  //private def changeNext(next: Next, paramChanges: Map[Local, Seq[Boolean]]): Next = {
    //next match {
      //case Next.Label(name, args) => Next.Label(name, applyChanges(args, paramChanges(name)))
      //case _ => next
    //}
  //}

}

object DeadCodeElimination extends PassCompanion {
  override def apply(config: tools.Config, top: Top) =
    new DeadCodeElimination()(top)

  class ChangeApplier(paramChanges: Map[Local, Seq[Boolean]]) extends Pass {
    override def preNext = {
      case Next.Label(name, args) => Next.Label(name, applyChanges(args, paramChanges(name)))
    }
  }

  def applyChanges[T](seq: Seq[T], changes: Seq[Boolean]): Seq[T] = {
    seq.zip(changes).collect {
      case (elem, true) => elem
    }
  }

}
