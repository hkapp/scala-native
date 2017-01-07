package scala.scalanative
package optimizer
package pass

import analysis.ControlFlow
import analysis.ClassHierarchy.Top
import analysis.Shows._

import nir._
import Inst._
import Shows._

class CFGOrdering extends Pass {

  override def preDefn = {
    case defn: Defn.Define =>
      val cfg = ControlFlow.Graph(defn.insts)
      val newInsts = cfg.map { b =>
        b.label +: b.insts
      }.flatten
      Seq(defn.copy(insts = newInsts))
  }

}

object CFGOrdering extends PassCompanion {
  override def apply(config: tools.Config, top: Top) =
    new CFGOrdering

}
