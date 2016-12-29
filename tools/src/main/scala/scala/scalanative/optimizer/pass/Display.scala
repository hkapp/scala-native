package scala.scalanative
package optimizer
package pass

import analysis.ControlFlow
import analysis.ClassHierarchy.Top
import analysis.Shows._

import nir._
import Inst._
import Shows._

class Display extends Pass {

  override def preDefn = {
    case defn: Defn.Define =>
      val methodName = showGlobal(defn.name).toString
      val displayName = "@Test$::main_class.ssnr.ObjectArray_unit"

      if (methodName == displayName) {
        val cfg = ControlFlow.Graph(defn.insts)
        println(codeFlowDot(cfg))
      }

      Seq(defn)
  }

}

object Display extends PassCompanion {
  override def apply(config: tools.Config, top: Top) =
    new Display

}
