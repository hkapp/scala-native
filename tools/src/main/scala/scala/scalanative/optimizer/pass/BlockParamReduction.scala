package scala.scalanative
package optimizer
package pass

import scala.collection.mutable

import analysis.ControlFlow
import analysis.ControlFlow.Block
import analysis.UseDef
import analysis.ClassHierarchy.Top
import analysis.Shows._
import analysis.SuppliedArguments

import nir._
import Inst._
import Shows._
import util.sh

class BlockParamReduction(implicit top: Top) extends Pass {
  import BlockParamReduction._
  import Debug._

  override def preDefn = {
    case defn: Defn.Define =>

      val methodName = showGlobal(defn.name).toString
      Debug.scope = methodName

      val cfg        = ControlFlow.Graph(defn.insts)

      val suppliedArgs = SuppliedArguments.build(cfg)
      val changeParams = new ParamChanger(suppliedArgs)

      changeParams(defn)
  }

}

object BlockParamReduction extends PassCompanion {
  def apply(config: tools.Config, top: Top) =
    new BlockParamReduction()(top)

  class ParamChanger(val suppliedArgs: SuppliedArguments) extends Pass {
    override def preInst = {
      case Label(name, params) =>
        val paramVals = suppliedArgs.paramValues(name)
        val newParams = params.zip(paramVals).collect {
          case (param, scala.None) => param
        }
        val argCopies = params.zip(paramVals).collect {
          case (param, Some(value)) =>
            Let(param.name, Op.Copy(value))
        }
        val newLabel = Label(name, newParams)
        newLabel +: argCopies
    }

    override def preNext = {
      case Next.Label(name, args) =>
        val newArgs = args.zip(suppliedArgs.paramValues(name)).collect {
          case (arg, scala.None) => arg
        }
        Next.Label(name, newArgs)
    }
  }

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
