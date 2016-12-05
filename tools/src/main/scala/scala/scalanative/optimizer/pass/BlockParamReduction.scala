package scala.scalanative
package optimizer
package pass

import scala.collection.mutable

import analysis.ControlFlow
import analysis.ControlFlow.Block
import analysis.UseDef
import analysis.ClassHierarchy.Top
import analysis.Shows._

import nir._
import Inst._
import Shows._
import util.sh

class BlockParamReduction(implicit top: Top) extends Pass {
  import BlockParamReduction._
  import Debug._

  //private var paramChanges = Map.empty[Local, Seq[Boolean]]
  private var paramValues = Map.empty[Local, Seq[Option[Val]]]

  override def preDefn = {
    case defn: Defn.Define =>

      val methodName = showGlobal(defn.name).toString
      Debug.scope = methodName

      val cfg        = ControlFlow.Graph(defn.insts)

      val suppliedArgs = gatherArgs(cfg)
      //val buildBlockChanges = buildBlockChanges(suppliedArgs)
      paramValues = reduceAllParams(cfg, suppliedArgs)

      //val suppliedArgs = gatherArgs(cfg)
      //val eligible = suppliedArgs.toList.filter { case (blockName, allArgs) =>
        //cfg.find(blockName).params.zip(allArgs).exists { case (param, argValues) =>
          //argValues.size == 1 || (argValues.size == 2 && argValues.contains(param))
        //}
      //}

      Seq(defn)
  }

  override def preInst = {
    case Label(name, params) =>
      val paramVals = paramValues(name)
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
      val newArgs = args.zip(paramValues(name)).collect {
        case (arg, scala.None) => arg
      }
      Next.Label(name, newArgs)
  }

  private def gatherArgs(cfg: ControlFlow.Graph): Map[Local, Seq[Set[Val]]] = {
      val argGatherer = new ArgGatherer
      cfg.all.foreach(b => argGatherer(b.insts.last))
      argGatherer.result
  }

  //private def buildBlockChanges(suppliedArgs: Map[Local, Seq[Set[Val]]]): Map[Local, Seq[]]

  private def reduceAllParams(cfg: ControlFlow.Graph, suppliedArgs: Map[Local, Seq[Set[Val]]]): Map[Local, Seq[Option[Val]]] = {
    cfg.all.map { b =>
      (b.name -> reduceParams(b, suppliedArgs))
    }.toMap
  }

  private def reduceParams(block: Block, suppliedArgs: Map[Local, Seq[Set[Val]]]): Seq[Option[Val]] = {
    block.params.zip(suppliedArgs(block.name)).map {
      case (param, argValues) =>
        val noRecArgs = argValues - param
        if (noRecArgs.size == 1)
          Some(noRecArgs.head)
        else
          scala.None
    }
  }

  //private def gatherArgs(cfg: ControlFlow.Graph): Map[Local, Seq[Set[Val]]] = {
    //val res = mutable.HashMap.empty[Local, Seq[Set[Val]]]
    //cfg.map { block =>
      //block.insts.last match {
        //case Jump(Next.Label(targetName, args)) => addArgs(res, targetName, args)
        //case If(_, Next.Label(thenName, thenArgs), Next.Label(elseName, elseArgs)) =>
          //addArgs(res, thenName, thenArgs)
          //addArgs(res, elseName, elseArgs)
        //case _ =>
      //}
    //}

    //res.toMap
  //}

}

object BlockParamReduction extends PassCompanion {
  def apply(config: tools.Config, top: Top) =
    new BlockParamReduction()(top)

  class ArgGatherer extends Pass {

    private val res = mutable.HashMap.empty[Local, Seq[Set[Val]]]

    def result = res.toMap

    override def preNext = {
      case next @ Next.Label(name, args) =>
        addArgs(name, args)
        next
    }

    private def addArgs(name: Local, args: Seq[Val]): Unit = {
      val suppliedArgs: Seq[Set[Val]] = res.getOrElse(name, Seq.fill(args.size)(Set.empty[Val]))
      assert(suppliedArgs.size == args.size)
      val newSuppliedArgs = suppliedArgs.zip(args).map { case (set, v) => set + v }
      res += (name -> newSuppliedArgs)
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
