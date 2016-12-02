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

class OpportunityTesting(implicit top: Top) extends Pass {
  import OpportunityTesting._
  import Debug._

  private val oppCounts = scala.collection.mutable.HashMap.empty[String, Int]

  override def preDefn = {
    case defn: Defn.Define =>

      val methodName = showGlobal(defn.name).toString
      Debug.scope = methodName

      val cfg        = ControlFlow.Graph(defn.insts)

      val allOppTests = buildAllOppTests(defn.insts, cfg)

      for (opp <- allOppTests) {
        val id = opp.identifier
        val rawCount = opp.run()
        val newCount = oppCounts.getOrElse(id, 0) + rawCount
        oppCounts += (id -> newCount)

        if (rawCount > 0 && opp.verbose)
          println(s"$id opportunities = ${newCount}")
      }

      Seq(defn)
  }

  //def testAll(insts: Seq[Inst], cfg: ControlFlow.Graph): Unit = {
    //val sa = new TestSuppliedArgs(insts, cfg).run()
    //if (sa > 0 && saVerbose) {
      //saCount += sa
      //println("SameSuppliedArgs opportunities = "+saCount)
    //}

    //val cs = new TestConstantSwitch(insts, cfg).run()
    //if (cs > 0 && csVerbose) {
      //csCount += cs
      //println("ConstantSwitch opportunities = "+csCount)
    //}

    //val is = new TestIfSwitch(insts, cfg).run()
    //if (is > 0 && isVerbose) {
      //isCount += is
      //println("IfSwitch opportunities = "+isCount)
    //}

    //val spa = new TestSinglePredArgs(insts, cfg).run()
    //if (spa > 0 && spaVerbose) {
      //spaCount += spa
      //println("SinglePredArgs opportunities = "+spaCount)
    //}

    //val sci = new TestSameCondIf(insts, cfg).run()
    //if (sci > 0 && sciVerbose) {
      //sciCount += sci
      //println("SameCondIf opportunities = "+sciCount)
    //}

    //if (spa >0 && sa == 0) {
      //println("Inconsistency in "+Debug.scope)
    //}
  //}
}

object OpportunityTesting extends PassCompanion {
  def apply(config: tools.Config, top: Top) =
    new OpportunityTesting()(top)

  trait Opportunity {

    def run(): Int
    def identifier(): String

    final def verbose(): Boolean = {
      oppVerbose(identifier)
    }

  }

  def buildAllOppTests(insts: Seq[Inst], cfg: ControlFlow.Graph) = Seq(
    new TestSuppliedArgs(insts, cfg),
    new TestConstantSwitch(insts, cfg),
    new TestIfSwitch(insts, cfg),
    new TestSinglePredArgs(insts, cfg),
    new TestSameCondIf(insts, cfg)
  )

  val oppVerbose = Map(
    "SameSuppliedArgs" -> false,
    "ConstantSwitch" -> false,
    "IfSwitch" -> false,
    "SinglePredArgs" -> false,
    "SameCondIf" -> false
  )

  //val saVerbose = false
  //val csVerbose = false
  //val isVerbose = false
  //val spaVerbose = false
  //val sciVerbose = false

  //private var saCount = 0
  //private var csCount = 0
  //private var isCount = 0
  //private var spaCount = 0
  //private var sciCount = 0



  class TestSuppliedArgs(insts: Seq[Inst], cfg: ControlFlow.Graph) extends Opportunity {
    import scala.collection.mutable

    val identifier = "SameSuppliedArgs"

    def run(): Int = {
      val suppliedArgs = gatherArgs()
      val eligible = suppliedArgs.toList.filter { case (blockName, allArgs) =>
        cfg.find(blockName).params.zip(allArgs).exists { case (param, argValues) =>
          argValues.size == 1 || (argValues.size == 2 && argValues.contains(param))
        }
      }

      if (eligible.nonEmpty && verbose) {
        println(s"SameSuppliedArgs: ${eligible.size} eligible blocks in ${Debug.scope}:")
        println(eligible.unzip._1.map(showLocal(_)).mkString("{", ", ", "}"))
      }

      eligible.size
    }

    def gatherArgs(): Map[Local, Seq[Set[Val]]] = {
      val res = mutable.HashMap.empty[Local, Seq[Set[Val]]]
      cfg.map { block =>
        block.insts.last match {
          case Jump(Next.Label(targetName, args)) => addArgs(res, targetName, args)
          case If(_, Next.Label(thenName, thenArgs), Next.Label(elseName, elseArgs)) =>
            addArgs(res, thenName, thenArgs)
            addArgs(res, elseName, elseArgs)
          case _ =>
        }
      }

      res.toMap
    }

    def addArgs(currentRes: mutable.HashMap[Local, Seq[Set[Val]]], name: Local, args: Seq[Val]): Unit = {
      val suppliedArgs: Seq[Set[Val]] = currentRes.getOrElse(name, Seq.fill(args.size)(Set.empty[Val]))
      val newSuppliedArgs = suppliedArgs.zip(args).map { case (set, v) => set + v }
      currentRes += (name -> newSuppliedArgs)
    }

  }

  class TestConstantSwitch(insts: Seq[Inst], cfg: ControlFlow.Graph) extends Opportunity {

    val identifier = "ConstantSwitch"

    def run(): Int = {
      val eligible = insts.filter {
        case Switch(_: Val.Local, _, _) => false
        case Switch(_, _, _) => true
        case _ => false
      }

      if (eligible.nonEmpty && verbose) {
        println(s"ConstantSwitch: ${eligible.size} eligible switches in ${Debug.scope}:")
        println(eligible.map(showInst(_)).mkString("\n"))
      }

      eligible.size
    }

  }

  class TestIfSwitch(insts: Seq[Inst], cfg: ControlFlow.Graph) extends Opportunity {

    val identifier = "IfSwitch"

    def run(): Int = {
      val eligible = insts.filter {
        case Switch(_, _, cases) => cases.size == 1
        case _ => false
      }

      if (eligible.nonEmpty && verbose) {
        println(s"IfSwitch: ${eligible.size} eligible switches in ${Debug.scope}:")
        println(eligible.map(showInst(_)).mkString("\n"))
      }

      eligible.size
    }

  }

  class TestSinglePredArgs(insts: Seq[Inst], cfg: ControlFlow.Graph) extends Opportunity {

    val identifier = "SinglePredArgs"

    def run(): Int = {
      val eligible = cfg.all.filter { block =>
        block.pred.size == 1 && block.params.nonEmpty && !block.pred.head.insts.last.isInstanceOf[Inst.Try]
      }

      if (eligible.nonEmpty && verbose) {
        println(s"SinglePredArgs: ${eligible.size} eligible blocks in ${Debug.scope}:")
        println(eligible.map(b => showLocal(b.name)).mkString("{", ", ", "}"))
      }

      eligible.size
    }

  }

  class TestSameCondIf(insts: Seq[Inst], cfg: ControlFlow.Graph) extends Opportunity {
    import scala.collection.mutable

    val identifier = "SameCondIf"

    def run(): Int = {
      val conditionUses = getCondUses()
      val eligible = conditionUses.filter { case (_, ifs) => ifs.size > 1 }

      if (eligible.nonEmpty && verbose) {
        println(s"SameCondIf: ${eligible.size} conditions used more than once in ${Debug.scope}:")
        println(eligible.map(kv => showLocal(kv._1)).mkString("{", ", ", "}"))
        println(codeFlowDot(cfg))
      }

      eligible.size
    }

    def getCondUses(): Map[Local, Set[Inst]] = {
      val result = mutable.HashMap.empty[Local, Set[Inst]]
      insts.map {
        case inst @ If(Val.Local(name, _), _, _) =>
          result += (name -> (result.getOrElse(name, Set.empty) + inst))

        case _ =>
      }

      result.toMap
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
