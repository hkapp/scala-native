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

class CfChainsSimplification(implicit fresh: Fresh, top: Top) extends Pass {
  import CfChainsSimplification._
  import Debug._

  override def preDefn = {
    case defn: Defn.Define =>

      val methodName = showGlobal(defn.name).toString
      Debug.scope = methodName

      val cfg        = ControlFlow.Graph(defn.insts)

      val debugMethod = "@deltablue.BinaryConstraint::chooseMethod_i32_unit"
      //Debug.verbose = (methodName == debugMethod)
      Debug.verbose = false

      //println(s"${methodName}")

      val newInsts = defn.insts.flatMap {
        case cfInst: Cf => simplifyCf(cfInst, cfg)
        case otherInst @ _ => Seq(otherInst)
      }

      Seq(defn.copy(insts = newInsts))
  }

  def simplifyCf(cfInst: Inst, cfg: ControlFlow.Graph): Seq[Inst] = {
    var nonCf = Seq.empty[Inst]
    //var lastCf = cfInst
    var currentCf = cfInst
    var continue = true

    while(continue) {
      //lastCf = currentCf
      val wholeOptSeq = simplifyCfOnce(currentCf, cfg)
      val newCf = wholeOptSeq.last
      continue = (newCf != currentCf)
      nonCf ++= wholeOptSeq.dropRight(1)
      currentCf = newCf
    }

    nonCf :+ currentCf
  }

  def simplifyCfOnce(cfInst: Inst, cfg: ControlFlow.Graph): Seq[Inst] = {
    val simpleRes = cfInst match {
      case Jump(Next.Label(targetName, args)) =>
        val targetBlock = cfg.find(targetName)
        targetBlock.insts match {

          case Seq(nextCf: Cf) =>
            val nextBlockArgNames = targetBlock.params.map(_.name)
            val usedef = UseDef(cfg)
            val canSkip = nextBlockArgNames.forall(arg => usedef(arg).uses.size <= 1) // should be change to more complex checks, i.e. variable doesn't get out of its block

            if (canSkip) {
              val evaluation = nextBlockArgNames.zip(args).toMap
              //println(s"In ${Debug.scope}:")
              //println(showMap(evaluation.map{case (l, v) => (showLocal(l), showVal(v)) }))
              //replaceInstVals(nextCf, evaluation)
              val replacer = new ArgumentReplacer(evaluation)
              val replacedArgs = replacer(nextCf)
              assert(replacedArgs.size == 1)
              replacedArgs.head
            }
            else {
              cfInst
            }

          case _ => cfInst
        }

      case If(Val.True, next, _) =>
        Jump(next)

      case If(Val.False, _, next) =>
        Jump(next)

      case If(cond, thenp, elsep) =>
        If(cond, simplifyIfBranch(thenp, cfg), simplifyIfBranch(elsep, cfg))

      case Switch(value, default, Seq()) => Jump(default)

      case Switch(value, default, cases) => Switch(value, simplifySwitchCase(default, cfg), cases.map(simplifySwitchCase(_, cfg)))

      case _ => cfInst
    }

    fixIf(simpleRes)
  }

  def fixIf(inst: Inst): Seq[Inst] = {
    inst match {
      case If(cond, thenNext @ Next.Label(thenName, thenArgs), Next.Label(elseName, elseArgs)) =>
        if (thenName == elseName) {
          if (thenArgs == elseArgs) {
            Seq(Jump(thenNext))
          }
          else {
            val (newArgs, selects) = thenArgs.zip(elseArgs).map { case (thenV, elseV) =>
              val freshVar = fresh()
              val selectInst = Let(freshVar, Op.Select(cond, thenV, elseV))
              (Val.Local(freshVar, thenV.ty), selectInst)
            }.unzip

            selects :+ Jump(Next.Label(thenName, newArgs))
          }
        }
        else {
          Seq(inst)
        }

      case _ => Seq(inst)
    }
  }

  def simplifyIfBranch(branch: Next, cfg: ControlFlow.Graph): Next = {
    var newBranch = branch
    var currentCf: Inst = Jump(branch)
    var continue = true

    while(continue) {
      val optSeq = simplifyCfOnce(currentCf, cfg)
      optSeq match {
        case Seq(Jump(next)) => newBranch = next
        case _ =>
      }
      val newCf = optSeq.last
      continue = (optSeq.size == 1 && newCf != currentCf)
      currentCf = newCf
    }

    newBranch
  }

  def simplifySwitchCase(swCase: Next, cfg: ControlFlow.Graph): Next = {
    swCase match {
      case Next.Case(value, name) => {
        var newLocalJump = name
        //var lastCf: Inst = Jump(Next.Label(name, Seq.empty))
        var currentCf: Inst = Jump(Next.Label(name, Seq.empty))
        var continue = true

        while(continue) {
          //lastCf = currentCf
          val optSeq = simplifyCfOnce(currentCf, cfg)
          optSeq match {
            case Seq(Jump(Next.Label(newLocal, Seq()))) => newLocalJump = newLocal
            case _ =>
          }
          val newCf = optSeq.last
          continue = (optSeq.size == 1 && currentCf != newCf)
          currentCf = newCf
        }

        Next.Case(value, newLocalJump)
      }

      case _ => swCase
    }
  }

}

object CfChainsSimplification extends PassCompanion {
  def apply(config: tools.Config, top: Top) =
    new CfChainsSimplification()(top.fresh, top)

  class ArgumentReplacer(evaluation: Map[Local, Val]) extends Pass {

    override def preVal = {
      case local @ Val.Local(name, _) =>
        evaluation.getOrElse(name, local)
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

    def cfgSize(cfg: ControlFlow.Graph): Int = {
      cfg.map(_ => 1).sum
    }

  }


}
