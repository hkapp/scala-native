package scala.scalanative
package optimizer
package pass

import analysis.ControlFlow
import analysis.ControlFlow.Block
import analysis.UseDef
import analysis.ClassHierarchy.Top

import nir._
import Inst._
import Shows._
import util.sh

class SimplifyUnit(implicit top: Top) extends Pass {
  import SimplifyUnit._
  import Debug._

  private var canPerform = false

  override def preInst = {
    case inst: Inst.Label =>
      canPerform = false
      Seq(inst)
    case inst @ _ =>
      canPerform = true
      Seq(inst)
  }

  override def preVal = {
    case Val.Local(_, Type.Unit) if (canPerform) => Val.Unit
  }

  //override def preDefn = {
    //case defn: Defn.Define =>

      //val methodName = showGlobal(defn.name).toString
      //Debug.scope = methodName

      //val cfg = ControlFlow.Graph(defn.insts)
      //val newInsts = defn.insts.head +: defn.insts.tail.map(simplifyInst(_, cfg))

      ////val debugMethod = testedMethod
      ////if (methodName == debugMethod) {
        ////val newCfg = ControlFlow.Graph(newInsts)
        ////println("Old CFG:")
        ////println(analysis.Shows.cfgToDot(cfg))
        ////println("New CFG:")
        ////println(analysis.Shows.cfgToDot(newCfg))
      ////}

      //Seq(defn.copy(insts = newInsts))
  //}

  private def simplifyInst(inst: Inst, cfg: ControlFlow.Graph): Inst = {
    inst match {
      case Label(name, params) => Label(name, params.filterNot(_.valty == Type.Unit))
      case cf: Cf => simplifyCf(cf, cfg)
      case _ => replaceUnitValsInst(inst)
    }
  }

  private def simplifyCf(cf: Inst.Cf, cfg: ControlFlow.Graph): Inst = {
    val unitArgRm = cf match {
      case Jump(next) => Jump(simplifyNext(next, cfg))
      case If(value, thenp, elsep) => If(value, simplifyNext(thenp, cfg), simplifyNext(elsep, cfg))
      case Switch(value, default, cases) => Switch(value, simplifyNext(default, cfg), cases.map(simplifyNext(_, cfg)))
      case Invoke(ty, ptr, args, succ, fail) => Invoke(ty, ptr, args, simplifyNext(succ, cfg), simplifyNext(fail, cfg))

      case Try(succ, fail) => Try(simplifyNext(succ, cfg), simplifyNext(fail, cfg))

      case _ => cf
    }

    replaceUnitValsInst(unitArgRm)
  }

  private def simplifyNext(next: Next, cfg: ControlFlow.Graph): Next = {
    // this causes problems if next is the first/entry block
    next match {
      case Next.Label(name, args) =>
        val paramTypes = cfg.find(name).params.map(_.valty)
        val typedArgs = args.zip(paramTypes)
        val correctTypedArgs = typedArgs.filterNot { case (_, ty) => ty == Type.Unit }
        val keptArgs = correctTypedArgs.map{ case (v, _) => v }
        Next.Label(name, keptArgs)

      case _ => next
    }
  }

  private def replaceUnitValsInst(inst: Inst): Inst = {
    inst match {
      case Let(name, op) => Let(name, replaceUnitValsOp(op))
      case Ret(value) => Ret(replaceUnitVal(value))
      case If(value, thenp, elsep) => If(replaceUnitVal(value), thenp, elsep) // replace unit val in next ?
      case Switch(value, default, cases) => Switch(replaceUnitVal(value), default, cases)
      case Invoke(ty, ptr, args, succ, fail) => Invoke(ty, replaceUnitVal(ptr), replaceUnitVals(args), succ, fail)
      case Throw(value) => Throw(replaceUnitVal(value))
      case _ => inst
    }
  }

  private def replaceUnitValsOp(op: Op): Op = {
    import Op._
    op match {
      case Call(ty, ptr, args)    => Call(ty, replaceUnitVal(ptr), replaceUnitVals(args))
      case Load(Type.Unit, ptr)          => Copy(Val.Unit) // can we do that ?
      //case Load(ty, ptr)          => Copy()
      case Store(ty, ptr, value)  => Store(ty, replaceUnitVal(ptr), replaceUnitVal(value))
      //case Elem(ty, ptr, indexes) => "Elem" +: ty +: ptr +: indexes
      case Extract(aggr, indexes) => Extract(replaceUnitVal(aggr), indexes)
      case Insert(aggr, value, indexes) =>
        Insert(replaceUnitVal(aggr), replaceUnitVal(value), indexes)

      //case Stackalloc(ty, n)          => Seq("Stackalloc", ty, n)
      case Bin(bin, ty, l, r)         => Bin(bin, ty, replaceUnitVal(l), replaceUnitVal(r))
      case Comp(comp, ty, l, r)       => Comp(comp, ty, replaceUnitVal(l), replaceUnitVal(r))
      case Conv(conv, ty, value)      => Conv(conv, ty, replaceUnitVal(value))
      case Select(cond, thenv, elsev) => Select(replaceUnitVal(cond), replaceUnitVal(thenv), replaceUnitVal(elsev))

      case Field(obj, name)           => Field(replaceUnitVal(obj), name)
      case Method(obj, name)          => Method(replaceUnitVal(obj), name)
      case As(ty, obj)                => As(ty, replaceUnitVal(obj))
      case Is(ty, obj)                => Is(ty, replaceUnitVal(obj))
      case Copy(value)                => Copy(replaceUnitVal(value))
      case Closure(ty, fun, captures) => Closure(ty, replaceUnitVal(fun), replaceUnitVals(captures))

      case _ => op
    }
  }

  private def replaceUnitVal(value: Val): Val = {
    import Val._
    value match {
      case Struct(name, values)  => Struct(name, replaceUnitVals(values))
      case Array(elemty, values) => Array(elemty, replaceUnitVals(values))
      case Const(value)          => Const(replaceUnitVal(value))

      case Local(_, Type.Unit) => Val.Unit
      case Global(_, Type.Unit) => Val.Unit

      case _ => value
    }
  }

  private def replaceUnitVals(values: Seq[Val]): Seq[Val] = {
    values.map(replaceUnitVal)
  }

}

object SimplifyUnit extends PassCompanion {
  def apply(ctx: Ctx) = new SimplifyUnit()(ctx.top)

  object Debug {

    var verbose = false
    var scope   = ""

    def showMap[A, B](map: Map[A, B]): String = {
      map.toList.map {
        case (k, v) => s"($k -> $v)"
      }.mkString("\n")
    }
  }


}
