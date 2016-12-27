package scala.scalanative
package optimizer
package pass

import analysis.ClassHierarchy.Top

import nir._
import Inst.Let
import Bin._
import Comp._

import scala.None

/** Simplifies single instruction patterns */
class PartialEvaluation extends Pass {
  import PartialEvaluation._
  import ConstantFolding._

  override def preInst = {
    case inst: Inst =>
      val newInst = inst match {

        /* Iadd */
        case Let(n, Op.Bin(Iadd, ty, lhs, IVal(0))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Iadd, ty, lhs, rhs)) if (lhs == rhs) =>
          Let(n, Op.Bin(Imul, ty, lhs, IVal(2, ty)))

        /* Isub */
        case Let(n, Op.Bin(Isub, ty, lhs, IVal(0))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Isub, ty, lhs, IVal(i))) if (i < 0) =>
          Let(n, Op.Bin(Iadd, ty, lhs, IVal(-i, ty)))

        case Let(n, Op.Bin(Isub, ty, lhs, rhs)) if (lhs == rhs) =>
          copy(n, IVal(0, ty))

        /* Imul */
        case Let(n, Op.Bin(Imul, ty, lhs, IVal(0))) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(Imul, ty, lhs, IVal(1))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Imul, ty, lhs, PowerOf2(shift))) =>
          Let(n, Op.Bin(Shl, ty, lhs, shift))

        /* Sdiv */
        case Let(n, Op.Bin(Sdiv, ty, _, IVal(0))) =>
          copy(n, Val.Undef(ty))

        case Let(n, Op.Bin(Sdiv, ty, lhs, IVal(1))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Sdiv, ty, IVal(0), _)) =>
          copy(n, IVal(0, ty))

        /* Udiv */
        case Let(n, Op.Bin(Udiv, ty, _, IVal(0))) =>
          copy(n, Val.Undef(ty))

        case Let(n, Op.Bin(Udiv, ty, lhs, IVal(1))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Udiv, ty, IVal(0), _)) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(Udiv, ty, lhs, PowerOf2(shift))) =>
          Let(n, Op.Bin(Lshr, ty, lhs, shift))

        /* Srem */
        case Let(n, Op.Bin(Srem, ty, lhs, IVal(0))) =>
          copy(n, Val.Undef(ty))

        case Let(n, Op.Bin(Srem, ty, lhs, IVal(1))) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(Srem, ty, lhs, IVal(-1))) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(Srem, ty, IVal(0), rhs)) =>
          copy(n, IVal(0, ty))

        /* Urem */
        case Let(n, Op.Bin(Urem, ty, lhs, IVal(0))) =>
          copy(n, Val.Undef(ty))

        case Let(n, Op.Bin(Urem, ty, lhs, IVal(1))) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(Urem, ty, IVal(0), rhs)) =>
          copy(n, IVal(0, ty))

        /* Shl */
        case Let(n, Op.Bin(Shl, ty, lhs, IVal(0))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Shl, ty, IVal(0), _)) =>
          copy(n, IVal(0, ty))

        /* Lshr */
        case Let(n, Op.Bin(Lshr, ty, lhs, IVal(0))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Lshr, ty, IVal(0), rhs)) =>
          copy(n, IVal(0, ty))

        /* Ashr */
        case Let(n, Op.Bin(Ashr, ty, lhs, IVal(0))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Ashr, ty, IVal(0), rhs)) =>
          copy(n, IVal(0, ty))

        /* And */
        case Let(n, Op.Bin(And, ty, lhs, rhs)) if (lhs == rhs) =>
          copy(n, lhs)

        case Let(n, Op.Bin(And, ty, lhs, IVal(0))) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(And, ty, lhs, IVal(-1))) =>
          copy(n, lhs)

        /* Or */
        case Let(n, Op.Bin(Or, ty, lhs, rhs)) if (lhs == rhs) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Or, ty, lhs, IVal(0))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Or, ty, lhs, IVal(-1))) =>
          copy(n, IVal(-1, ty))

        /* Xor */
        case Let(n, Op.Bin(Xor, ty, lhs, rhs)) if (lhs == rhs) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(Xor, ty, lhs, IVal(0))) =>
          copy(n, lhs)

        /* Ieq */
        case Let(n, Op.Comp(Ieq, ty, lhs, rhs)) if (lhs == rhs) =>
          copy(n, Val.True)

        case Let(n, Op.Comp(Ieq, ty, lhs, Val.True)) =>
          copy(n, lhs)

        case Let(n, Op.Comp(Ieq, ty, lhs, Val.False)) =>
          neg(n, lhs)

        /* Ine */
        case Let(n, Op.Comp(Ine, ty, lhs, rhs)) if (lhs == rhs) =>
          copy(n, Val.False)

        case Let(n, Op.Comp(Ine, ty, lhs, Val.False)) =>
          copy(n, lhs)

        case Let(n, Op.Comp(Ine, ty, lhs, Val.True)) =>
          neg(n, lhs)

        /* Select */
        case Let(n, Op.Select(cond, thenv, elsev)) if (thenv == elsev) =>
          copy(n, thenv)

        case Let(n, Op.Select(cond, Val.True, Val.False)) =>
          copy(n, cond)

        case Let(n, Op.Select(cond, Val.False, Val.True)) =>
          neg(n, cond)


        case _ => inst
      }
      Seq(newInst)
  }

  private def copy(n: Local, value: Val): Inst =
    Let(n, Op.Copy(value))

  private def neg(n: Local, value: Val): Inst =
    Let(n, Op.Bin(Xor, Type.Bool, value, Val.True))

}

object PartialEvaluation extends PassCompanion {
  override def apply(config: tools.Config, top: Top) =
    new PartialEvaluation

  object PowerOf2 {
    def unapply(v: Val): Option[Val] = {
      v match {
        case Val.I8(b) =>
          extractPow2(b).map(p => Val.I8(p.toByte))

        case Val.I16(s) =>
          extractPow2(s).map(p => Val.I16(p.toShort))

        case Val.I32(i) =>
          extractPow2(i).map(p => Val.I32(p.toInt))

        case Val.I64(l) =>
          extractPow2(l).map(p => Val.I64(p.toLong))

        case _ => None
      }
    }

    def log2(x: Double): Double =
      math.log(x) / math.log(2)

    def extractPow2(x: Double): Option[Double] = {
      if (x < 1)
        None
      else {
        val log = log2(x)
        if (math.floor(log) == log)
          Some(log)
        else
          None
      }
    }
  }

}
