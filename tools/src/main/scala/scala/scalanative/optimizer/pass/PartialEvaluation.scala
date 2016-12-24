package scala.scalanative
package optimizer
package pass

import analysis.ClassHierarchy._
import analysis.ClassHierarchyExtractors._
import analysis.ControlFlow

import nir._
import Inst._
import Shows._
import Bin._
import Comp._

import scala.None
import scala.collection.mutable

class PartialEvaluation extends Pass {
  import PartialEvaluation._
  import ConstantFolding._

  override def preInst = {
    case inst: Inst =>
      val newInst = inst match {
        // TODO: take care of overflows

        // Patterns:
        /* %src.39 = xor[i32] %src.38: i32, %src.7: i32
         * %src.42 = ine[i32] %src.39: i32, 0i32
         * =>
         * %src.42 = ine[i32] %src.38: i32, %src.7: i32
         */

        /* Iadd */
        case Let(n, Op.Bin(Iadd, ty, lhs, IVal(0))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Iadd, ty, lhs, rhs)) if (lhs == rhs) =>
          Let(n, Op.Bin(Imul, ty, lhs, IVal(2, ty)))

        /* Fadd */
        case Let(n, Op.Bin(Fadd, ty, lhs, FVal(0))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Fadd, ty, lhs, rhs)) if (lhs == rhs) =>
          Let(n, Op.Bin(Fmul, ty, lhs, FVal(2, ty)))

        /* Isub */
        case Let(n, Op.Bin(Isub, ty, lhs, IVal(0))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Isub, ty, lhs, IVal(i))) if (i < 0) =>
          Let(n, Op.Bin(Iadd, ty, lhs, IVal(-i, ty)))

        case Let(n, Op.Bin(Isub, ty, lhs, rhs)) if (lhs == rhs) =>
          copy(n, IVal(0, ty))

        /* Fsub */
        case Let(n, Op.Bin(Fsub, ty, lhs, FVal(0))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Fsub, ty, lhs, FVal(d))) if (d < 0) =>
          Let(n, Op.Bin(Fadd, ty, lhs, FVal(-d, ty)))

        case Let(n, Op.Bin(Fsub, ty, lhs, rhs)) if (lhs == rhs) =>
          copy(n, FVal(0, ty))

        /* Imul */
        case Let(n, Op.Bin(Imul, ty, lhs, IVal(0))) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(Imul, ty, lhs, IVal(1))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Imul, ty, lhs, PowerOf2(shift))) =>
          Let(n, Op.Bin(Shl, ty, lhs, shift))

        /* Fmul */
        case Let(n, Op.Bin(Fmul, ty, lhs, FVal(0))) =>
          copy(n, FVal(0, ty))

        case Let(n, Op.Bin(Fmul, ty, lhs, FVal(1))) =>
          copy(n, lhs)

        /* Sdiv */
        case Let(n, Op.Bin(Sdiv, ty, _, IVal(0))) =>
          copy(n, Val.Undef(ty))

        case Let(n, Op.Bin(Sdiv, ty, lhs, IVal(1))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Sdiv, ty, IVal(0), _)) =>
          copy(n, IVal(0, ty))

        //case Let(n, Op.Bin(Sdiv, ty, lhs, PowerOf2(shift))) =>
          //Let(n, Op.Bin(Ashr, ty, lhs, shift)) // keep the sign

        /* Udiv */
        case Let(n, Op.Bin(Udiv, ty, _, IVal(0))) =>
          copy(n, Val.Undef(ty))

        case Let(n, Op.Bin(Udiv, ty, lhs, IVal(1))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Udiv, ty, IVal(0), _)) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(Udiv, ty, lhs, PowerOf2(shift))) =>
          Let(n, Op.Bin(Lshr, ty, lhs, shift)) // don't keep the sign

        /* Fdiv */
        case Let(n, Op.Bin(Fdiv, ty, _, FVal(0))) =>
          copy(n, Val.Undef(ty))

        case Let(n, Op.Bin(Fdiv, ty, lhs, FVal(1))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Fdiv, ty, FVal(0), _)) =>
          copy(n, FVal(0, ty))

        /* Srem */
        // TODO: mask for PowerOf2 rhs
        case Let(n, Op.Bin(Srem, ty, lhs, IVal(0))) =>
          copy(n, Val.Undef(ty))

        case Let(n, Op.Bin(Srem, ty, lhs, IVal(1))) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(Srem, ty, lhs, IVal(-1))) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(Srem, ty, IVal(0), rhs)) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(Srem, ty, IVal(1), rhs)) =>
          copy(n, IVal(1, ty)) // we know that the rhs is neither +/- 1 nor 0

        case Let(n, Op.Bin(Srem, ty, IVal(-1), rhs)) =>
          copy(n, IVal(1, ty)) // we know that the rhs is neither +/- 1 nor 0

        /* Urem */
        // TODO: mask for PowerOf2 rhs
        case Let(n, Op.Bin(Urem, ty, lhs, IVal(0))) =>
          copy(n, Val.Undef(ty))

        case Let(n, Op.Bin(Urem, ty, lhs, IVal(1))) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(Urem, ty, IVal(0), rhs)) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(Urem, ty, IVal(1), rhs)) =>
          copy(n, IVal(1, ty)) // we know that the rhs is neither 1 nor 0

        /* Frem */
        case Let(n, Op.Bin(Frem, ty, lhs, FVal(0))) =>
          copy(n, Val.Undef(ty))

        case Let(n, Op.Bin(Frem, ty, FVal(0), _)) =>
          copy(n, FVal(0, ty))

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

        //case Let(n, Op.Bin(And, Type.Bool, lhs, Val.True)) =>
        //copy(n, lhs)

        //case Let(n, Op.Bin(And, Type.Bool, lhs, Val.False)) =>
        //copy(n, Val.False)

        /* Or */
        case Let(n, Op.Bin(Or, ty, lhs, rhs)) if (lhs == rhs) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Or, ty, lhs, IVal(0))) =>
          copy(n, lhs)

        case Let(n, Op.Bin(Or, ty, lhs, IVal(-1))) =>
          copy(n, IVal(-1, ty))

        //case Let(n, Op.Bin(Or, Type.Bool, lhs, Val.True)) =>
        //copy(n, Val.True)

        //case Let(n, Op.Bin(Or, Type.Bool, lhs, Val.False)) =>
        //copy(n, lhs)

        /* Xor */
        //case Let(n, Op.Bin(Xor, Type.Bool, lhs, rhs)) if (lhs == rhs) =>
        //copy(n, Val.False)

        case Let(n, Op.Bin(Xor, ty, lhs, rhs)) if (lhs == rhs) =>
          copy(n, IVal(0, ty))

        case Let(n, Op.Bin(Xor, ty, lhs, IVal(0))) =>
          copy(n, lhs)

        //case Let(n, Op.Bin(Xor, Type.Bool, lhs, Val.False)) =>
        //copy(n, lhs)

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

  //object IVal {
  //def unapply(v: Val): Option[Long] = {
  //v match {
  //case Val.I8(b) => Some(b)
  //case Val.I16(s) => Some(s)
  //case Val.I32(i) => Some(i)
  //case Val.I64(l) =>Some(l)

  //case Val.False => Some(0)
  //case Val.True => Some(1)

  //case _ => None
  //}
  //}

  //def apply(value: Long, ty: Type): Val = {
  //ty match {
  //case Type.I8 => Val.I8(value.toByte)
  //case Type.I16 => Val.I16(value.toShort)
  //case Type.I32 => Val.I32(value.toInt)
  //case Type.I64 => Val.I64(value)

  //case Type.Bool if (value == 0) => Val.False
  //case Type.Bool if (value == 1) => Val.True
  //case Type.Bool => throw new IllegalArgumentException(s"Can't cast value $value to Boolean")

  //case _ => throw new IllegalArgumentException(s"Type ${showType(ty)} is not an integer type")
  //}
  //}
  //}

  //object FVal {
  //def unapply(v: Val): Option[Double] = {
  //v match {
  //case Val.F32(f) => Some(f)
  //case Val.F64(d) => Some(d)

  //case _ => None
  //}
  //}

  //def apply(value: Double, ty: Type): Val = {
  //ty match {
  //case Type.F32 => Val.F32(value.toFloat)
  //case Type.F64 => Val.F64(value)

  //case _ => throw new IllegalArgumentException(s"Type ${showType(ty)} is not a floating point type")
  //}
  //}
  //}
}
