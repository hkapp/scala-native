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
import Conv._

import scala.None
import scala.collection.mutable

class ConstantFolding extends Pass {
  import ConstantFolding._

  override def preInst = {
    case inst: Inst =>
      val newInst = inst match {
        // TODO: take care of overflows
        case Let(n, op) =>
          val newVal = op match {

            /*  BIN  */

            case Op.Bin(Iadd, ty, IVal(a), IVal(b)) =>
              IVal(a + b, ty)

            case Op.Bin(Fadd, _, Val.F32(a), Val.F32(b)) =>
              Val.F32(a + b)
            case Op.Bin(Fadd, _, Val.F64(a), Val.F64(b)) =>
              Val.F64(a + b)

            case Op.Bin(Isub, ty, IVal(a), IVal(b)) =>
              IVal(a - b, ty)

            case Op.Bin(Fsub, _, Val.F32(a), Val.F32(b)) =>
              Val.F32(a - b)
            case Op.Bin(Fsub, _, Val.F64(a), Val.F64(b)) =>
              Val.F64(a - b)

            case Op.Bin(Imul, ty, IVal(a), IVal(b)) =>
              IVal(a * b, ty)

            case Op.Bin(Fmul, _, Val.F32(a), Val.F32(b)) =>
              Val.F32(a * b)
            case Op.Bin(Fmul, _, Val.F64(a), Val.F64(b)) =>
              Val.F64(a * b)

            case Op.Bin(Sdiv, ty, _, IVal(0)) =>
              Val.Undef(ty)
            case Op.Bin(Sdiv, ty, IVal(a), IVal(b)) =>
              IVal(a / b, ty)

            case Op.Bin(Udiv, ty, _, IVal(0)) =>
              Val.Undef(ty)
            case Op.Bin(Udiv, _, Val.I8(a), Val.I8(b)) =>
              Val.I8(Unsigned.Div(a, b))
            case Op.Bin(Udiv, _, Val.I16(a), Val.I16(b)) =>
              Val.I16(Unsigned.Div(a, b))
            case Op.Bin(Udiv, _, Val.I32(a), Val.I32(b)) =>
              Val.I32(Unsigned.Div(a, b))
            case Op.Bin(Udiv, _, Val.I64(a), Val.I64(b)) =>
              Val.I64(Unsigned.Div(a, b))

            //case Op.Bin(Udiv, _, Val.I8(a), Val.I8(b)) =>
            //val ua = java.lang.Byte.toUnsignedInt(a)
            //val ub = java.lang.Byte.toUnsignedInt(b)
            //val ures = (ua / ub).toByte
            //Val.I8(ures)
            //case Op.Bin(Udiv, _, Val.I16(a), Val.I16(b)) =>
            //val ua = java.lang.Short.toUnsignedInt(a)
            //val ub = java.lang.Short.toUnsignedInt(b)
            //val ures = (ua / ub).toShort
            //Val.I16(ures)
            //case Op.Bin(Udiv, _, Val.I32(a), Val.I32(b)) =>
            //Val.I32(java.lang.Integer.divideUnsigned(a, b))
            //case Op.Bin(Udiv, _, Val.I64(a), Val.I64(b)) =>
            //Val.I64(java.lang.Long.divideUnsigned(a, b))

            case Op.Bin(Fdiv, ty, _, FVal(0)) =>
              Val.Undef(ty)
            case Op.Bin(Fdiv, _, Val.F32(a), Val.F32(b)) =>
              Val.F32(a / b)
            case Op.Bin(Fdiv, _, Val.F64(a), Val.F64(b)) =>
              Val.F64(a / b)

            case Op.Bin(Srem, ty, _, IVal(0)) =>
              Val.Undef(ty)
            case Op.Bin(Srem, ty, IVal(a), IVal(b)) =>
              IVal(a % b, ty)

            case Op.Bin(Urem, ty, _, IVal(0)) =>
              Val.Undef(ty)
            case Op.Bin(Urem, _, Val.I8(a), Val.I8(b)) =>
              Val.I8(Unsigned.Rem(a, b))
            case Op.Bin(Urem, _, Val.I16(a), Val.I16(b)) =>
              Val.I16(Unsigned.Rem(a, b))
            case Op.Bin(Urem, _, Val.I32(a), Val.I32(b)) =>
              Val.I32(Unsigned.Rem(a, b))
            case Op.Bin(Urem, _, Val.I64(a), Val.I64(b)) =>
              Val.I64(Unsigned.Rem(a, b))

            //case Op.Bin(Urem, _, Val.I8(a), Val.I8(b)) =>
            //val ua = java.lang.Byte.toUnsignedInt(a)
            //val ub = java.lang.Byte.toUnsignedInt(b)
            //val ures = (ua % ub).toByte
            //Val.I8(ures)
            //case Op.Bin(Urem, _, Val.I16(a), Val.I16(b)) =>
            //val ua = java.lang.Short.toUnsignedInt(a)
            //val ub = java.lang.Short.toUnsignedInt(b)
            //val ures = (ua % ub).toShort
            //Val.I16(ures)
            //case Op.Bin(Urem, _, Val.I32(a), Val.I32(b)) =>
            //Val.I32(java.lang.Integer.remainderUnsigned(a, b))
            //case Op.Bin(Urem, _, Val.I64(a), Val.I64(b)) =>
            //Val.I64(java.lang.Long.remainderUnsigned(a, b))

            case Op.Bin(Frem, ty, _, FVal(0)) =>
              Val.Undef(ty)
            case Op.Bin(Frem, _, Val.F32(a), Val.F32(b)) =>
              Val.F32(a % b)
            case Op.Bin(Frem, _, Val.F64(a), Val.F64(b)) =>
              Val.F64(a % b)

            case Op.Bin(Shl, ty, IVal(a), IVal(b)) =>
              IVal(a << b, ty)

            case Op.Bin(Lshr, ty, IVal(a), IVal(b)) =>
              IVal(a >>> b, ty)

            case Op.Bin(Ashr, ty, IVal(a), IVal(b)) =>
              IVal(a >> b, ty)

            case Op.Bin(And, ty, IVal(a), IVal(b)) =>
              IVal(a & b, ty)

            case Op.Bin(Or, ty, IVal(a), IVal(b)) =>
              IVal(a | b, ty)

            case Op.Bin(Xor, ty, IVal(a), IVal(b)) =>
              IVal(a ^ b, ty)

            /*  COMP  */

            case Op.Comp(Ieq, ty, IVal(a), IVal(b)) =>
              Val.Bool(a == b)
            case Op.Comp(Ine, ty, IVal(a), IVal(b)) =>
              Val.Bool(a != b)

            case Op.Comp(Ugt, ty, IVal(a), IVal(b)) =>
              Val.Bool(java.lang.Long.compareUnsigned(a, b) > 0)
            case Op.Comp(Uge, ty, IVal(a), IVal(b)) =>
              Val.Bool(java.lang.Long.compareUnsigned(a, b) >= 0)
            case Op.Comp(Ult, ty, IVal(a), IVal(b)) =>
              Val.Bool(java.lang.Long.compareUnsigned(a, b) < 0)
            case Op.Comp(Ule, ty, IVal(a), IVal(b)) =>
              Val.Bool(java.lang.Long.compareUnsigned(a, b) <= 0)

            case Op.Comp(Sgt, ty, IVal(a), IVal(b)) =>
              Val.Bool(a > b)
            case Op.Comp(Sge, ty, IVal(a), IVal(b)) =>
              Val.Bool(a >= b)
            case Op.Comp(Slt, ty, IVal(a), IVal(b)) =>
              Val.Bool(a < b)
            case Op.Comp(Sle, ty, IVal(a), IVal(b)) =>
              Val.Bool(a <= b)

            case Op.Comp(Feq, ty, Val.F32(a), Val.F32(b)) =>
              Val.Bool(a == b)
            case Op.Comp(Feq, ty, Val.F64(a), Val.F64(b)) =>
              Val.Bool(a == b)

            case Op.Comp(Fne, ty, Val.F32(a), Val.F32(b)) =>
              Val.Bool(a != b)
            case Op.Comp(Fne, ty, Val.F64(a), Val.F64(b)) =>
              Val.Bool(a != b)

            case Op.Comp(Fgt, ty, Val.F32(a), Val.F32(b)) =>
              Val.Bool(a > b)
            case Op.Comp(Fgt, ty, Val.F64(a), Val.F64(b)) =>
              Val.Bool(a > b)

            case Op.Comp(Fge, ty, Val.F32(a), Val.F32(b)) =>
              Val.Bool(a >= b)
            case Op.Comp(Fge, ty, Val.F64(a), Val.F64(b)) =>
              Val.Bool(a >= b)

            case Op.Comp(Flt, ty, Val.F32(a), Val.F32(b)) =>
              Val.Bool(a < b)
            case Op.Comp(Flt, ty, Val.F64(a), Val.F64(b)) =>
              Val.Bool(a < b)

            case Op.Comp(Fle, ty, Val.F32(a), Val.F32(b)) =>
              Val.Bool(a <= b)
            case Op.Comp(Fle, ty, Val.F64(a), Val.F64(b)) =>
              Val.Bool(a <= b)

            /*  CONV  */
            case Op.Conv(Trunc, ty, IVal(i)) =>
              IVal(i, ty)

            case Op.Conv(Zext, ty, Val.I8(b)) =>
              IVal(java.lang.Byte.toUnsignedLong(b), ty)
            case Op.Conv(Zext, ty, Val.I16(s)) =>
              IVal(java.lang.Short.toUnsignedLong(s), ty)
            case Op.Conv(Zext, ty, Val.I32(i)) =>
              IVal(java.lang.Integer.toUnsignedLong(i), ty)
            case Op.Conv(Zext, ty, Val.I64(l)) =>
              IVal(l, ty)

            case Op.Conv(Sext, ty, IVal(i)) =>
              IVal(i, ty)

            case Op.Conv(Fptrunc, Type.F32, Val.F64(d)) =>
              Val.F32(d.toFloat)

            case Op.Conv(Fpext, Type.F64, Val.I32(f)) =>
              Val.F64(f.toDouble)

            case Op.Conv(Fptoui, ty, FVal(d)) if (d >= 0) =>
              IVal(math.floor(d).toLong, ty)

            case Op.Conv(Fptosi, ty, FVal(d)) if (d >= 0) =>
              IVal(math.floor(d).toLong, ty)
            case Op.Conv(Fptosi, ty, FVal(d)) if (d < 0) =>
              IVal(math.ceil(d).toLong, ty)

            // TODO: Uitofp

            case Op.Conv(Sitofp, ty, IVal(a)) =>
              FVal(a.toDouble, ty)

            /* Select */
            case Op.Select(Val.True, thenv, _) =>
              thenv
            case Op.Select(Val.False, _, elsev) =>
              elsev

            case _ => Val.None
          }

          newVal match {
            case Val.None => inst
            case _        => Let(n, Op.Copy(newVal))
          }

        case _ => inst
      }
      Seq(newInst)
  }

}

object ConstantFolding extends PassCompanion {
  override def apply(config: tools.Config, top: Top) =
    new ConstantFolding

  object IVal {
    def unapply(v: Val): Option[Long] = {
      v match {
        case Val.I8(b)  => Some(b)
        case Val.I16(s) => Some(s)
        case Val.I32(i) => Some(i)
        case Val.I64(l) => Some(l)

        case Val.False => Some(0)
        case Val.True  => Some(-1)

        case _ => None
      }
    }

    def apply(value: Long, ty: Type): Val = {
      ty match {
        case Type.I8  => Val.I8(value.toByte)
        case Type.I16 => Val.I16(value.toShort)
        case Type.I32 => Val.I32(value.toInt)
        case Type.I64 => Val.I64(value)

        case Type.Bool if (value == 0)  => Val.False
        case Type.Bool if (value == -1) => Val.True
        case Type.Bool =>
          throw new IllegalArgumentException(
            s"Can't cast value $value to Boolean")

        case _ =>
          throw new IllegalArgumentException(
            s"Type ${showType(ty)} is not an integer type")
      }
    }
  }

  object FVal {
    def unapply(v: Val): Option[Double] = {
      v match {
        case Val.F32(f) => Some(f)
        case Val.F64(d) => Some(d)

        case _ => None
      }
    }

    def apply(value: Double, ty: Type): Val = {
      ty match {
        case Type.F32 => Val.F32(value.toFloat)
        case Type.F64 => Val.F64(value)

        case _ =>
          throw new IllegalArgumentException(
            s"Type ${showType(ty)} is not a floating point type")
      }
    }
  }

  class UnsignedOp(baseOp: (Long, Long) => Long) {

    def apply(a: Byte, b: Byte): Byte = {
      val ua = java.lang.Byte.toUnsignedLong(a)
      val ub = java.lang.Byte.toUnsignedLong(b)
      baseOp(ua, ub).toByte
    }

    def apply(a: Short, b: Short): Short = {
      val ua = java.lang.Short.toUnsignedLong(a)
      val ub = java.lang.Short.toUnsignedLong(b)
      baseOp(ua, ub).toShort
    }

    def apply(a: Int, b: Int): Int = {
      val ua = java.lang.Integer.toUnsignedLong(a)
      val ub = java.lang.Integer.toUnsignedLong(b)
      baseOp(ua, ub).toInt
    }

    def apply(a: Long, b: Long): Long = {
      baseOp(a, b)
    }
  }

  object Unsigned {

    val Div = new UnsignedOp((a, b) => java.lang.Long.divideUnsigned(a, b))
    val Rem = new UnsignedOp((a, b) => java.lang.Long.remainderUnsigned(a, b))

  }
}
