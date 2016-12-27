package scala.scalanative
package optimizer
package pass

import analysis.ClassHierarchy.Top
import analysis.ControlFlow

import nir._
import Inst._
import Bin._
import Comp._

import scala.None
import scala.collection.mutable

class InstCombine()(implicit fresh: Fresh) extends Pass {
  import InstCombine._
  import ConstantFolding._

  override def preDefn = {
    case defn: Defn.Define =>
      // This stores the encountered definitions for non-params locals
      val defop    = mutable.HashMap.empty[Local, Op]
      val resolver = new DefOp(defop)
      val cfg      = ControlFlow.Graph(defn.insts)

      /* Because of the pre-order traversal of the CFG, the definitions will be
       * seen before their use
       */
      val newInsts = cfg.map { b =>
        b.label +: b.insts.flatMap { inst =>
          val simplifiedSeq = simplify(inst, resolver)
          simplifiedSeq.foreach {
            case Let(n, op) => defop += (n -> op)
            case _          =>
          }
          simplifiedSeq
        }
      }.flatten

      Seq(defn.copy(insts = newInsts))
  }

  private def simplify(inst: Inst, defop: DefOp): Seq[Inst] = {
    val singleSimp = inst match {

      case Let(z, Op.Bin(Iadd, ty, y, IVal(a))) =>
        defop(y) match {
          // (x + b) + a = x + (a + b)
          case Some(Op.Bin(Iadd, _, x, IVal(b))) =>
            Let(z, Op.Bin(Iadd, ty, x, IVal(a + b, ty)))

          // (x - b) + a = x + (a - b)
          case Some(Op.Bin(Isub, _, x, IVal(b))) =>
            Let(z, Op.Bin(Iadd, ty, x, IVal(a - b, ty)))

          case _ => inst
        }

      case Let(z, Op.Bin(Isub, ty, y, IVal(a))) =>
        defop(y) match {
          // (x - b) - a = x - (a + b)
          case Some(Op.Bin(Isub, _, x, IVal(b))) =>
            Let(z, Op.Bin(Isub, ty, x, IVal(a + b, ty)))

          // (x + b) - a = x - (a - b)
          case Some(Op.Bin(Iadd, _, x, IVal(b))) =>
            Let(z, Op.Bin(Isub, ty, x, IVal(a - b, ty)))

          case _ => inst
        }

      case Let(z, Op.Bin(Imul, ty, y, IVal(a))) =>
        defop(y) match {
          // (x * b) * a = x * (a * b)
          case Some(Op.Bin(Imul, _, x, IVal(b))) =>
            Let(z, Op.Bin(Imul, ty, x, IVal(a * b, ty)))

          // (x << b) * a = x * (a * 2^b)
          case Some(Op.Bin(Shl, _, x, IVal(b))) =>
            Let(z, Op.Bin(Imul, ty, x, IVal(a * math.pow(2, b).toLong, ty)))

          case _ => inst
        }

      case Let(n, Op.Comp(Ieq, tyIeq, compared, IVal(0))) =>
        defop(compared) match {
          // ((lhs xor rhs) == 0) = (lhs == rhs)
          case Some(Op.Bin(Xor, tyXor, lhs, rhs)) if (tyIeq == tyXor) =>
            Let(n, Op.Comp(Ieq, tyIeq, lhs, rhs))

          case _ => inst
        }

      case Let(n, Op.Comp(Ine, tyIne, compared, IVal(0))) =>
        defop(compared) match {
          // ((lhs xor rhs) != 0) = (lhs != rhs)
          case Some(Op.Bin(Xor, tyXor, lhs, rhs)) if (tyIne == tyXor) =>
            Let(n, Op.Comp(Ine, tyIne, lhs, rhs))

          case _ => inst
        }

      case Let(n, Op.Select(cond, thenv, elsev)) =>
        defop(cond) match {
          // select (c xor true) then a else b  =  select c then b else a
          case Some(Op.Bin(Xor, _, negCond, Val.True)) =>
            Let(n, Op.Select(negCond, elsev, thenv))

          case _ => inst
        }

      case If(cond, thenp, elsep) =>
        defop(cond) match {
          // if (c xor true) then a else b  =  if c then b else a
          case Some(Op.Bin(Xor, _, negCond, Val.True)) =>
            If(negCond, elsep, thenp)

          case _ => inst
        }

      case Let(n, op @ Op.Bin(_, _, lhs, rhs)) =>
        Let(n, simplifyBin(defop(lhs), defop(rhs), op))

      // Nothing
      case _ => inst
    }

    simplifyExt(singleSimp, defop)
  }

  def simplifyBin(lhsDef: Option[Op], rhsDef: Option[Op], op: Op.Bin): Op = {
    (lhsDef, rhsDef, op) match {

      // (a * b) % a = 0
      // (a * b) % b = 0
      case (Some(Op.Bin(Imul, _, a, b)),
            _,
            Op.Bin(Srem, ty, _, c))
          if ((a == c) || (b == c)) =>
        Op.Copy(IVal(0, ty))

      // (x << a) * b = x * (2^a * b)
      case (Some(Op.Bin(Shl, _, x, IVal(a))),
            _,
            Op.Bin(Imul, ty, _, IVal(b))) =>
        Op.Bin(Imul, ty, x, IVal(math.pow(2, a).toLong * b, ty))

      // (x * a) << b = x * (a * 2^b)
      case (Some(Op.Bin(Imul, _, x, IVal(a))),
            _,
            Op.Bin(Shl, ty, _, IVal(b))) =>
        Op.Bin(Imul, ty, x, IVal(a * math.pow(2, b).toLong, ty))

      // a + (0 - b) = a - b
      case (_, Some(Op.Bin(Isub, _, IVal(0), b)), Op.Bin(Iadd, ty, a, _)) =>
        Op.Bin(Isub, ty, a, b)

      // a - (0 - b) = a + b
      case (_, Some(Op.Bin(Isub, _, IVal(0), b)), Op.Bin(Isub, ty, a, _)) =>
        Op.Bin(Iadd, ty, a, b)

      // (0 - a) + b = b - a
      case (Some(Op.Bin(Isub, _, IVal(0), a)), _, Op.Bin(Iadd, ty, _, b)) =>
        Op.Bin(Isub, ty, b, a)

      // (a - b) + b = a
      case (Some(Op.Bin(Isub, _, a, b)), _, Op.Bin(Iadd, _, _, c))
          if (b == c) =>
        Op.Copy(a)

      // (a + b) - b = a
      case (Some(Op.Bin(Iadd, _, a, b)), _, Op.Bin(Isub, _, _, c))
          if (b == c) =>
        Op.Copy(a)

      case _ => op
    }
  }

  def simplifyExt(inst: Inst, defop: DefOp)(implicit fresh: Fresh): Seq[Inst] = {
    inst match {
      // (a * c) + (b * c) = (a + b) * c
      case Let(n,
               Op.Bin(Iadd,
                      ty,
                      defop(Op.Bin(Imul, _, a, c)),
                      defop(Op.Bin(Imul, _, b, d)))) if (c == d) =>
        val tmp = fresh()
        Seq(Let(tmp, Op.Bin(Iadd, ty, a, b)),
            Let(n, Op.Bin(Imul, ty, Val.Local(tmp, ty), c)))

      // unbox (box a) = a
      case Let(n, Op.Unbox(_, defop(Op.Box(_, a)))) =>
        Seq(Let(n, Op.Copy(a)))

      // box (unbox b) = b
      case Let(n, Op.Box(_, defop(Op.Unbox(_, b)))) =>
        Seq(Let(n, Op.Copy(b)))

      case _ => Seq(inst)
    }
  }

  def copy(n: Local, value: Val): Inst =
    Let(n, Op.Copy(value))

}

object InstCombine extends PassCompanion {
  override def apply(config: tools.Config, top: Top) =
    new InstCombine()(top.fresh)

  class DefOp(val defops: mutable.HashMap[Local, Op]) {

    def apply(value: Val): Option[Op] = {
      unapply(value)
    }

    def unapply(value: Val): Option[Op] = {
      value match {
        case Val.Local(l, _) => defops.get(l)
        case _               => None
      }
    }

  }
}
