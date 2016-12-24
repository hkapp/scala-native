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

class InstCombine()(implicit fresh: Fresh) extends Pass {
  import InstCombine._
  import ConstantFolding._

  override def preDefn = {
    case defn: Defn.Define =>
      val defop = mutable.HashMap.empty[Local, Op] // only stores def for non-params
      val cfg   = ControlFlow.Graph(defn.insts)

      val resolver = new DefOp(defop)
      //val valDefop: Val => Option[Op] = {
        //case Val.Local(l, _) => defop.get(l)
        //case _               => None
      //}

      // No need to use the dominator tree here, as the cfg is being traversed

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
      // Patterns:
      /* Multiply, then divide */
      // same if tricks with select
      // a = (b * c) + (d * c) => a = (b + d) * c

      case Let(z, Op.Bin(Iadd, ty, y, IVal(a))) =>
        defop(y) match {
          case Some(Op.Bin(Iadd, _, x, IVal(b))) =>
            Let(z, Op.Bin(Iadd, ty, x, IVal(a + b, ty)))

          case Some(Op.Bin(Isub, _, x, IVal(b))) =>
            Let(z, Op.Bin(Iadd, ty, x, IVal(a - b, ty)))

          case _ => inst
        }

      case Let(z, Op.Bin(Fadd, ty, y, FVal(a))) =>
        defop(y) match {
          case Some(Op.Bin(Fadd, _, x, FVal(b))) =>
            Let(z, Op.Bin(Fadd, ty, x, FVal(a + b, ty)))

          case Some(Op.Bin(Fsub, _, x, FVal(b))) =>
            Let(z, Op.Bin(Fadd, ty, x, FVal(a - b, ty)))

          case _ => inst
        }

      case Let(z, Op.Bin(Isub, ty, y, IVal(a))) =>
        defop(y) match {
          case Some(Op.Bin(Isub, _, x, IVal(b))) =>
            Let(z, Op.Bin(Isub, ty, x, IVal(a + b, ty)))

          case Some(Op.Bin(Iadd, _, x, IVal(b))) =>
            Let(z, Op.Bin(Isub, ty, x, IVal(a - b, ty)))

          case _ => inst
        }

      case Let(z, Op.Bin(Fsub, ty, y, FVal(a))) =>
        defop(y) match {
          case Some(Op.Bin(Fsub, _, x, FVal(b))) =>
            Let(z, Op.Bin(Fsub, ty, x, FVal(a + b, ty)))

          case Some(Op.Bin(Fadd, _, x, FVal(b))) =>
            Let(z, Op.Bin(Fsub, ty, x, FVal(a - b, ty)))

          case _ => inst
        }

      case Let(z, Op.Bin(Imul, ty, y, IVal(a))) =>
        defop(y) match {
          case Some(Op.Bin(Imul, _, x, IVal(b))) =>
            Let(z, Op.Bin(Imul, ty, x, IVal(a * b, ty)))

          case Some(Op.Bin(Shl, _, x, IVal(b))) =>
            Let(z, Op.Bin(Imul, ty, x, IVal(a * math.pow(2, b).toLong, ty)))

          case _ => inst
        }

      case Let(z, Op.Bin(Fmul, ty, y, FVal(a))) =>
        defop(y) match {
          case Some(Op.Bin(Fmul, _, x, FVal(b))) =>
            Let(z, Op.Bin(Fmul, ty, x, FVal(a * b, ty)))

          case Some(Op.Bin(Fdiv, _, x, FVal(b))) if (b != 0) =>
            Let(z, Op.Bin(Fmul, ty, x, FVal(a / b, ty)))

          case Some(Op.Bin(Fdiv, _, FVal(b), x)) =>
            Let(z, Op.Bin(Fmul, ty, FVal(a * b, ty), x))

          case _ => inst
        }

      case Let(n, Op.Comp(Ieq, tyIeq, compared, IVal(0))) =>
        defop(compared) match {
          case Some(Op.Bin(Xor, tyXor, lhs, rhs)) if (tyIeq == tyXor) =>
            Let(n, Op.Comp(Ieq, tyIeq, lhs, rhs))

          case _ => inst
        }

      case Let(n, Op.Comp(Ine, tyIne, compared, IVal(0))) =>
        defop(compared) match {
          case Some(Op.Bin(Xor, tyXor, lhs, rhs)) if (tyIne == tyXor) =>
            Let(n, Op.Comp(Ine, tyIne, lhs, rhs))

          case _ => inst
        }

      case Let(n, Op.Select(cond, thenv, elsev)) =>
        defop(cond) match {
          case Some(Op.Bin(Xor, _, negCond, Val.True)) =>
            Let(n, Op.Select(negCond, elsev, thenv))

          case _ => inst
        }

      case If(cond, thenp, elsep) =>
        defop(cond) match {
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

      // (a * b) % a = 0  [i]
      // (a * b) % b = 0  [i]
      case (Some(Op.Bin(Imul, _, a, b)),
            _,
            Op.Bin(Srem, ty, _, c))
          if ((a == c) || (b == c)) =>
        Op.Copy(IVal(0, ty))

      // (a * b) % a = 0  [f]
      // (a * b) % b = 0  [f]
      case (Some(Op.Bin(Fmul, _, a, b)),
            _,
            Op.Bin(Frem, ty, _, c))
          if ((a == c) || (b == c)) =>
        Op.Copy(FVal(0, ty))

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

      //case (Some(Op.Bin(Ashr, _, x, IVal(a))),
            //_,
            //Op.Bin(Sdiv, ty, _, IVal(b))) =>
        //Op.Bin(Sdiv, ty, x, IVal(math.pow(2, a).toLong * b, ty))

      //// (x >>> a) /u b = x /u (2^a * b)
      //case (Some(Op.Bin(Lshr, _, x, IVal(a))),
            //_,
            //Op.Bin(Udiv, ty, _, IVal(b))) =>
        //Op.Bin(Udiv, ty, x, IVal(math.pow(2, a).toLong * b, ty))

      //// (x /u a) >>> b = x /u (2^a * b)
      //case (Some(Op.Bin(Udiv, _, x, IVal(a))),
            //_,
            //Op.Bin(Udiv, ty, _, IVal(b))) =>
        //Op.Bin(Udiv, ty, x, IVal(math.pow(2, a).toLong * b, ty))

      // (a / x) * b = (a * b) / x
      case (Some(Op.Bin(Fdiv, _, FVal(a), x)),
            _,
            Op.Bin(Fmul, ty, _, FVal(b))) =>
        Op.Bin(Fdiv, ty, FVal(a * b, ty), x)

      // a + (0 - b) = a - b
      case (_,
            Some(Op.Bin(Isub, _, IVal(0), b)),
            Op.Bin(Iadd, ty, a, _)) =>
        Op.Bin(Isub, ty, a, b)

      // a - (0 - b) = a + b
      case (_,
            Some(Op.Bin(Isub, _, IVal(0), b)),
            Op.Bin(Isub, ty, a, _)) =>
        Op.Bin(Iadd, ty, a, b)

      // (0 - a) + b = b - a
      case (Some(Op.Bin(Isub, _, IVal(0), a)),
            _,
            Op.Bin(Iadd, ty, _, b)) =>
        Op.Bin(Isub, ty, b, a)

      // (1.0 / a) * b = b / a
      case (Some(Op.Bin(Fdiv, _, FVal(1), a)),
            _,
            Op.Bin(Fmul, ty, _, b)) =>
        Op.Bin(Fdiv, ty, b, a)

      // (a - b) + b = a
      case (Some(Op.Bin(Isub, _, a, b)),
          _,
          Op.Bin(Iadd, _, _, c))
          if (b == c) =>
        Op.Copy(a)

      // (a + b) - b = a
      case (Some(Op.Bin(Iadd, _, a, b)),
          _,
          Op.Bin(Isub, _, _, c))
          if (b == c) =>
        Op.Copy(a)

      // (a / b) * b = a
      case (Some(Op.Bin(Fdiv, _, a, b)),
            _,
            Op.Bin(Fmul, _, _, c))
            if (b == c) =>
        Op.Copy(a)

      // (a * b) / b = a
      case (Some(Op.Bin(Fmul, _, a, b)),
            _,
            Op.Bin(Fdiv, _, _, c))
            if (b == c) =>
        Op.Copy(a)

      // (a / b) * (b / a) = 1.0
      case (Some(Op.Bin(Fdiv, _, a, b)),
            Some(Op.Bin(Fdiv, _, c, d)),
            Op.Bin(Fmul, ty, _, _))
            if ((a == c) && (b == d)) =>
        Op.Copy(FVal(1, ty))

      //// (a * c) + (b * c) = (a + b) * c  [i]
      //case (Some(Op.Bin(Imul, _, a, c)),
            //Some(Op.Bin(Imul, _, b, d)),
            //Op.Bin(Iadd, ty, _, _))
            //if (c == d) =>


      //// (a * b) + (a * c) = a * (b + c)
      //case (Some(Op.Bin(Imul, _, a, c)),
            //Some(Op.Bin(Imul, _, b, d)),
            //Op.Bin(Iadd, ty, _, _))
            //if (c == d) =>


      // (a * b) + (c * a) = a * (b + c)
      // (2^a * b) + (c << a) = (b + c) << a
      // (x * b) + x = x * (b + 1)
      // same with '-'

      // (a + b) % b = a ==> not true ! (negatives doesn't work)
      // a * (x << b) = x * (a * 2^b)  ==> forbidden by canonicalization

      case _ => op
    }
  }

  def simplifyExt(inst: Inst, defop: DefOp)(implicit fresh: Fresh): Seq[Inst] = {
    inst match {
      // (a * c) + (b * c) = (a + b) * c  [i]
      case Let(n, Op.Bin(Iadd, ty,
              defop(Op.Bin(Imul, _, a, c)),
              defop(Op.Bin(Imul, _, b, d))))
            if (c == d) =>
        val tmp = fresh()
        Seq(
          Let(tmp, Op.Bin(Iadd, ty, a, b)),
          Let(n, Op.Bin(Imul, ty, Val.Local(tmp, ty), c)))


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
      value match  {
        case Val.Local(l, _) => defops.get(l)
        case _               => None
      }
    }

  }
}
