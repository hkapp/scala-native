package scala.scalanative
package optimizer
package pass

import analysis.ClassHierarchy._
import analysis.ClassHierarchyExtractors._
import nir._, Inst.Let

/** Moves constant operands in Op.Bin and Op.Comp to the right. */
class Canonicalization extends Pass {

  override def preInst = {
    case Let(n, Op.Bin(bin, ty, lhs, rhs))
        if (commutativeBin(bin) && constant(lhs)) =>
      Seq(Let(n, Op.Bin(bin, ty, rhs, lhs)))

    case Let(n, Op.Comp(comp, ty, lhs, rhs))
        if (commutativeComp(comp) && constant(lhs)) =>
      Seq(Let(n, Op.Comp(comp, ty, rhs, lhs)))
  }

  private def commutativeBin(bin: Bin): Boolean = {
    import Bin._
    bin match {
      case Iadd | Fadd | Imul | Fmul | And | Or | Xor => true
      case Isub | Fsub | Sdiv | Udiv | Fdiv | Srem | Urem | Frem | Shl | Lshr |
          Ashr =>
        false
    }
  }

  private def commutativeComp(comp: Comp): Boolean = {
    import Comp._
    // we could handle the '>' by reverting them (same holds for other Comps)
    comp match {
      case Ieq | Ine | Feq | Fne => true
      case _                     => false
    }
  }

  private def constant(value: Val): Boolean = {
    import Val._
    // TODO rewrite this
    value match {
      case _: Struct | _: Array | _: Local | _: Global | _: Const => false
      case _                                                      => true
    }
  }

}

object Canonicalization extends PassCompanion {
  override def apply(config: tools.Config, top: Top) =
    new Canonicalization
}
