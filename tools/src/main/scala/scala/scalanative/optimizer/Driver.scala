package scala.scalanative
package optimizer

sealed trait Driver {

  /** Companion of all the passes in the driver's pipeline. */
  def passes: Seq[PassCompanion]

  /** Take all passes including the given one. */
  def takeUpTo(pass: PassCompanion): Driver

  /** Take all passes including the given one. */
  def takeBefore(pass: PassCompanion): Driver

  /** Append a pass to the pipeline. */
  def append(pass: PassCompanion): Driver
}

object Driver {

  /** Create driver with default pipeline for this configuration. */
  def apply(config: tools.Config): Driver =
    new Impl(
      Seq(
        //pass.UnitSimplification,
        //pass.DeadCodeElimination,
        //pass.CfChainsSimplification,
        //pass.DeadCodeElimination,
        //pass.BasicBlocksFusion,
        //pass.CopyPropagation,
        //pass.BlockParamReduction,
        //pass.CopyPropagation,
        //pass.Canonicalization,
        //pass.ConstantFolding,
        //pass.CopyPropagation,
        //pass.PartialEvaluation,
        //pass.CopyPropagation,
        //pass.InstCombine,
        //pass.CopyPropagation,
        //pass.DeadCodeElimination,
        //pass.GlobalBoxingElimination,
        //pass.CopyPropagation,
        //pass.DeadCodeElimination,
        //pass.GlobalValueNumbering,
        pass.UnitSimplification,
        pass.DeadCodeElimination,
        pass.CfChainsSimplification,
        pass.BasicBlocksFusion,
        pass.BlockParamReduction,
        pass.CopyPropagation,
        pass.Canonicalization,
        pass.ConstantFolding,
        pass.PartialEvaluation,
        pass.InstCombine,
        pass.GlobalBoxingElimination,
        pass.GlobalValueNumbering,
        pass.MainInjection,
        pass.ExternHoisting,
        pass.ModuleLowering,
        pass.RuntimeTypeInfoInjection,
        pass.BoxingLowering,
        pass.AsLowering,
        pass.IsLowering,
        pass.MethodLowering,
        pass.TraitLowering,
        pass.ClassLowering,
        pass.StringLowering,
        pass.ConstLowering,
        pass.UnitLowering,
        pass.ThrowLowering,
        pass.NothingLowering,
        pass.TryLowering,
        pass.AllocLowering,
        pass.SizeofLowering,
        //pass.CopyPropagation,
        //pass.DeadCodeElimination,
        //pass.UnitSimplification,
        //pass.DeadCodeElimination,
        //pass.CfChainsSimplification,
        //pass.DeadCodeElimination,
        //pass.BasicBlocksFusion,
        //pass.CopyPropagation,
        //pass.BlockParamReduction,
        //pass.CopyPropagation,
        //pass.Canonicalization,
        //pass.ConstantFolding,
        //pass.CopyPropagation,
        //pass.PartialEvaluation,
        //pass.CopyPropagation,
        //pass.InstCombine,
        //pass.CopyPropagation,
        //pass.DeadCodeElimination,
        //pass.GlobalBoxingElimination,
        //pass.CopyPropagation,
        //pass.DeadCodeElimination,
        //pass.GlobalValueNumbering,
        pass.CopyPropagation,
        pass.DeadCodeElimination
      ))

  /** Create an empty pass-lesss driver. */
  def empty: Driver =
    new Impl(Seq.empty)

  private final class Impl(val passes: Seq[PassCompanion]) extends Driver {
    def takeUpTo(pass: PassCompanion): Driver = {
      val (before, after) = passes.span(_ != pass)
      new Impl(before :+ after.head)
    }

    def takeBefore(pass: PassCompanion): Driver = ???

    def append(pass: PassCompanion): Driver =
      new Impl(passes :+ pass)
  }
}
