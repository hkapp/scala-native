package scala.scalanative
package optimizer

import nir._
import Shows._

object AssessPerformance {

  val config = tools.Config.empty.withInjectMain(false)

  def apply(assembly: Seq[Defn]): Unit = {
    println("Original code size : "+codeSize(assembly))

    val basicDriver =
      Driver.empty
        .append(pass.GlobalBoxingElimination)
        .append(pass.CopyPropagation)
        .append(pass.DeadCodeElimination)

    val simplifiedCode = runOptimizer(assembly, basicDriver)

    println("Simplified code size : "+codeSize(simplifiedCode))
    reportSeparate(simplifiedCode)
  }

  def reportSeparate(assembly: Seq[Defn]): Unit = {
    val addedPasses = Seq(
      pass.GlobalBoxingElimination,
      pass.CopyPropagation,
      pass.DeadCodeElimination,
      pass.UnitSimplification,
      pass.CfChainsSimplification,
      pass.BasicBlocksFusion,
      pass.BlockParamReduction,
      pass.Canonicalization,
      pass.ConstantFolding,
      pass.PartialEvaluation,
      pass.InstCombine,  // TODO : special treatment, reorder code as in CFG (could add it above)
      pass.GlobalValueNumbering
    )

    for (newPass <- addedPasses) {
      val driver =
        Driver.empty
          .append(newPass)
          .append(pass.CopyPropagation)
          .append(pass.DeadCodeElimination)

      println(" > " +
        newPass
          .getClass
          .getName
          .split('.')
          .last
          .replace("$","")
        + " < ")

      report(assembly, driver)
    }
  }

  def reportGlobal(assembly: Seq[Defn]): Unit = {
    val driver =
      Driver(config)
        .takeUpTo(pass.GlobalValueNumbering)
        .append(pass.CopyPropagation)
        .append(pass.DeadCodeElimination)

    report(assembly, driver)
  }

  def report(assembly: Seq[Defn], driver: Driver): Unit = {
    val optimizedCode = runOptimizer(assembly, driver)

    val metrics = Seq(
      Metrics.Raw,
      Metrics.Optimizeable,
      Metrics.Touched,
      Metrics.MethodsTouched,
      Metrics.OutOfTouched
    )

    for (metric <- metrics) {
      metric.reportOn(assembly, optimizedCode)
    }
  }

  def runOptimizer(assembly: Seq[Defn], driver: Driver): Seq[Defn] = {
    val reporter = Reporter.empty

    println("Starting optimization ...")
    val optimizedCode = Optimizer(config, driver, assembly, reporter)
    optimizedCode
  }

  trait Metric {

    def reportOn(originalCode: Seq[Defn], optimizedCode: Seq[Defn]): Unit

  }

  trait StaticMetric extends Metric {

    def measure(code: Seq[Defn]): Int

    def performance(oldM: Int, newM: Int): Double =
      1 - (newM.toDouble / oldM)

    def name: String = this.getClass.getName.toString.split('$').filterNot(_.isEmpty).last

    override def reportOn(originalCode: Seq[Defn], optimizedCode: Seq[Defn]): Unit = {
      val oldM = measure(originalCode)
      val newM = measure(optimizedCode)
      val perf = performance(oldM, newM)

      println(s"== $name ==")
      println(s"Original: $oldM")
      println(s"Optimized: $newM")
      println(s"Performance: ${perf * 100} %")
    }

  }

  object Metrics {

    object Raw extends StaticMetric {
      override def measure(code: Seq[Defn]): Int =
        codeSize(code)
        //code.map(defnSize).sum

      //def defnSize(defn: Defn): Int =
        //lineCount(showDefn(defn).toString)
    }

    object Optimizeable extends StaticMetric {
      override def measure(code: Seq[Defn]): Int = {
          val methodDefs = methods(code)
          codeSize(methodDefs) - 4 * methodDefs.size
        }
        //code.map(optimizeableLinesIn).sum

      //def optimizeableLinesIn(defn: Defn): Int = {
        //defn match {
          //case m: Defn.Define => insts.size - 2 // at least one Cf and one Label
          //case _ => 0
        //}
      //}
    }

    object Touched extends Metric {
      override def reportOn(originalCode: Seq[Defn], optimizedCode: Seq[Defn]): Unit = {
        assert(originalCode.size == optimizedCode.size)
        val touched = originalCode.zip(optimizedCode).count {
          case (origDef, optiDef) => (origDef != optiDef)
        }
        val total = originalCode.size

        val perf = touched.toDouble / total

        println("== Touched ==")
        println(s"Globals touched: $touched (out of $total)")
        println(s"Performance: ${perf * 100} %")
      }
    }

    object MethodsTouched extends Metric {
      override def reportOn(originalCode: Seq[Defn], optimizedCode: Seq[Defn]): Unit = {
        val origMethods = methods(originalCode)
        val optiMethods = methods(optimizedCode)
        assert(origMethods.size == optiMethods.size)
        val touched = origMethods.zip(optiMethods).count {
          case (origDef, optiDef) => (origDef != optiDef)
        }
        val total = origMethods.size

        val perf = touched.toDouble / total

        println("== MethodsTouched ==")
        println(s"Methods touched: $touched (out of $total)")
        println(s"Performance: ${perf * 100} %")
      }
    }

    object OutOfTouched extends Metric {
      override def reportOn(originalCode: Seq[Defn], optimizedCode: Seq[Defn]): Unit = {
        assert(originalCode.size == optimizedCode.size)
        val (origTouched, optiTouched) = originalCode.zip(optimizedCode).filter {
          case (origDef, optiDef) => (origDef != optiDef)
        }.unzip
        val touched = origTouched.size

        //val rawPerf = Raw.performance(Raw.measure(origTouched))

        println("== OutOfTouched ==")
        print("  ")
        Raw.reportOn(origTouched, optiTouched)
        print("  ")
        Optimizeable.reportOn(origTouched, optiTouched)
        //println(s"Methods touched: $touched (out of $total)")
        //println(s"Performance: ${perf * 100} %")
      }
    }
  }

  def methods(defns: Seq[Defn]): Seq[Defn] =
    defns.collect { case m: Defn.Define => m }

  def lineCount(str: String): Int =
    str.count(_ == '\n') + 1

  def codeSize(code: Seq[Defn]): Int =
    code.map(defn => lineCount(showDefn(defn).toString)).sum
}
