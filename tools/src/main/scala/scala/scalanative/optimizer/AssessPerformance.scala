package scala.scalanative
package optimizer

import nir._
import Shows._

object AssessPerformance {

  def apply(assembly: Seq[Defn]): Unit = {

    val config = tools.Config.empty.withInjectMain(false)
    val driver =
      Driver(config)
        .takeUpTo(pass.GlobalValueNumbering)
        .append(pass.CopyPropagation)
        .append(pass.DeadCodeElimination)
    val reporter = Reporter.empty

    println("Starting optimization ...")
    val optimizedCode = Optimizer(config, driver, assembly, reporter)

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

    println(assembly.groupBy(_.getClass.getName.toString).map {case (k,v) => (k, v.size)})
    println(assembly.groupBy(_.getClass.getName.toString).map {case (k,v) => (k, v.map(defn => showDefn(defn).toString.count(_ == '\n')).sum)})

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
        code.map(defnSize).sum

      def defnSize(defn: Defn): Int =
        showDefn(defn).toString.count(_ == '\n')
    }

    object Optimizeable extends StaticMetric {
      override def measure(code: Seq[Defn]): Int =
        code.map(optimizeableLinesIn).sum

      def optimizeableLinesIn(defn: Defn): Int = {
        defn match {
          case Defn.Define(_, _, _, insts) => insts.size - 2 // at least one Cf and one Label
          case _ => 0
        }
      }
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

    object OutOfTouched extends StaticMetric {
      override def measure(code: Seq[Defn]): Int =
        Raw.measure(methods(code))
    }
  }

  def methods(defns: Seq[Defn]): Seq[Defn] =
    defns.collect { case m: Defn.Define => m }

}
