package scala.scalanative
package optimizer
package pass

import analysis.ClassHierarchy._
import analysis.ClassHierarchyExtractors._
import analysis.ControlFlow

import nir._
import Shows._

import scala.collection.mutable

class PatternFinder extends Pass {

  private val patternCount = mutable.HashMap.empty[(String, String), Int]
  //private val shownPattern = ("ashr", "and")  // -> selecting some bits from an int
  private val showPattern = Set.empty[(String, String)]

  override def preDefn = {
    case defn: Defn.Define =>
      defn.insts.sliding(2).foreach {
        case Seq(_: Inst.Label, _) =>
        case Seq(_, _: Inst.Label) =>
        case Seq(i1, i2) =>
          val r1 = instRep(i1)
          val r2 = instRep(i2)
          if (showPattern((r1, r2)))
            println(s"${showInst(i1)}\n${showInst(i2)}\n----")
          addPattern(r1, r2)
      }

      //defn.insts.foldLeft(None: Option[Inst]) {
      //case (_, _:Inst.Label) =>
      //None

      //case (None, inst) =>
      //Some(instRep(inst))

      //case (Some(lastRep), inst) =>
      //val rep = instRep(inst)
      //addPattern(lastRep, rep)
      //Some(rep)
      //}

      val methodName = showGlobal(defn.name).toString
      //val lastMethod = "@scala.util.hashing.package$::init"
      val lastMethod = "@tracer.Vector::z_f64"

      if (methodName == lastMethod) {
        println("Reached the end")
        printResults()
      }

      Seq(defn)
  }

  private val ignored = Set("call",
                            "module",
                            "method",
                            "field",
                            "stackalloc",
                            "store",
                            "load",
                            "classalloc",
                            "copy",
                            "ret",
                            "jump")

  private def addPattern(i1: String, i2: String): Unit = {
    if (!ignored(i1) && !ignored(i2)) {
      val pattern      = (i1, i2)
      val currentCount = patternCount.getOrElse(pattern, 0)
      patternCount += (pattern -> (currentCount + 1))
    }
  }

  private def instRep(inst: Inst): String = {
    inst match {
      case Inst.Let(_, op) => extractRep(showOp(op).toString)
      case _               => extractRep(showInst(inst).toString)
    }
  }

  private def extractRep(showRes: String): String =
    showRes.takeWhile(c => (c != ' ') && (c != '['))

  private def printResults() {
    val sortedPatternCount = patternCount.toList.sortBy(_._2)
    sortedPatternCount.reverse.foreach {
      case ((i1, i2), count) =>
        println(s"$i1 -> $i2 [$count]")
    }
  }

}

object PatternFinder extends PassCompanion {
  override def apply(config: tools.Config, top: Top) =
    new PatternFinder
}
