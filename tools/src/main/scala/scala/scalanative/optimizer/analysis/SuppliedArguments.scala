package scala.scalanative
package optimizer
package analysis

import ControlFlow.Block
import nir.{Local, Val, Next}
import scala.collection.mutable

class SuppliedArguments(val cfg: ControlFlow.Graph, val forBlock: Map[Local, Seq[Set[Val]]]) {

  lazy val paramValues: Map[Local, Seq[Option[Val]]] = {
    cfg.all.map { b =>
      if (b.name == cfg.entry.name)
        (b.name -> Seq.fill(b.params.size)(None))
      else
        (b.name -> reduceParams(b))
    }.toMap
  }

  private def reduceParams(block: Block): Seq[Option[Val]] = {
    forBlock.get(block.name) match {
      case Some(args) =>
        block.params.zip(args).map {
          case (param, argValues) =>
            val noRecArgs = argValues - param
            if (noRecArgs.size == 1)
              Some(noRecArgs.head)
            else
              None
        }

      // handles block that are unreachable, or reachable only through non-Next.Label nexts (like Success or Case)
      case None => Seq.fill(block.params.size)(None)
    }
  }
}

object SuppliedArguments {

  def build(cfg: ControlFlow.Graph): SuppliedArguments = {
    val argGatherer = new ArgGatherer
    cfg.all.foreach(b => argGatherer(b.insts.last))
    new SuppliedArguments(cfg, argGatherer.result)
  }


  class ArgGatherer extends Pass {

    private val res = mutable.HashMap.empty[Local, Seq[Set[Val]]]

    def result = res.toMap

    override def preNext = {
      case next @ Next.Label(name, args) =>
        addArgs(name, args)
        next
    }

    private def addArgs(name: Local, args: Seq[Val]): Unit = {
      val suppliedArgs: Seq[Set[Val]] = res.getOrElse(name, Seq.fill(args.size)(Set.empty[Val]))
      assert(suppliedArgs.size == args.size)
      val newSuppliedArgs = suppliedArgs.zip(args).map { case (set, v) => set + v }
      res += (name -> newSuppliedArgs)
    }
  }

}
