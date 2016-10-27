package scala.scalanative
package compiler
package pass

import scala.collection.mutable
import scala.util.hashing.MurmurHash3

import analysis.ClassHierarchy.Top
import analysis.ClassHierarchyExtractors._
import analysis.ControlFlow
import analysis.ControlFlow.Block
import analysis.DominatorTree

import nir._, Shows._

class GlobalValueNumbering(implicit top: Top) extends Pass {
  import GlobalValueNumbering._
  import Debug._

  //private var maxOldBlocks = 80

  override def preDefn = {
    case defn: Defn.Define =>
      val cfg = ControlFlow.Graph(defn.insts)

      val methodName = showGlobal(defn.name).toString
      //println("| | | |")
      //println(s"Processing $methodName ...")
      Debug.scope = methodName

      //val debugMethod = "@java.util.Arrays$::java$util$Arrays$$checkRangeIndices_i32_i32_i32_unit"
      //Debug.verbose = (methodName == debugMethod)

      val domination = DominatorTree.build(cfg)
      //val refDomination = DominatorTree.buildRef(cfg)

      //Debug.testDominationEquality(domination, refDomination)

      //val debugMethod = "@scala.collection.immutable.VectorPointer$class$::gotoFreshPosWritable0_trait.scala.collection.immutable.VectorPointer_i32_i32_i32_unit"
      //if (methodName == debugMethod) {
      //val fixpointDomination = buildFixpointDomination(cfg)
      //Debug.testDominationEquality(domination, fixpointDomination)
      //println("=====\nCFG:")
      //println(showCFG(cfg))
      //println("=====\ncfg.dot:")
      //println(cfgToDot(cfg))
      //println("=====\nDominator tree:")
      //println(showDominatorTree(domination))
      //println("=====\nFixpoint Dominator tree:")
      //println(showDominatorTree(fixpointDomination))
      //}

      //if (defn.oldblocks.size > maxOldBlocks) {
      //println(s"=====\nNew biggest CFG (size=${maxOldBlocks}):")
      //println(cfgToDot(cfg))
      //maxOldBlocks = defn.oldblocks.size
      //}

      val newInsts = performSimpleValueNumbering(cfg, domination)

      Seq(defn.copy(insts = newInsts))
  }

  def pred(block: Block) = block.pred.map(_.from)
  def succ(block: Block) = block.succ.map(_.to)

  def performSimpleValueNumbering(
      cfg: ControlFlow.Graph,
      domination: Map[Block, Set[Block]]): Seq[Inst] = {

    val variableVN   = mutable.HashMap.empty[Local, Hash]
    val instructions = mutable.HashMap.empty[Hash, List[Inst.Let]]
    val localDefs    = mutable.HashMap.empty[Local, Inst]

    val hash       = new HashFunction(variableVN)
    val deepEquals = new DeepEquals(localDefs)

    //println(showMap(cfg.find.map{case (l,b) => (showLocal(l), showLocal(b.name))}))

    def blockDominatedByDef(dominatedBlock: Block,
                            dominatingDef: Local): Boolean = {

      domination(dominatedBlock).exists { dominatingBlock =>
        val foundInParam = dominatingBlock.params.exists {
          case Val.Local(paramName, _) => paramName == dominatingDef
        }
        val foundInInsts = dominatingBlock.insts.exists {
          case Inst.Let(name, _) => (name == dominatingDef)
          case _                 => false
        }

        foundInParam || foundInInsts
      }
    }

    val newInsts = cfg.map { block =>
      variableVN ++= block.params.map(lval =>
        (lval.name, HashFunction.rawLocal(lval.name)))
      localDefs ++= block.params.map(lval => (lval.name, block.label))

      val newBlockInsts = block.insts.map { //inst =>

        case inst: Inst.Let => {
          val idempotent = isIdempotent(inst.op)

          if (Debug.verbose)
            println(
              s"Processing instruction '${showInst(inst)}' of type Let and ${if (!idempotent) "not" else ""} idempotent")

          val instHash =
            if (idempotent)
              hash(inst.op)
            else
              inst.hashCode // hash the assigned variable as well, so a = op(b) and c = op(b) don't have the same hash

          variableVN += (inst.name -> instHash)
          localDefs += (inst.name  -> inst)

          if (Debug.verbose)
            println(
              s"Added the hash ${showHash(instHash)} for ${showLocal(inst.name)}")

          if (idempotent) {
            val hashEqualInstrs = instructions.getOrElse(instHash, Nil)
            instructions += (instHash -> (inst :: hashEqualInstrs))

            val equalInstrs =
              hashEqualInstrs.filter(otherInst =>
                deepEquals.eqInst(inst, otherInst))
            val redundantInstrs = equalInstrs.filter(eqInst =>
              blockDominatedByDef(block, eqInst.name)) // only redundant if the current block is dominated by the block in which the equal instruction occurs
            //val redundantInstrs = equalInstrs.filter(eqInst => domination(block).contains(cfg.blocks(eqInst.name)))  // only redundant if the current block is dominated by the block in which the equal instruction occurs

            //if (Debug.verbose) {
            val hashCollisions = hashEqualInstrs.filterNot(otherInst =>
              deepEquals.eqInst(inst, otherInst))
            if (hashCollisions.nonEmpty) {
              println(s"Collisions in method ${Debug.scope}:")
              println(showInst(inst))
              println(
                hashCollisions
                  .map(showInst(_).toString)
                  .mkString(" =!= ", "\n =!= ", "\n"))
            }
            //}

            val newInstOpt = redundantInstrs.headOption.map(
              redInst =>
                Inst.Let(inst.name,
                         Op.Copy(Val.Local(redInst.name, redInst.op.resty))))
            newInstOpt.getOrElse(inst)
          } else {
            inst
          }
        }

        case otherInst @ _ =>
          if (Debug.verbose)
            println(s"Ignoring instruction '${showInst(otherInst)}'")
          otherInst
      }

      block.label +: newBlockInsts
    }

    newInsts.flatten
  }

  //def deepEqual(instA: Inst, instB: Inst, localDefs: Map[Local, Inst]): Boolean = {
  //val opA = instA.op
  //val opB = instB.op

  //if (opA.name == opB.name)
  //true
  //else if (!isIdempotent(opA) || !isIdempotent(opB))
  //false
  //else {
  //(opA, opB) match {
  //// Here we know that both functions are pure
  //case (Call(tyA, ptrA, argsA), Call(tyB, ptrB, argsB)) =>
  //(tyA == tyB && deepEqual)
  //case Load(ty, ptr) =>
  //if (Debug.verbose) print(s"Hashing ${showOp(op)}: ")
  //Seq("Load", ty, ptr)
  //case Store(ty, ptr, value)  => Seq("Store", ty, ptr, value)
  //case Elem(ty, ptr, indexes) => "Elem" +: ty +: ptr +: indexes
  //case Extract(aggr, indexes) => "Extract" +: aggr +: indexes
  //case Insert(aggr, value, indexes) =>
  //"Insert" +: aggr +: value +: indexes

  //case Stackalloc(ty, n)          => Seq("Stackalloc", ty, n)
  //case Bin(bin, ty, l, r)         => Seq("Bin", bin, ty, l, r)
  //case Comp(comp, ty, l, r)       => Seq("Comp", comp, ty, l, r)
  //case Conv(conv, ty, value)      => Seq("Conv", ty, value)
  //case Select(cond, thenv, elsev) => Seq("Select", cond, thenv, elsev)

  ////case Classalloc(name) => hashGlobal(name)
  //case Field(ty, obj, name)  => Seq("Field", obj, name)
  //case Method(ty, obj, name) => Seq("Method", ty, obj, name)
  ////case Module(name) => ???
  //case As(ty, obj) => Seq("As", ty, obj)
  //case Is(ty, obj) => Seq("Is", ty, obj)
  //case Copy(value) => Seq("Copy", value)
  ////case Sizeof(ty) =>
  //case Closure(ty, fun, captures) => "Closure" +: ty +: fun +: captures

  //case _ => false
  //}
  //}
  //}

}

object GlobalValueNumbering extends PassCompanion {
  def apply(ctx: Ctx) = new GlobalValueNumbering()(ctx.top)

  /* The definition of idempotent for Call might be wrong.
   * Example:
   * val a = new AnyRef { var b: Int = 0; override def toString = b.toString }
   * val c = a.toString
   * a.b = 1
   * val d = a.toString
   * --> toString is pure, but the values of c and d are different !
   * */
  def isIdempotent(op: Op)(implicit top: Top): Boolean = {
    import Op._
    op match {
      // Always idempotent:
      case (_: Pure | _: Method | _: As | _: Is | _: Copy | _: Sizeof |
          _: Module | _: Field) =>
        true

      // Never idempotent:
      case (_: Load | _: Store | _: Stackalloc | _: Classalloc) => false

      // Special cases:
      case Call(_, Val.Global(Ref(node), _), _) =>
        node.attrs.isPure

      case Call(_, _, _) => false

      case _: Closure => ???
    }
  }

  class DeepEquals(localDefs: Local => Inst)(implicit top: Top) {

    def eqInst(instA: Inst.Let, instB: Inst.Let): Boolean = {
      (instA.name == instB.name) || eqOp(instA.op, instB.op)
    }

    def eqOp(opA: Op, opB: Op): Boolean = {
      import Op._
      if (!(isIdempotent(opA) && isIdempotent(opB)))
        false
      else {
        (opA, opB) match {
          // Here we know that the function called is idempotent
          case (Call(tyA, ptrA, argsA), Call(tyB, ptrB, argsB)) =>
            eqType(tyA, tyB) && eqVal(ptrA, ptrB) && eqVals(argsA, argsB)

          case (Load(_, _), Load(_, _)) =>
            false // non idempotent

          case (Store(_, _, _), Store(_, _, _)) =>
            false // non idempotent

          case (Elem(tyA, ptrA, indexesA), Elem(tyB, ptrB, indexesB)) =>
            eqType(tyA, tyB) && eqVal(ptrA, ptrB) && eqVals(indexesA, indexesB)

          case (Extract(aggrA, indexesA), Extract(aggrB, indexesB)) =>
            eqVal(aggrA, aggrB) && indexesA.zip(indexesB).forall {
              case (m, n) => m == n
            }

          case (Insert(aggrA, valueA, indexesA),
                Insert(aggrB, valueB, indexesB)) =>
            eqVal(aggrA, aggrB) && eqVal(valueA, valueB) && indexesA
              .zip(indexesB)
              .forall { case (m, n) => m == n }

          case (Stackalloc(_, _), Stackalloc(_, _)) =>
            false // non idempotent

          // TODO handle commutativity of some bins
          case (Bin(binA, tyA, lA, rA), Bin(binB, tyB, lB, rB)) =>
            eqBin(binA, binB) && eqType(tyA, tyB) && eqVal(lA, lB) && eqVal(rA,
                                                                            rB)

          case (Comp(compA, tyA, lA, rA), Comp(compB, tyB, lB, rB)) =>
            eqComp(compA, compB) && eqType(tyA, tyB) && eqVal(lA, lB) && eqVal(
              rA,
              rB)

          case (Conv(convA, tyA, valueA), Conv(convB, tyB, valueB)) =>
            eqConv(convA, convB) && eqType(tyA, tyB) && eqVal(valueA, valueB)

          case (Select(condA, thenvA, elsevA),
                Select(condB, thenvB, elsevB)) =>
            eqVals(Seq(condA, thenvA, elsevA), Seq(condB, thenvB, elsevB))

          case (Classalloc(_), Classalloc(_)) =>
            false // non idempotent

          case (Field(tyA, objA, nameA), Field(tyB, objB, nameB)) =>
            eqType(tyA, tyB) && eqVal(objA, objB) && eqGlobal(nameA, nameB)

          case (Method(tyA, objA, nameA), Method(tyB, objB, nameB)) =>
            eqType(tyA, tyB) && eqVal(objA, objB) && eqGlobal(nameA, nameB)

          case (Module(nameA), Module(nameB)) =>
            eqGlobal(nameA, nameB)

          case (As(tyA, objA), As(tyB, objB)) =>
            eqType(tyA, tyB) && eqVal(objA, objB)

          case (Is(tyA, objA), Is(tyB, objB)) =>
            eqType(tyA, tyB) && eqVal(objA, objB)

          case (Copy(valueA), Copy(valueB)) =>
            eqVal(valueA, valueB)

          case (Sizeof(tyA), Sizeof(tyB)) =>
            eqType(tyA, tyB)

          case (Closure(tyA, funA, capturesA),
                Closure(tyB, funB, capturesB)) =>
            eqType(tyA, tyB) && eqVal(funA, funB) && eqVals(capturesA,
                                                            capturesB)

          case _ => false // non-matching pairs of ops
        }
      }
    }

    def eqVal(valueA: Val, valueB: Val): Boolean = {
      import Val._
      (valueA, valueB) match {
        case (Struct(nameA, valuesA), Struct(nameB, valuesB)) =>
          eqGlobal(nameA, nameB) && eqVals(valuesA, valuesB)

        case (Array(elemtyA, valuesA), Array(elemtyB, valuesB)) =>
          eqType(elemtyA, elemtyB) && eqVals(valuesA, valuesB)

        case (Const(valueA), Const(valueB)) =>
          eqVal(valueA, valueB)

        case (Local(nameA, valtyA), Local(nameB, valtyB)) =>
          lazy val eqDefs = (localDefs(nameA), localDefs(nameB)) match {
            case (_: Inst.Label, _: Inst.Label)     => (nameA == nameB)
            case (instA: Inst.Let, instB: Inst.Let) => eqInst(instA, instB)
            case _                                  => false
          }
          eqType(valtyA, valtyB) && ((nameA == nameB) || eqDefs)

        case _ =>
          valueA == valueB
      }
    }

    def eqVals(valsA: Seq[Val], valsB: Seq[Val]): Boolean = {
      valsA.zip(valsB).forall { case (a, b) => eqVal(a, b) }
    }

    def eqType(tyA: Type, tyB: Type): Boolean = {
      tyA == tyB
    }

    def eqGlobal(globalA: Global, globalB: Global): Boolean = {
      globalA == globalB
    }

    def eqBin(binA: Bin, binB: Bin): Boolean = {
      binA == binB
    }

    def eqComp(compA: Comp, compB: Comp): Boolean = {
      compA == compB
    }

    def eqConv(convA: Conv, convB: Conv): Boolean = {
      convA == convB
    }

  }

  type Hash = Int

  class HashFunction(hashLocal: Local => Hash) extends (Any => Hash) {

    import HashFunction._

    def apply(obj: Any): Hash = {
      obj match {
        case op: Op     => hashOp(op)
        case value: Val => hashVal(value)

        case local: Local => hashLocal(local)

        case ty: Type   => hashType(ty)
        case g: Global  => hashGlobal(g)
        case bin: Bin   => hashBin(bin)
        case comp: Comp => hashComp(comp)
        case conv: Conv => hashConv(conv)

        case b: Boolean  => b.hashCode
        case i: Int      => i.hashCode
        case d: Double   => d.hashCode
        case str: String => str.hashCode

        case _ =>
          throw new IllegalArgumentException(
            s"Unable to hash value {${obj}} of type ${obj.getClass.getName}")
      }
    }

    def hashOp(op: Op): Hash = {
      import Op._
      val opFields: Seq[Any] = op match {
        case Call(ty, ptr, args)    => "Call" +: ty +: ptr +: args
        case Load(ty, ptr)          => Seq("Load", ty, ptr)
        case Store(ty, ptr, value)  => Seq("Store", ty, ptr, value)
        case Elem(ty, ptr, indexes) => "Elem" +: ty +: ptr +: indexes
        case Extract(aggr, indexes) => "Extract" +: aggr +: indexes
        case Insert(aggr, value, indexes) =>
          "Insert" +: aggr +: value +: indexes

        case Stackalloc(ty, n)          => Seq("Stackalloc", ty, n)
        case Bin(bin, ty, l, r)         => Seq("Bin", bin, ty, l, r)
        case Comp(comp, ty, l, r)       => Seq("Comp", comp, ty, l, r)
        case Conv(conv, ty, value)      => Seq("Conv", ty, value)
        case Select(cond, thenv, elsev) => Seq("Select", cond, thenv, elsev)

        case Field(ty, obj, name)       => Seq("Field", obj, name)
        case Method(ty, obj, name)      => Seq("Method", ty, obj, name)
        case As(ty, obj)                => Seq("As", ty, obj)
        case Is(ty, obj)                => Seq("Is", ty, obj)
        case Copy(value)                => Seq("Copy", value)
        case Closure(ty, fun, captures) => "Closure" +: ty +: fun +: captures

        case Classalloc(name) => Seq("Classalloc", name)
        case Module(name)     => Seq("Module", name)
        case Sizeof(ty)       => Seq("Sizeof", ty)
      }

      combineHashes(opFields.map(this.apply))
    }

    def hashVal(value: Val): Hash = {
      import Val._
      val fields: Seq[Any] = value match {
        case Struct(name, values)  => "Struct" +: name +: values
        case Array(elemty, values) => "Array" +: elemty +: values
        case Const(value)          => Seq("Const", value)

        case Local(name, _) => Seq(hashLocal(name))

        // the other val kinds can't have another Val in them
        case _ => Seq(value.hashCode)
      }

      combineHashes(fields.map(this.apply))
    }

    def hashType(ty: Type): Hash = {
      ty.hashCode
    }

    def hashGlobal(global: Global): Hash = {
      global.hashCode
    }

    def hashBin(bin: Bin): Hash = {
      bin.hashCode
    }

    def hashComp(comp: Comp): Hash = {
      comp.hashCode
    }

    def hashConv(conv: Conv): Hash = {
      conv.hashCode
    }

  }

  object HashFunction {

    def combineHashes(hashes: Seq[Hash]): Hash = {
      MurmurHash3.orderedHash(hashes)
    }

    def rawLocal(local: Local): Hash = {
      combineHashes(Seq(local.scope.hashCode, local.id.hashCode))
    }

  }

  object Debug {

    var verbose = false
    var scope   = ""

    def showMap[A, B](map: Map[A, B]): String = {
      map.toList.map {
        case (k, v) => s"($k -> $v)"
      }.mkString("\n")
    }

    def showHash(h: Hash): String = {
      val buf = java.nio.ByteBuffer.allocate(4)
      buf.putInt(h)
      java.util.Base64.getEncoder.encodeToString(buf.array).dropRight(2)
    }

    def blockToString(block: Block): String =
      showLocal(block.name).toString

    def showCFG(cfg: ControlFlow.Graph): String =
      cfg
        .map(block =>
          s"${blockToString(block)} -> ${block.succ
            .map(_.to)
            .map(blockToString)
            .mkString("(", ",", ")")}, pred = ${block.pred.map(_.from).map(blockToString).mkString("(", ",", ")")}")
        .mkString("\n")

    def showDominatorTree(domination: Map[Block, Set[Block]]): String = {
      domination.toList
        .sortBy(_._1.name.id)
        .map {
          case (block, set) =>
            s"${blockToString(block)} -> ${set.map(blockToString).mkString("(", ",", ")")}"
        }
        .mkString("\n")
    }

    def cfgToDot(cfg: ControlFlow.Graph): String = {
      def blockToDot(block: Block): String = {
        val successors = block.succ.map(_.to)
        val blockID    = block.name.id
        if (successors.nonEmpty)
          successors
            .map(succ => succ.name.id.toString)
            .mkString(s"${blockID} -> {", " ", "};")
        else
          s"${blockID} [ shape=doublecircle ];"
      }

      s"""
         |digraph {
         | node [shape=circle, width=0.6, fixedsize=true];
         |${cfg.map(blockToDot).mkString("\n")}
         |}
      """.stripMargin
    }

    def showI32(n: Int): String = {
      val binString    = n.toBinaryString
      val leadingZeros = 32 - binString.size
      ("0" * leadingZeros) + binString
    }

    def testDominationEquality(domA: Map[Block, Set[Block]],
                               domB: Map[Block, Set[Block]]): Unit = {
      val allBlocks = domA.keySet ++ domB.keySet
      val blockDifferences = allBlocks.map { block =>
        val a = domA.getOrElse(block, Set.empty)
        val b = domB.getOrElse(block, Set.empty)
        (block, (a diff b), (b diff a))
      }
      val existingDifferences = blockDifferences.filter {
        case (_, diffA, diffB) => diffA.nonEmpty || diffB.nonEmpty
      }

      if (existingDifferences.nonEmpty) {
        println("<===>")
        println(
          s"${existingDifferences.size} differences found between the dominations (in $scope)")
        val diffString = existingDifferences.map {
          case (block, diffA, diffB) =>
            s"${blockToString(block)} -> A \\ B = ${diffA.map(blockToString)}, B \\ A = ${diffB.map(blockToString)}"
        }
        println(diffString.mkString("\n"))
      }
    }
  }

}
