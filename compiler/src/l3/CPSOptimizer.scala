package l3

import l3.CL3Literal.{BooleanLit}
import scala.collection.mutable.Map as MutableMap
import scala.reflect.TypeTest
import scala.annotation.tailrec


abstract class CPSOptimizer[T <: SymbolicNames]
(protected val treeModule: T)
(using TypeTest[treeModule.Atom, treeModule.Literal],
 TypeTest[treeModule.Atom, treeModule.Name],
 TypeTest[treeModule.Tree, treeModule.Body]) {
  import treeModule._


  protected def rewrite(tree: Program): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = size(simplifiedTree) * 3 / 2
    fixedPoint(simplifiedTree, 8)(`inline`(_, maxSize))
  }

  private case class Count(applied: Int = 0, asValue: Int = 0)

  private case class State(
                            // keeps track of how many times variables are applied, name -> count
                            census: Map[Name, Count],
                            // keeps track of the substitution of atoms
                            aSubst: Subst[Atom] = emptySubst,
                            // keeps track of the substitution of continuations
                            cSubst: Subst[Name] = emptySubst,
                            // keeps track of the results of evaluating expressions
                            eInvEnv: Map[(ValuePrimitive, Seq[Atom]), Atom] = Map.empty,
                            // keeps track of substitutions for blocks
                            bEnv: Map[(Atom, Atom), Atom] = Map.empty,
                            // keeps track of the continuations
                            cEnv: Map[Name, Cnt] = Map.empty,
                            // keeps track of the functions
                            fEnv: Map[Name, Fun] = Map.empty) {

    // TODO: what about transitive dependencies?
    def dead(s: Name): Boolean =
      ! census.contains(s)

    def appliedOnce(s: Name): Boolean =
      census.get(s).contains(Count(applied = 1))

    def hasFun(fun: Name, actualArgs: Seq[Atom]): Boolean =
      fEnv.get(fun).exists(_.args.length == actualArgs.length)
    def hasCnt(cnt: Name, actualArgs: Seq[Atom]): Boolean =
      cEnv.get(cnt).exists(_.args.length == actualArgs.length)

    def withASubst(from: Atom, to: Atom): State =
      copy(aSubst = aSubst + (from -> aSubst(to)))
    def withASubst(from: Seq[Name], to: Seq[Atom]): State =
      copy(aSubst = aSubst ++ (from zip to.map(aSubst)))

    def withBSubst(from: (Atom, Atom), to: Atom): State =
      copy(bEnv = bEnv + (from -> to))

    def withCSubst(from: Name, to: Name): State =
      copy(cSubst = cSubst + (from -> cSubst(to)))

    def withExp(atom: Atom, prim: ValuePrimitive, args: Seq[Atom]): State =
      copy(eInvEnv = eInvEnv + ((prim, args) -> atom))

    def withCnts(cnts: Seq[Cnt]): State =
      copy(cEnv = cEnv ++ (cnts.map(_.name) zip cnts))
    def withFuns(funs: Seq[Fun]): State =
      copy(fEnv = fEnv ++ (funs.map(_.name) zip funs))

    def substituteOrIgnore(atom: Atom): Atom =
      atom match {
        // Check if the atom is a name that has been substituted
        // in the current state, if so return the substitution,
        // otherwise return the atom itself.
        case n: Name => aSubst.getOrElse(n, cSubst.getOrElse(n, n))
        case _ => atom
      }
  }

  // Needed for the construction of trees containing other trees,
  // which requires checking (dynamically here) it is indeed a subtype of Body.
  given Conversion[Tree, Body] = {
    case body: Body => body
    case other => sys.error(s"${other} is not a Body")
  }

  private def shrink(tree: Tree): Tree =
    shrink(tree, State(census(tree)))

  private def shrinkLetP(letp: LetP, s: State): Tree = {
    letp match {

      case LetP(name, this.identity, Seq(idName: Name), body) =>
        shrink(body, s.withASubst(name, idName))

      case LetP(name, this.identity, Seq(idLit: Literal), body) =>
        shrink(body, s.withASubst(name, idLit))

      /* Block primitives.  */
      case LetP(name, this.blockAlloc, args@Seq(tagNumber, sz: Literal), body)  if Set(0,2,3,4,5).contains(tagNumber) =>
        LetP(name, this.blockAlloc, args, shrink(body, s.withBSubst((name, name), name)))

      case LetP(name, this.blockSet, args@Seq(b, i, a), body)
        if s.bEnv.contains((b, b)) =>
        LetP(name, this.blockSet, args, shrink(body, s.withBSubst((b, i), a)))

      case LetP(name, this.blockGet, args@Seq(b, i), body)
        if s.bEnv.contains((b, i)) =>
        shrink(body, s.withASubst(name, s.bEnv((b, i))))

      /* Constant folding.  */
      // Case 1: the primitive is a value primitive
      case LetP(name, prim, args@Seq(a: Literal, b: Literal), body)
        if vEvaluator.isDefinedAt((prim, args)) =>
          shrink(body, s.withASubst(name, vEvaluator((prim, args))))

      /* Dead code elimination.  */
      case LetP(name, prim, _, body) if !impure(prim) && s.dead(name) =>
        shrink(body, s)

      /* Neutral/absorbing element elimination.  */
      case LetP(name, prim, Seq(l: Literal, a: Atom), body)
        if leftNeutral((l, prim)) => shrink(body, s.withASubst(name, a))
      case LetP(name, prim, Seq(a: Atom, l: Literal), body)
        if rightNeutral((prim, l)) => shrink(body, s.withASubst(name, a))
      case LetP(name, prim, Seq(l: Literal, a: Atom), body)
        if leftAbsorbing((l, prim)) => shrink(body, s.withASubst(name, l))
      case LetP(name, prim, Seq(a: Atom, l: Literal), body)
        if rightAbsorbing((prim, l)) => shrink(body, s.withASubst(name, l))

      case LetP(name, prim, Seq(arg1, arg2), body)
        if sameArgValue(arg1, arg2, s) && sameArgReduce.isDefinedAt((prim, arg1)) =>
          val simplifiedArg = sameArgReduce((prim, arg1))
          shrink(body, s.withASubst(name, simplifiedArg))

      /* Common subexpression elimination.  */
      case LetP(name, prim, args, body) =>
        val args1 = args.map(s.substituteOrIgnore)

        // Check if the expression has already been evaluated
        s.eInvEnv.get((prim, args1)).map { res =>
          shrink(body, s.withASubst(name, res))
        }.getOrElse {
          if !impure(prim) && !unstable(prim) then
            LetP(name, prim, args1, shrink(body, s.withExp(name, prim, args1)))
          else
            LetP(name, prim, args1, shrink(body, s))
        }
    }
  }

  private def sameArgValue(arg1: Atom, arg2: Atom, s: State): Boolean = {
    (s.substituteOrIgnore(arg1), s.substituteOrIgnore(arg2)) match {
      case (lit1: Literal, lit2: Literal) => lit1 == lit2
      case (name1: Name, name2: Name) => name1 == name2
      case _ => false
    }
  }

  private def shrinkLetF(letF: LetF, s: State): Tree = {
    val (toInline, toKeep) = letF.funs
      .filterNot(f => s.dead(f.name))
      .partition(f => s.appliedOnce(f.name))

    val newState = s.withFuns(toInline)
    if toKeep.isEmpty then
      shrink(letF.body, newState)
    else
      LetF(
        toKeep.map(f => f.copy(body = shrink(f.body, newState))),
        shrink(letF.body, newState)
      )
  }

    private def shrinkLetC(letC: LetC, s: State): Tree = {
      val (toInline, toKeep) = letC.cnts
        .filterNot(c => s.dead(c.name))
        .partition(c => s.appliedOnce(c.name))

      val newState = s.withCnts(toInline)
      if toKeep.isEmpty then
        shrink(letC.body, newState)
      else
        LetC(
          toKeep.map(c => c.copy(body = shrink(c.body, newState))),
          shrink(letC.body, newState)
        )
    }


  private def shrinkAppF(appF: AppF, s: State): Tree = {
    appF match {
      case AppF(fun, retC, args) if s.aSubst.contains(fun) =>
        shrink(AppF(s.aSubst(fun), retC, args), s)

      case AppF(fun: Name, retC, args) if s.cSubst.contains(fun) =>
        shrink(AppF(s.cSubst(fun), retC, args), s)

      case AppF(fun: Name, retC, args) if s.fEnv.contains(fun) =>
        val Fun(_, funRetC, funArgs, funBody) = s.fEnv(fun)
        shrink(funBody, s.withASubst(funArgs, args).withCSubst(funRetC, retC))

      case _ => appF
    }
  }

  private def shrinkAppC(appC: AppC, s: State): Tree = {
    appC match {
      case AppC(cnt, args) if s.cSubst.contains(cnt) =>
        shrink(AppC(s.cSubst(cnt), args), s)
      case AppC(cnt, args) if s.cEnv.contains(cnt) =>
        val Cnt(_, cntArgs, cntBody) = s.cEnv(cnt)
        shrink(cntBody, s.withASubst(cntArgs, args))
      case _ => appC
    }
  }

  private def shrinkIf(i: If, s: State): Tree = {
    i match {
      // Constant folding
      case If(cond, Seq(a: Literal, b: Literal), thenC, elseC)
        if cEvaluator.isDefinedAt((i.cond, Seq(a, b))) =>
        shrink(
          AppC(
            if cEvaluator((i.cond, Seq(a, b))) then thenC else elseC, Seq()
          ), s
        )

      case If(cond, Seq(a: BooleanLit, b: BooleanLit), thenC, elseC)
        if sameArgReduceC(cond) => shrink(AppC(if (a == b) then thenC else elseC, Seq()), s)

      // Semi-constant constant folding (if (a == a) then b else c) -> b
      // a < a is always false, a == a is always true..., we'll use equalCEvaluator
      case If(cond, Seq(a: Atom, b: Atom), thenC, elseC) if a == b && equalCEvaluator.isDefinedAt(cond) =>
        shrink(AppC(if equalCEvaluator(cond) then thenC else elseC, Seq()), s)

      case _ => i

    }
  }

  private def shrink(tree: Tree, s: State): Tree = tree match {
    case letP: LetP =>
      shrinkLetP(letP, s)
    case letF: LetF =>
      shrinkLetF(letF, s)
    case letC: LetC =>
      shrinkLetC(letC, s)
    case Halt(a) =>
      Halt(s.substituteOrIgnore(a))
    case ifT: If =>
      shrinkIf(ifT.copy(args = ifT.args.map(s.substituteOrIgnore)), s)
    case appC: AppC =>
      shrinkAppC(appC.copy(args = appC.args.map(s.substituteOrIgnore)), s)
    case AppF(fun, retC, args) =>
      shrinkAppF(AppF(fun, s.cSubst.getOrElse(retC, retC), args.map(s.substituteOrIgnore)), s)
  }

  // (Non-shrinking) inlining

  private def inline(tree: Tree, maxSize: Int): Tree = {
    def copyT(t: Tree, subV: Subst[Atom], subC: Subst[Name]): Tree = t match {
      case LetF(funs, body) =>
        val names = funs map (_.name)
        val names1 = names map (_.copy())
        val subV1 = subV ++ (names zip names1)
        LetF(funs map (copyF(_, subV1, subC)), copyT(body, subV1, subC))
      case LetC(cnts, body) =>
        val names = cnts map (_.name)
        val names1 = names map (_.copy())
        val subC1 = subC ++ (names zip names1)
        LetC(cnts map (copyC(_, subV, subC1)), copyT(body, subV, subC1))
      case LetP(name, prim, args, body) =>
        val name1 = name.copy()
        LetP(name1, prim, args map subV,
          copyT(body, subV + (name -> name1), subC))
      case AppF(fun, retC, args) =>
        AppF(subV(fun), subC(retC), args map subV)
      case AppC(cnt, args) =>
        AppC(subC(cnt), args map subV)
      case If(cond, args, thenC, elseC) =>
        If(cond, args map subV, subC(thenC), subC(elseC))
      case Halt(arg) =>
        Halt(subV(arg))
    }

    def copyF(fun: Fun, subV: Subst[Atom], subC: Subst[Name]): Fun = {
      val retC1 = fun.retC.copy()
      val subC1 = subC + (fun.retC -> retC1)
      val args1 = fun.args map (_.copy())
      val subV1 = subV ++ (fun.args zip args1)
      val funName1 = subV(fun.name).asInstanceOf[Name]
      Fun(funName1, retC1, args1, copyT(fun.body, subV1, subC1))
    }

    def copyC(cnt: Cnt, subV: Subst[Atom], subC: Subst[Name]): Cnt = {
      val args1 = cnt.args map (_.copy())
      val subV1 = subV ++ (cnt.args zip args1)
      Cnt(subC(cnt.name), args1, copyT(cnt.body, subV1, subC))
    }

    val fibonacci = Seq(1, 2, 3, 5, 8, 13)

    val trees = LazyList.iterate((0, tree), fibonacci.length){ (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i

      def inlineT(tree: Tree)(implicit s: State): Tree =
        def cntInlineHeuristic(cnt: Cnt): Boolean = {
          size(cnt.body) <= cntLimit
        }

        // Helper function to detect recursive calls
        def containsRecursiveCall(funName: Name, tree: Tree): Boolean = tree match {
          case AppF(target: Name, _, _) => target == funName
          case LetF(funs, body) => funs.exists(f => containsRecursiveCall(funName, f.body)) || containsRecursiveCall(funName, body)
          case LetC(cnts, body) => cnts.exists(c => containsRecursiveCall(funName, c.body)) || containsRecursiveCall(funName, body)
          case LetP(_, _, _, body) => containsRecursiveCall(funName, body)
          case _ => false
        }

        def funInlineHeuristic(fun: Fun): Boolean = {
          // Heuristic based on function size
          val isSmall = size(fun.body) < funLimit

          // Check for recursive calls within the function body
          val isRecursive = containsRecursiveCall(fun.name, fun.body)

          // Combine heuristics: inline if function is small, pure, and not recursive
          isSmall && !isRecursive
        }

        tree match {

          case LetP(name, prim, args, body) => LetP(name, prim, args, inlineT(body))

          case LetC(cnts, body) =>
            val inlined = cnts.map(x => x.copy(body = inlineT(x.body)))
            val toInline = inlined.filter(c => cntInlineHeuristic(c))
            LetC(inlined, inlineT(body)(s.withCnts(toInline)))

          case LetF(funs, body) =>
            val inlined = funs.map(x => x.copy(body = inlineT(x.body)))
            val toInline = inlined.filter(f => funInlineHeuristic(f))
            LetF(inlined, inlineT(body)(s.withFuns(toInline)))

          case AppF(fun: Name, retC, args) => s.fEnv.get(fun) match {
            case Some(Fun(_, funRetC, funArgs, funBody)) if funArgs.length == args.length =>
              val subV = funArgs.zip(args).toMap
              val subA = s.aSubst ++ subV
              val subN = s.cSubst + (funRetC -> retC)
              copyT(funBody, subA, subN)

            case _ => tree
          }

          case AppC(cnt: Name, args) => s.cEnv.get(cnt) match {
            case Some(Cnt(_, cntArgs, cntBody)) if cntArgs.length == args.length =>
              val subV = cntArgs.zip(args).toMap
              val subA = s.aSubst ++ subV
              val subN = s.cSubst
              copyT(cntBody, subA, subN)

            case _ => tree
          }

          case _ => tree
      }
      (i + 1, fixedPoint(inlineT(tree)(using State(census(tree))))(shrink))
    }

    trees.takeWhile{ (_, tree) => size(tree) <= maxSize }.last._2
  }

  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]().withDefault(_ => Count())
    val rhs = MutableMap[Name, Tree]()

    def incAppUse(atom: Atom): Unit = atom match {
      case n: Name =>
        val currCount = census(n)
        census(n) = currCount.copy(applied = currCount.applied + 1)
        rhs.remove(n).foreach(addToCensus)
      case _: Literal =>
    }

    def incValUse(atom: Atom): Unit = atom match {
      case n: Name =>
        val currCount = census(n)
        census(n) = currCount.copy(asValue = currCount.asValue + 1)
        rhs.remove(n).foreach(addToCensus)
      case _: Literal =>
    }

    @tailrec
    def addToCensus(tree: Tree): Unit = tree match {
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetP(_, _, args, body) =>
        args foreach incValUse; addToCensus(body)
      case AppF(fun, retC, args) =>
        incAppUse(fun); incValUse(retC); args foreach incValUse
      case AppC(cnt, args) =>
        incAppUse(cnt); args foreach incValUse
      case If(_, args, thenC, elseC) =>
        args foreach incValUse; incValUse(thenC); incValUse(elseC)
      case Halt(arg) =>
        incValUse(arg)
    }

    addToCensus(tree)
    census.toMap
  }

  private def size(tree: Tree): Int = tree match {
    case LetF(fs, body) => fs.map(_.body).map(size).sum + size(body)
    case LetC(cs, body) => cs.map(_.body).map(size).sum + size(body)
    case LetP(_, _, _, body) => size(body) + 1
    case _: (AppF | AppC | If | Halt) => 1
  }

  protected val impure: ValuePrimitive => Boolean
  protected val unstable: ValuePrimitive => Boolean

  protected val blockAlloc: ValuePrimitive
  protected val blockTag: ValuePrimitive
  protected val blockLength: ValuePrimitive
  protected val blockSet: ValuePrimitive
  protected val blockGet: ValuePrimitive

  protected val identity: ValuePrimitive
  protected val byteWrite: ValuePrimitive

  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom]
  protected val sameArgReduceC: TestPrimitive => Boolean

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Atom]),
    Literal]
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Atom]),
    Boolean]

  protected val equalCEvaluator: PartialFunction[TestPrimitive, Boolean]
}

object HighCPSOptimizer extends CPSOptimizer(HighCPSTreeModule)
  with (HighCPSTreeModule.Program => HighCPSTreeModule.Program) {
  import treeModule._
  import CL3Literal._, L3Primitive._


  def apply(program: Program): Program =
    rewrite(program)

  private[this] given Conversion[L3Int, Literal] = IntLit.apply
  private[this] given Conversion[Int, Literal] = L3Int.apply

  protected val impure: ValuePrimitive => Boolean = Set(ByteRead, ByteWrite, BlockSet)

  protected val unstable: ValuePrimitive => Boolean = {
    case BlockAlloc | BlockGet | ByteRead => true
    case _ => false
  }

  protected val blockAlloc: ValuePrimitive = BlockAlloc
  protected val blockTag: ValuePrimitive = BlockTag
  protected val blockLength: ValuePrimitive = BlockLength
  protected val blockSet: ValuePrimitive = BlockSet
  protected val blockGet: ValuePrimitive = BlockGet

  protected val identity: ValuePrimitive = Id
  protected val byteWrite: ValuePrimitive = ByteWrite

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, IntAdd), (1, IntMul),
      (~0, IntBitwiseAnd), (0, IntBitwiseOr),
      (0, IntBitwiseXOr))

  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((IntAdd, 0), (IntSub, 0), (IntMul, 1), (IntDiv, 1),
      (IntShiftLeft, 0), (IntShiftRight, 0),
      (IntBitwiseAnd, ~0), (IntBitwiseOr, 0), (IntBitwiseXOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, IntMul), (0, IntDiv),
      (0, IntShiftLeft), (0, IntShiftRight),
      (0, IntBitwiseAnd), (~0, IntBitwiseOr))

  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((IntMul, 0), (IntBitwiseAnd, 0), (IntBitwiseOr, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] =
  {
    case (IntBitwiseAnd | IntBitwiseOr, a) => a
    case (IntSub | IntMod | IntBitwiseXOr, _) => 0
    case (IntDiv, _) => 1
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] =
  {
    case IntLe | Eq => true
    case IntLt => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Atom]),
    Literal] = {
    case (IntAdd, Seq(IntLit(x), IntLit(y))) => x + y
    case (IntSub, Seq(IntLit(x), IntLit(y))) => x - y
    case (IntMul, Seq(IntLit(x), IntLit(y))) => x * y
    case (IntDiv, Seq(IntLit(x), IntLit(y))) if y.toInt != 0 => x / y
    case (IntMod, Seq(IntLit(x), IntLit(y))) if y.toInt != 0 => x % y

    case (IntShiftLeft, Seq(IntLit(x), IntLit(y))) => x << y
    case (IntShiftRight, Seq(IntLit(x), IntLit(y))) => x >> y
    case (IntBitwiseAnd, Seq(IntLit(x), IntLit(y))) => x & y
    case (IntBitwiseOr, Seq(IntLit(x), IntLit(y))) => x | y
    case (IntBitwiseXOr, Seq(IntLit(x), IntLit(y))) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Atom]),
    Boolean] = {
    case (IntLt, Seq(IntLit(x), IntLit(y))) => x < y
    case (IntLe, Seq(IntLit(x), IntLit(y))) => x <= y
    case (Eq, Seq(IntLit(x), IntLit(y))) => x == y
  }

  protected val equalCEvaluator: PartialFunction[TestPrimitive, Boolean] = {
    case Eq => true
    case IntLe | IntLt => false
  }
}

object FlatCPSOptimizer extends CPSOptimizer(FlatCPSTreeModule)
  with (FlatCPSTreeModule.Program => FlatCPSTreeModule.Program) {
  import treeModule._
  import CPSValuePrimitive._
  import CPSTestPrimitive._

  def apply(program: Program): Program = rewrite(program) match {
    case tree: Program => tree
    case other => LetF(Seq(), other)
  }

  protected val impure: ValuePrimitive => Boolean =
    Set(BlockSet, ByteRead, ByteWrite)

  protected val unstable: ValuePrimitive => Boolean =
    Set(BlockAlloc, BlockGet, ByteRead)

  protected val blockAlloc: ValuePrimitive = BlockAlloc
  protected val blockTag: ValuePrimitive = BlockTag
  protected val blockLength: ValuePrimitive = BlockLength
  protected val blockSet: ValuePrimitive = BlockSet
  protected val blockGet: ValuePrimitive = BlockGet

  protected val identity: ValuePrimitive = Id
  protected val byteWrite: ValuePrimitive = ByteWrite

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, Add), (1, Mul), (~0, And), (0, Or), (0, XOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((Add, 0), (Sub, 0), (Mul, 1), (Div, 1),
      (ShiftLeft, 0), (ShiftRight, 0),
      (And, ~0), (Or, 0), (XOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, Mul), (0, Div),
      (0, ShiftLeft), (0, ShiftRight),
      (0, And), (~0, Or))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((Mul, 0), (And, 0), (Or, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (And | Or, a) => a
    case (Sub | Mod | XOr, _) => 0
    case (Div, _) => 1
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case Le | Eq => true
    case Lt => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Atom]),
    Literal] = {
    case (Add, Seq(x: Literal, y: Literal)) => x + y
    case (Sub, Seq(x: Literal, y: Literal)) => x - y
    case (Mul, Seq(x: Literal, y: Literal)) => x * y
    case (Div, Seq(x: Literal, y: Literal)) if y.toInt != 0 => x / y
    case (Mod, Seq(x: Literal, y: Literal)) if y.toInt != 0 => x % y

    case (ShiftLeft,  Seq(x: Literal, y: Literal)) => x << y
    case (ShiftRight, Seq(x: Literal, y: Literal)) => x >> y
    case (And, Seq(x: Literal, y: Literal)) => x & y
    case (Or,  Seq(x: Literal, y: Literal)) => x | y
    case (XOr, Seq(x: Literal, y: Literal)) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Atom]),
    Boolean] = {
    case (Lt, Seq(x: Literal, y: Literal)) => x < y
    case (Le, Seq(x: Literal, y: Literal)) => x <= y
    case (Eq, Seq(x: Literal, y: Literal)) => x == y
  }

  protected val equalCEvaluator: PartialFunction[TestPrimitive, Boolean] = {
    case Eq => true
    case Le | Lt => false
  }
}
