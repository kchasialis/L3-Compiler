package l3

import l3.HighCPSTreeModule as H
import l3.LowCPSTreeModule as L
import l3.L3Primitive as L3
import l3.CPSValuePrimitive as CPS
import l3.CPSTestPrimitive as CPST
import CL3Literal.*
import l3.CPSValuePrimitive.BlockAlloc

import scala.collection.immutable.Seq

object CPSValueRepresenter extends (H.Tree => L.Tree) {

  private class ABuilder {
    private val _aMap = collection.mutable.Map.empty[Int, Symbol]

    def a(ct: Int): Symbol = {
      if (!_aMap.contains(ct)) {
        _aMap(ct) = Symbol.fresh(s"a$ct")
      }

      _aMap(ct)
    }
  }

  @inline
  private def wrap(output: Symbol, input: Symbol, temp: Symbol)(bodyClosure: L.Tree) = {
    L.LetP(temp, CPS.ShiftLeft, input :: 1 :: Nil,
      L.LetP(output, CPS.Add, temp :: 1 :: Nil, bodyClosure)
    )
  }

  @inline
  private def unwrap(output: Symbol, input: L.Atom)(bodyClosure: L.Tree) = {
    L.LetP(output, CPS.ShiftRight, input :: 1 :: Nil, bodyClosure)
  }

  private def defaultArgsError(args: Seq[H.Atom]): Nothing = {
    throw new Exception(s"Unexpected args: $args")
  }

  private def applyLetP(name: H.Name, prim: H.ValuePrimitive, args: Seq[H.Atom], body: H.Body) = {
    val aBuilder = new ABuilder
    def a(ct: Int): Symbol = aBuilder.a(ct)

    def converter: CPSValuePrimitive = {
      prim match {
        case L3.IntBitwiseAnd => CPS.And
        case L3.IntBitwiseOr => CPS.Or

        case L3.BlockTag => CPS.BlockTag
        case L3.BlockLength => CPS.BlockLength

        case L3.IntAdd => CPS.Add
        case L3.IntSub => CPS.Sub
        case L3.IntDiv => CPS.Div
        case L3.IntMod => CPS.Mod

        case _ => throw new Exception(s"Unexpected primitive: $prim")
      }
    }

    prim match {
      case L3.BlockAlloc => args match {
        case Seq(n, m) =>
          unwrap(a(1), rewrite(n))(
            unwrap(a(2), rewrite(m))(
              L.LetP(name, CPS.BlockAlloc, a(1) :: a(2) :: Nil, apply(body)))
          )
        case args => defaultArgsError(args)
      }

      case L3.BlockTag | L3.BlockLength => args match {
        case Seq(n) =>
          L.LetP(a(1), converter, rewrite(n) :: Nil,
            wrap(name, a(1), a(2))(apply(body))
          )
        case args => defaultArgsError(args)
      }

      case L3.BlockGet => args match {
        case Seq(n, m) =>
            unwrap(a(1), rewrite(m))(
              L.LetP(name, CPS.BlockGet, rewrite(n) :: a(1) :: Nil, apply(body)))
      }

      case L3.BlockSet => args match {
        case Seq(n, m, x) =>
          unwrap(a(1), rewrite(m))(
            L.LetP(name, CPS.BlockSet, rewrite(n) :: a(1) :: rewrite(x) :: Nil, apply(body)))
        case args => defaultArgsError(args)
      }

      case L3.IntAdd | L3.IntSub => args match {
        case Seq(n, m) =>
          val p1 = if (prim == L3.IntAdd) CPS.Add else CPS.Sub
          val p2 = if (prim == L3.IntAdd) CPS.Sub else CPS.Add

          L.LetP(a(1), p1, rewrite(n) :: rewrite(m) :: Nil,
            L.LetP(name, p2, a(1) :: 1 :: Nil, apply(body))
          )
        case args => defaultArgsError(args)
      }

      case L3.IntMul => args match {
        case Seq(n, m) =>
          L.LetP(a(1), CPS.Sub, rewrite(n) :: 1 :: Nil,
            unwrap(a(2), rewrite(m))(
              L.LetP(a(3), CPS.Mul, a(1) :: a(2) :: Nil,
                L.LetP(name, CPS.Add, a(3) :: 1 :: Nil, apply(body)))))
        case args => defaultArgsError(args)
      }

      case L3.IntDiv => args match {
        case Seq(n, m) =>
          L.LetP(a(1), CPS.Sub, rewrite(n) :: 1 :: Nil,
            L.LetP(a(2), CPS.Sub, rewrite(m) :: 1 :: Nil,
              L.LetP(a(3), CPS.Div, a(1) :: a(2) :: Nil,
                wrap(name, a(3), a(4))(apply(body))))
          )
        case args => defaultArgsError(args)
      }

      case L3.IntMod => args match {
        case Seq(n, m) =>
          // By PruDaddy's theorem, (n-1/2) % (m-1/2) = ((n-1) % (m-1)) / 2
          L.LetP(a(1), CPS.Sub, rewrite(n) :: 1 :: Nil,
            L.LetP(a(2), CPS.Sub, rewrite(m) :: 1 :: Nil,
            L.LetP(a(3), CPS.Mod, a(1) :: a(2) :: Nil,
                L.LetP(name, CPS.Or, a(3) :: 1 :: Nil, apply(body))
              )
            )
          )
        case args => defaultArgsError(args)
      }

      case L3.IntShiftLeft => args match {
        case Seq(n, m) =>
          L.LetP(a(1), CPS.Sub, rewrite(n) :: 1 :: Nil,
            unwrap(a(2), rewrite(m))(
              L.LetP(a(3), CPS.ShiftLeft, a(1) :: a(2) :: Nil,
                L.LetP(name, CPS.Add, a(3) :: 1 :: Nil, apply(body))))
          )
      }

      case L3.IntShiftRight => args match {
        case Seq(n, m) =>
          unwrap(a(1), rewrite(m))(
            L.LetP(name, CPS.ShiftRight, rewrite(n) :: a(1) :: Nil,
              L.LetP(name, CPS.Or, name :: 1 :: Nil, apply(body)
          )))
      }
      case L3.IntBitwiseAnd | L3.IntBitwiseOr => args match {
        case Seq(n, m) =>
          L.LetP(name, converter, rewrite(n) :: rewrite(m) :: Nil, apply(body))
        case args => defaultArgsError(args)
      }

      case L3.IntBitwiseXOr => args match {
        case Seq(n, m) =>
          L.LetP(a(1), CPS.XOr, rewrite(n) :: rewrite(m) :: Nil,
            L.LetP(name, CPS.Or, a(1) :: 1 :: Nil, apply(body))
          )
        case args => defaultArgsError(args)
      }

      case L3.ByteRead => args match {
        case Seq() =>
          L.LetP(a(1), CPS.ByteRead, Nil,
            wrap(name, a(1), a(2))(apply(body)))
        case args => defaultArgsError(args)
      }

      case L3.ByteWrite => args match {
          case Seq(n) =>
            unwrap(a(1), rewrite(n))(
              L.LetP(name, CPS.ByteWrite, a(1) :: Nil, apply(body)))
          case args => defaultArgsError(args)
        }

      case L3.IntToChar => args match {
        case Seq(n) =>
          L.LetP(a(1), CPS.ShiftLeft, rewrite(n) :: 2 :: Nil,
            L.LetP(name, CPS.Add, a(1) :: 2 :: Nil, apply(body)))
        case args => defaultArgsError(args)
      }

      case L3.CharToInt => args match {
        case Seq(n) =>
          L.LetP(name, CPS.ShiftRight, rewrite(n) :: 2 :: Nil, apply(body))
        case args => defaultArgsError(args)
      }

      case L3.Id => args match {
        case Seq(n) =>
          L.LetP(name, CPS.Id, rewrite(n) :: Nil, apply(body))
        case args => defaultArgsError(args)
      }
    }
  }

  private def applyIf(cond: H.TestPrimitive, args: Seq[H.Atom], thenC: H.Name, elseC: H.Name) = {
    val aBuilder = new ABuilder
    def a(ct: Int): Symbol = aBuilder.a(ct)

    cond match {
      case L3.BlockP => args match {
        case Seq(n) =>
          L.LetP(a(1), CPS.And, rewrite(n) :: 3 :: Nil,
            L.If(CPST.Eq, a(1) :: 0 :: Nil, thenC, elseC))
        case args => defaultArgsError(args)
      }

      case L3.IntP => args match {
        case Seq(n) =>
          L.LetP(a(1), CPS.And, rewrite(n) :: 1 :: Nil,
            L.If(CPST.Eq, a(1) :: 1 :: Nil, thenC, elseC))
        case args => defaultArgsError(args)
      }

      case L3.CharP => args match {
        case Seq(n) =>
          L.LetP(a(1), CPS.And, rewrite(n) :: 7 :: Nil,
            L.If(CPST.Eq, a(1) :: 6 :: Nil, thenC, elseC))
        case args => defaultArgsError(args)
      }

      case L3.BoolP => args match {
        case Seq(n) =>
          L.LetP(a(1), CPS.And, rewrite(n) :: 15 :: Nil,
            L.If(CPST.Eq, a(1) :: 10 :: Nil, thenC, elseC))
        case args => defaultArgsError(args)
      }

      case L3.UnitP => args match {
        case Seq(n) =>
          L.LetP(a(1), CPS.And, rewrite(n) :: 15 :: Nil,
            L.If(CPST.Eq, a(1) :: 2 :: Nil, thenC, elseC))
        case args => defaultArgsError(args)
      }

      case L3.IntLt => args match {
        case Seq(n, m) =>
          L.If(CPST.Lt, rewrite(n) :: rewrite(m) :: Nil, thenC, elseC)
        case args => defaultArgsError(args)
      }

      case L3.IntLe => args match {
        case Seq(n, m) =>
          L.If(CPST.Le, rewrite(n) :: rewrite(m) :: Nil, thenC, elseC)
        case args => defaultArgsError(args)
      }

      case L3.Eq => args match {
        case Seq(n, m) =>
          L.If(CPST.Eq, rewrite(n) :: rewrite(m) :: Nil, thenC, elseC)
        case args => defaultArgsError(args)
      }
    }
  }

  // Returns the set of free variables.
  private def f(tree: H.Tree): Set[Symbol] = {
    def fAtom(atom: H.Atom): Set[Symbol] = atom match {
      case n: H.Name => Set(n)
      case _ => Set.empty
    }

    tree match {
      case H.LetP(name, prim, args, b) =>
        (f(b) - name) ++ args.flatMap(fAtom)

      case H.LetC(cnts, body) =>
        f(body) ++ cnts.foldRight(Set.empty[Symbol]) { (cnt, fv) =>
          fv ++ (f(cnt.body) -- cnt.args.toSet)
        }

      case H.LetF(funs, body) =>
        val funNames = Set(funs.map(_.name): _*)
        (f(body) ++ funs.foldRight(Set.empty[Symbol]) { (fun, fv) =>
          fv ++ (f(fun.body) -- fun.args.toSet)
        }) -- funNames

      case H.AppC(cnt, args) =>
        args.flatMap(fAtom).toSet

      case H.AppF(fun, retC, args) =>
        fAtom(fun) ++ args.flatMap(fAtom)

      case H.If(cond, args, thenC, elseC) =>
        args.flatMap(fAtom).toSet

      case H.Halt(a) =>
        fAtom(a)
    }
  }

  // Substitutes the free variables in the bodies of the Tree.
  private def substitute(tree: L.Tree)(cxt: Subst[Symbol]): L.Tree = {
    def substituteAtom(a: L.Atom): L.Atom = a match {
      case n: H.Name => cxt(n)
      case _ => a
    }

    tree match {
      case L.LetP(name, prim, args, body) => L.LetP(name, prim, args.map(a => substituteAtom(a)), substitute(body)(cxt))

      case L.LetC(cnts, body) => L.LetC(cnts.map(c => L.Cnt(c.name, c.args, substitute(c.body)(cxt))), substitute(body)(cxt))

      case L.LetF(funs, body) => L.LetF(funs, substitute(body)(cxt))

      case L.AppC(cnt, args) => L.AppC(cnt, args.map(a => substituteAtom(a)))

      case L.AppF(fun, retC, args) => L.AppF(substituteAtom(fun), retC, args.map(a => substituteAtom(a)))

      case L.If(cond, args, thenC, elseC) => L.If(cond, args.map(a => substituteAtom(a)), thenC, elseC)

      case L.Halt(a) => L.Halt(substituteAtom(a))
    }
  }
  private def closedFun(fun: H.Fun): (L.Fun, Subst[Symbol], Symbol) = {
    val env1 = Symbol.fresh("env1")
    var cxt = subst[Symbol](fun.name, env1)
    val fvs = (f(fun.body) -- Set(fun.name) -- fun.args.toSet).toSeq

    def substituteFvs(body: H.Body, currentIndex: Int): L.Tree = {
      if (currentIndex >= fvs.size) {
        substitute(apply(body))(cxt)
      } else {
        val f = fvs(currentIndex)
        val v1 = Symbol.fresh("v1")
        cxt = cxt + (f -> v1)
        L.LetP(v1, CPS.BlockGet, Seq(env1, rewrite(IntLit(L3Int(currentIndex + 1)))), substituteFvs(body, currentIndex + 1))
      }
    }

    val w1 = Symbol.fresh("w1")
    (L.Fun(w1, fun.retC, Seq(env1) ++ fun.args, substituteFvs(fun.body, 0)), cxt - fun.name, w1)
  }

  private def blockSetBody(funs: Seq[H.Fun], w1s: Seq[Symbol], cxts: Seq[Subst[Symbol]], currentIndex: Int, body: H.Body): L.Tree = {
    def blockSets(name: H.Name, cxt: Seq[Symbol], cxtIdx: Int, body: L.Body): L.Body = {
      if (cxtIdx >= cxt.size) {
        body
      } else {
        L.LetP(Symbol.fresh("t2"), CPS.BlockSet, Seq(name, rewrite(IntLit(L3Int(cxtIdx + 1))), cxt(cxtIdx)),
          blockSets(name, cxt, cxtIdx + 1, body))
      }
    }
    
    if (currentIndex >= funs.size) {
      apply(body)
    } else {
      val fun = funs(currentIndex)
      val w1 = w1s(currentIndex)
      val cxt = cxts(currentIndex)
      L.LetP(Symbol.fresh("t1"), CPS.BlockSet, Seq(fun.name, 0, w1),
        blockSets(fun.name, cxt.keys.toSeq, 0, blockSetBody(funs, w1s, cxts, currentIndex + 1, body))
      )
    }
  }

  private def createClosures(funs: Seq[H.Fun], ctxs: Seq[Subst[Symbol]], currentIndex: Int, body: L.Body): L.Tree = {
    if (currentIndex >= funs.size) {
      body
    } else {
      val fun = funs(currentIndex)
      val ctx = ctxs(currentIndex)
      L.LetP(fun.name, CPS.BlockAlloc, Seq(BlockTag.Function, rewrite(IntLit(L3Int(ctx.size + 1)))),
        createClosures(funs, ctxs, currentIndex + 1, body))
    }
  }

  def apply(tree: H.Tree): L.Tree = tree match {
    case H.AppC(cnt, args) => L.AppC(cnt, args.map(rewrite))

    case H.LetP(name, prim, args, b) => applyLetP(name, prim, args, b)

    case H.LetC(cnts, body) => L.LetC(
      cnts.map {
        case H.Cnt(name, args, body) => L.Cnt(name, args, apply(body))
      },
      apply(body)
    )

    case H.AppF(fun, retC, args) => {
      val f = Symbol.fresh("f")
      val fNew = rewrite(fun)
      L.LetP(f, CPS.BlockGet, Seq(fNew, 0),
        L.AppF(f, retC, Seq(fNew) ++ args.map(rewrite))
      )
    }

    case H.LetF(funs, body) =>
      val processed = funs.map(closedFun)
      val closedFuns = processed.map(_._1)
      val ctxs = processed.map(_._2)
      val w1s = processed.map(_._3)
      val cl = createClosures(funs, ctxs, 0, blockSetBody(funs, w1s, ctxs, 0, body))
      L.LetF(closedFuns, cl)

    case H.If(cond, args, thenC, elseC) => applyIf(cond, args, thenC, elseC)

    case H.Halt(tree) => {
      val halt = Symbol.fresh("halt")
      L.LetP(halt, CPS.ShiftRight, Seq(rewrite(tree), 1), L.Halt(halt))
    }
  }

    private def rewrite(a: H.Atom): L.Atom = a match {
      case n: H.Name => n
      case IntLit(v) => (v.toInt << 1) | 1
      case CharLit(v) => (v << 3) | 6
      case BooleanLit(true) => 26
      case BooleanLit(false) => 10
      case UnitLit => 2
  }
}

