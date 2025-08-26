package l3

import l3.SymbolicCL3TreeModule as S
import l3.HighCPSTreeModule as H
import CL3Literal.*
import l3.L3TestPrimitive.Eq
import l3.L3ValuePrimitive.Id

object CL3ToCPSTranslator extends (S.Tree => H.Tree) {
  def apply(tree: S.Tree): H.Tree =
    transform(tree)(_ => H.Halt(IntLit(L3Int(0))))

  private def transform(tree: S.Tree)(ctx: H.Atom => H.Tree): H.Tree = nonTail(tree)(ctx)

  private def tail(t: S.Tree, c: Symbol)(using Position): H.Tree = {
    t match
      case S.Ident(name) => H.AppC(c, Seq(name))
      case S.Lit(lit) => H.AppC(c, Seq(lit))


      case S.Let(bindings, body) => bindings match {
        case Seq() => tail(body, c)
        case (name, value) +: bs => nonTail(value)(v => H.LetP(name, L3ValuePrimitive.Id, Seq(v), tail(S.Let(bs, body), c)))
      }
      case S.LetRec(bindings, body) => letRecImpl(bindings, body, ctx => H.AppC(c, Seq(ctx)))

      case S.App(fun, args) => stackBuild(args)(ctxs => nonTail(fun)(f => H.AppF(f, c, ctxs)))

      case S.Prim(prim: L3TestPrimitive, args) => {
        val thenName = Symbol.fresh("then")
        val elseName = Symbol.fresh("else")

        val thenCnt = H.Cnt(thenName, Seq(), H.AppC(c, Seq(BooleanLit(true))))
        val elseCnt = H.Cnt(elseName, Seq(), H.AppC(c, Seq(BooleanLit(false))))

        H.LetC(
          Seq(thenCnt, elseCnt),
          cond(t, thenName, elseName)
        )
      }

      case S.Prim(prim: L3ValuePrimitive, args) => {
        val prim2 = Symbol.fresh("prim")
        stackBuild(args)(ctxs => H.LetP(prim2, prim, ctxs, H.AppC(c, Seq(prim2)))
        )
      }

      case S.Halt(arg) => nonTail(arg)(a => H.Halt(a))
      case _ => nonTail(t)(a => H.AppC(c, Seq(a)))
  }

  private def cond(t: S.Tree, ct: Symbol, ce: Symbol)(using Position): H.Tree = {
    var _ac: Option[Symbol] = None
    def ac: Symbol = _ac match {
      case Some(ac) => ac
      case None =>
        val ac = Symbol.fresh("ac")
        _ac = Some(ac)
        ac
    }

    def letc(t1: S.Tree, ct1: Symbol, ce1: Symbol)(t2: S.Tree, ct2: Symbol, ce2: Symbol) = {
      H.LetC(
        Seq(H.Cnt(ac, Seq(), cond(t1, ct1, ce1))),
        cond(t2, ct2, ce2)
      )
    }

    t match {
      case S.If(S.Lit(BooleanLit(true)), S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))) => H.AppC(ct, Seq())
      case S.If(S.Lit(BooleanLit(false)), S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))) => H.AppC(ce, Seq())
      case S.If(S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false)), S.Lit(BooleanLit(true))) => H.AppC(ce, Seq())
      case S.If(S.Lit(BooleanLit(false)), S.Lit(BooleanLit(false)), S.Lit(BooleanLit(true))) => H.AppC(ct, Seq())

      case S.If(S.Lit(BooleanLit(true)), e2, e3) => nonTail(e2)(ctx => H.AppC(ct, Seq(ctx)))
      case S.If(S.Lit(BooleanLit(false)), e2, e3) => nonTail(e3)(ctx => H.AppC(ce, Seq(ctx)))

      case S.If(e1, S.Lit(BooleanLit(false)), S.Lit(BooleanLit(true))) => cond(e1, ce, ct)
      case S.If(e1, S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))) => cond(e1, ct, ce)

      case S.If(e1, S.Lit(BooleanLit(true)), e3) => letc(e3, ct, ce)(e1, ac, ct)
      case S.If(e1, S.Lit(BooleanLit(false)), e3) => letc(e3, ct, ce)(e1, ac, ce)

      case S.If(e1, e2, S.Lit(BooleanLit(false))) => letc(e2, ct, ce)(e1, ac, ce)
      case S.If(e1, e2, S.Lit(BooleanLit(true)))  => letc(e2, ct, ce)(e1, ac, ct)

      case S.Prim(prim: L3TestPrimitive, args) => {
        stackBuild(args)(ctx => H.If(prim, ctx, ct, ce))
      }
      case a => nonTail(a)(v => H.If(Eq, Seq(v, BooleanLit(false)), ce, ct))
    }
  }

  private def nonTail(tree: S.Tree)(ctx: H.Atom => H.Tree): H.Tree = {
    given Position = tree.pos

    tree match {

      case S.Ident(name) => ctx(name)
      case S.Lit(lit) => ctx(lit)

      case S.Let(Seq(), body) => nonTail(body)(ctx)
      case S.Let(bindings, body) =>
        body match {
          case S.Let(next, nextBody) => nonTail(S.Let(bindings ++ next, nextBody))(ctx)
          case(_) => bindings match {
            case Seq () => {
              nonTail (body) (ctx)
            }
            case (name, value) +: bs => {
              nonTail(value)(v => H.LetP(name, L3ValuePrimitive.Id, Seq(v), nonTail(S.Let(bs, body))(ctx)))
            }
          }
        }

      case S.LetRec(bindings, body) => letRecImpl(bindings, body, ctx)

      case S.If(e1, e2, e3) => {
        val c = Symbol.fresh("c")
        val r = Symbol.fresh("r")
        val thenName = Symbol.fresh("then")
        val elseName = Symbol.fresh("else")

        val thenTransform = tail(e2, c)
        val elseTransform = tail(e3, c)
        val thenCnt = H.Cnt(thenName, Seq(), thenTransform)
        val elseCnt = H.Cnt(elseName, Seq(), elseTransform)

        val topCnt = H.Cnt(c, Seq(r), ctx(r))

        H.LetC(
          Seq(topCnt, thenCnt, elseCnt),
          cond(e1, thenName, elseName)
        )
      }

      case S.App(fun, args) => {
        val ret = Symbol.fresh("app_ret")

        nonTail(fun)(f =>
          stackBuild(args, Seq(f)) { ctxs =>
            val v = Symbol.fresh("v")

            H.LetC(
              Seq(H.Cnt(ret, Seq(v), ctx(v))),
              H.AppF(ctxs.head, ret, ctxs.tail)
            )
          }
        )
      }

      case S.Prim(prim: L3TestPrimitive, args) =>
        nonTail(S.If(S.Prim(prim, args), S.Lit(BooleanLit(true)), S.Lit(BooleanLit(false))))(ctx)

      case S.Prim(prim: L3ValuePrimitive, Seq()) =>
        val prim2 = Symbol.fresh("prim")
        H.LetP(prim2, prim, Seq(), ctx(prim2))

      case S.Prim(prim: L3ValuePrimitive, args) =>
        val prim2 = Symbol.fresh("prim")
        stackBuild(args)(ctxs => H.LetP(prim2, prim, ctxs, ctx(prim2)))

      case S.Halt(arg) => nonTail(arg)(a => H.Halt(a))
    }
  }

  private def letRecImpl(bindings: Seq[S.Fun], body: S.Tree, ctx: H.Atom => H.Tree)(using Position): H.Tree = {
    val functions = bindings.map {
      case S.Fun(name, args, innerBody) =>
        val ret = Symbol.fresh("letrec_ret")

        H.Fun(name, ret, args, tail(innerBody, ret))
    }
    H.LetF(functions, nonTail(body)(ctx))
  }

  private def stackBuild(args: Seq[S.Tree], initial: Seq[H.Atom] = Seq())(builder: Seq[H.Atom] => H.Tree): H.Tree = {
    def builderFunc(args: Seq[S.Tree], diffCtxs: Seq[H.Atom]): H.Tree = {
      args match {
        case Seq() =>
          builder(diffCtxs)
        case a +: as => {
          nonTail(a)(b => builderFunc(as, diffCtxs :+ b))
        }
      }
    }

    builderFunc(args, initial)
  }
}
