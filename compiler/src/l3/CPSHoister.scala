package l3

import l3.LowCPSTreeModule as L
import l3.FlatCPSTreeModule as F

import scala.annotation.tailrec

object CPSHoister extends (L.Program => F.Program) {
  def apply(tree: L.Tree): F.Program = tree match {
    case L.LetP(name, prim, args, body) =>
      val letfBody = apply(body)
      F.LetF(letfBody.funs, F.LetP(name, prim, args, letfBody.body))

    case L.LetC(cnts, body) =>
      @tailrec
      def getNewCnts(cnts: Seq[L.Cnt], newCnts: Seq[F.Cnt], newFuns: Seq[Seq[F.Fun]]): (Seq[F.Cnt], Seq[Seq[F.Fun]]) = cnts match {
        case Seq() =>
          (newCnts, newFuns)
        case cnt +: rest =>
          val letfCnt = apply(cnt.body)
          getNewCnts(rest, newCnts :+ F.Cnt(cnt.name, cnt.args, letfCnt.body), newFuns :+ letfCnt.funs)
      }

      val (newCnts, newFuns) = getNewCnts(cnts, Seq(), Seq())
      val letfBody = apply(body)
      F.LetF(newFuns.flatten ++ letfBody.funs, F.LetC(newCnts, letfBody.body))

    case L.LetF(funs, body) =>
      @tailrec
      def getNewFuns(funs: Seq[L.Fun], newFuns: Seq[Seq[F.Fun]], newLetFuns: Seq[F.Fun]): (Seq[Seq[F.Fun]], Seq[F.Fun]) = funs match {
        case Seq() =>
          (newFuns, newLetFuns)
        case fun +: rest =>
          val letfFun = apply(fun.body)
          getNewFuns(rest, newFuns :+ letfFun.funs, newLetFuns :+ F.Fun(fun.name, fun.retC, fun.args, letfFun.body))
      }

      val (newFuns, newLetFuns) = getNewFuns(funs, Seq(), Seq())
      val letfBody = apply(body)
      F.LetF(newLetFuns ++ newFuns.flatten ++ letfBody.funs, letfBody.body)

    case L.AppC(cnt, args) => F.LetF(Seq(), F.AppC(cnt, args))
    case L.AppF(fun, retC, args) => F.LetF(Seq(), F.AppF(fun, retC, args))
    case L.If(cond, args, thenC, elseC) => F.LetF(Seq(), F.If(cond, args, thenC, elseC))
    case L.Halt(arg) => F.LetF(Seq(), F.Halt(arg))
  }
}
