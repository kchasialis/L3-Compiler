package l3

import l3.FlatCPSTreeModule as F

object CPSProgramPrinter extends (F.Program => F.Program) {

  def apply(prog: F.Program): F.Program = {
    println("Program:")
    println("  Functions:")
    prog.funs.foreach { case F.Fun(name, retC, args, body) =>
      println(s"    $name:")
      println(s"      return continuation: $retC")
      println(s"      arguments: $args")
      println(s"      body:")
      println(s"        $body")
    }
    println("  Main:")
    println(s"    ${prog.body}")
    prog
  }
}