package scala.scalanative
package compiler

import java.lang.System.{currentTimeMillis => time}
import java.nio.ByteBuffer
import scala.collection.mutable
import codegen.LLCodeGen
import linker.Linker
import nir._, Shows._
import nir.serialization._
import util.sh

final class Compiler(opts: Opts) {
  private lazy val entry =
    Global.Member(Global.Top(opts.entry), "main_class.ssnr.ObjectArray_unit")

  private def measure[T](label: String)(f: => T): T = {
    val start = time()
    val res   = f
    val end   = time()
    println(s"-- $label: ${end - start} ms")
    res
  }

  private lazy val passCompanions: Seq[PassCompanion] = Seq(
      pass.MainInjection,
      pass.ExternHoisting,
      pass.ModuleLowering,
      pass.RuntimeTypeInfoInjection,
      pass.StringLowering,
      pass.ConstLowering,
      pass.StackallocHoisting,
      pass.CopyPropagation)

  private lazy val (links, assembly): (Seq[Attr.Link], Seq[Defn]) =
    measure("linking") {
      val deps           = passCompanions.flatMap(_.depends).distinct
      val injects        = passCompanions.flatMap(_.injects).distinct
      val linker         = new Linker(opts.dotpath, opts.classpath)
      val (links, defns) = linker.linkClosed(entry +: deps)
      val assembly       = defns ++ injects

      if (opts.verbose) dump(assembly, ".hnir")

      (links, defns ++ injects)
    }

  private lazy val ctx = Ctx(fresh = Fresh("tx"),
                             entry = entry,
                             top = analysis.ClassHierarchy(assembly))

  private lazy val passes = passCompanions.map(_.apply(ctx))

  private def codegen(assembly: Seq[Defn]): Unit = measure("codegen") {
    def serialize(defns: Seq[Defn], bb: ByteBuffer): Unit = {
      val gen = new LLCodeGen(assembly)(ctx.top)
      gen.gen(bb)
    }
    serializeFile(serialize _, assembly, opts.outpath)
  }

  private def dump(assembly: Seq[Defn], suffix: String) = {
    def serialize(defns: Seq[Defn], bb: ByteBuffer): Unit = {
      bb.put(nir.Shows.showDefns(assembly).toString.getBytes)
    }
    serializeFile(serialize _, assembly, opts.outpath + suffix)
  }

  def apply(): Seq[Attr.Link] = measure("total") {
    def loop(assembly: Seq[Defn], passes: Seq[(Pass, Int)]): Seq[Defn] =
      passes match {
        case Seq() =>
          assembly

        case (pass, id) +: rest =>
          val nassembly = pass(assembly)
          val n         = id + 1
          val padded    = if (n < 10) "0" + n else "" + n

          loop(nassembly, rest)
      }

    codegen(measure("transformations")(loop(assembly, passes.zipWithIndex)))

    links
  }
}
