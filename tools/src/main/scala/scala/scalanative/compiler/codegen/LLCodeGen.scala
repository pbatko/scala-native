package scala.scalanative
package compiler
package codegen

import java.{lang => jl}
import scala.collection.mutable
import scala.reflect.ClassTag
import util.{unsupported, unreachable, sh, Show}
import util.Show.{Sequence => s, Indent => i, Unindent => ui, Repeat => r, Newline => nl}
import compiler.analysis._
import ClassHierarchy.{Top, Class, Trait}
import ClassHierarchyExtractors._
import ControlFlow.{Graph => CFG}
import nir.Shows.brace
import nir._

class LLCodeGen(val assembly: Seq[Defn], val entry: Global)(implicit val top: Top)
    extends LLDefnGen
    with LLInstGen
    with LLTypeGen
    with LLValGen {
  type Res = Show.Result

  implicit val fresh = new Fresh("gen")
  val ll             = new LLBuilder(fresh)

  def gen(buffer: java.nio.ByteBuffer) =
    buffer.put(genAssembly().toString.getBytes)
}
