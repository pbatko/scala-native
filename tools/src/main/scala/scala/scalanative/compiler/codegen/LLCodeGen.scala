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

class LLCodeGen(val assembly: Seq[Defn])(implicit val top: Top)
    extends LLDefnGen
    with LLInstGen
    with LLTypeGen
    with LLValGen {
  type Res          = Show.Result
  type TaggedRes    = (Int, Res)
  type Buf[T]       = mutable.UnrolledBuffer[T]
  type ResBuf       = Buf[Res]
  type TaggedResBuf = Buf[TaggedRes]

  def withBuf[T: ClassTag, R](f: Buf[T] => R): R = {
    val buf = mutable.UnrolledBuffer.empty[T]
    f(buf)
  }
  def withResBuf[R](f: ResBuf => R): R             = withBuf[Res, R](f)
  def withTaggedResBuf[R](f: TaggedResBuf => R): R = withBuf[TaggedRes, R](f)

  val fresh = new Fresh("gen")

  def gen(buffer: java.nio.ByteBuffer) =
    buffer.put(genAssembly().toString.getBytes)
}
