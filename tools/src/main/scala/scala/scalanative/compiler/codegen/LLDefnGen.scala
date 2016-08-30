package scala.scalanative
package compiler
package codegen

import scala.collection.mutable
import compiler.analysis._
import ClassHierarchy._
import ClassHierarchyExtractors._
import util.{unsupported, unreachable, sh, Show}
import util.Show.{Sequence => s, Indent => i, Unindent => ui, Repeat => r, Newline => nl}
import nir._, Shows.brace

trait LLDefnGen { self: LLCodeGen =>
  import LLDefnGen._
  import top.{traits, classes, methods}

  private lazy val gxxpersonality =
    sh"personality i8* bitcast (i32 (...)* @__gxx_personality_v0 to i8*)"

  private lazy val prelude = Seq(
      (DECLARE, sh"declare void @scalanative_throw(i8*)"),
      (DECLARE, sh"declare i8* @scalanative_alloc(i8*, i64)"),
      (DECLARE, sh"declare i32 @llvm.eh.typeid.for(i8*)"),
      (DECLARE, sh"declare i32 @__gxx_personality_v0(...)"),
      (DECLARE, sh"declare i8* @__cxa_begin_catch(i8*)"),
      (DECLARE, sh"declare void @__cxa_end_catch()"),
      (CONST,
       sh"@_ZTIN11scalanative16ExceptionWrapperE = external constant { i8*, i8*, i8* }")
  )

  lazy val (dispatchTy, dispatchDefn) = {
    val traitMethods = methods.filter(_.inTrait).sortBy(_.id)

    val columns = classes.sortBy(_.id).map { cls =>
      val row = Array.fill[Val](traitMethods.length)(Val.Null)
      cls.imap.foreach {
        case (meth, value) =>
          row(meth.id) = value
      }
      Val.Array(Type.Ptr, row)
    }
    val value = Val.Array(Type.Array(Type.Ptr, traitMethods.length), columns)
    val defn  = Defn.Const(Attrs.None, dispatchName, value.ty, value)

    (value.ty, defn)
  }

  lazy val dispatch = sh"$dispatchTy* @${dispatchName: Global}"

  lazy val (instanceTy, instanceDefn) = {
    val columns = classes.sortBy(_.id).map { cls =>
      val row = new Array[Boolean](traits.length)
      cls.alltraits.foreach { trt =>
        row(trt.id) = true
      }
      Val.Array(Type.Bool, row.map(Val.Bool))
    }
    val value = Val.Array(Type.Array(Type.Bool, traits.length), columns)
    val defn  = Defn.Const(Attrs.None, instanceName, value.ty, value)

    (value.ty, defn)
  }

  lazy val instance = sh"$instanceTy* @${instanceName: Global}"

  def genAssembly(): Res = withTaggedResBuf { buf =>
    buf ++= prelude
    assembly.foreach(genDefn(buf, _))
    genDefn(buf, instanceDefn)
    genDefn(buf, dispatchDefn)

    r(buf.sortBy(_._1).map(_._2), sep = nl(""))
  }

  def genDefn(buf: TaggedResBuf, defn: Defn): Unit = defn match {
    case Defn.Var(attrs, name, ty, rhs) =>
      genGlobalDefn(buf, name, attrs.isExtern, isConst = false, ty, rhs)
    case Defn.Const(attrs, name, ty, rhs) =>
      genGlobalDefn(buf, name, attrs.isExtern, isConst = true, ty, rhs)
    case Defn.Declare(attrs, name, sig) =>
      genFunctionDefn(buf, attrs, name, sig, Seq())
    case Defn.Define(attrs, name, sig, blocks) =>
      genFunctionDefn(buf, attrs, name, sig, blocks)
    case Defn.Struct(_, name, tys) =>
      genStruct(buf, name, tys)
    case Defn.Class(_, ClassRef(cls), _, _) =>
      genClass(buf, cls)
    case Defn.Trait(_, TraitRef(trt), _) =>
      genTrait(buf, trt)
    case defn =>
      unsupported(defn)
  }

  def genGlobalDefn(buf: TaggedResBuf,
                    name: nir.Global,
                    isExtern: Boolean,
                    isConst: Boolean,
                    ty: nir.Type,
                    rhs: nir.Val): Unit = {
    val external = if (isExtern) "external " else ""
    val keyword  = if (isConst) "constant" else "global"
    val tag      = if (isConst) CONST else GLOBAL
    val init = rhs match {
      case Val.None => sh"$ty"
      case _        => sh"$rhs"
    }

    buf += ((tag, sh"@$name = $external$keyword $init"))
  }

  def genFunctionDefn(buf: TaggedResBuf,
                      attrs: Attrs,
                      name: Global,
                      sig: Type,
                      blocks: Seq[Block]): Unit = {
    val Type.Function(argtys, retty) = sig

    val isDecl  = blocks.isEmpty
    val keyword = if (isDecl) "declare" else "define"
    val tag     = if (isDecl) DECLARE else DEFINE
    val params =
      if (isDecl) r(argtys, sep = ", ")
      else r(blocks.head.params: Seq[Val], sep = ", ")
    val postattrs: Seq[Attr] =
      if (attrs.inline != Attr.MayInline) Seq(attrs.inline) else Seq()
    val personality = if (attrs.isExtern || isDecl) s() else gxxpersonality
    val body: Res =
      if (isDecl) s()
      else {
        s(" ", brace(r(genBlocks(blocks))))
      }

    buf += ((tag,
             sh"$keyword $retty @$name($params)$postattrs$personality$body"))
  }

  def genStruct(buf: TaggedResBuf, name: Global, tys: Seq[Type]): Unit =
    buf += ((STRUCT, sh"%$name = type {${r(tys, sep = ", ")}}"))

  def genClass(buf: TaggedResBuf, cls: Class): Unit =
    genStruct(buf, cls.classStruct.name, cls.classStruct.tys)

  def genTrait(buf: TaggedResBuf, trt: Trait): Unit = ()
}

object LLDefnGen {
  val dispatchName = Global.Top("__dispatch")
  val instanceName = Global.Top("__instance")

  final val STRUCT  = 1
  final val CONST   = 2
  final val GLOBAL  = 3
  final val DECLARE = 4
  final val DEFINE  = 5
}
