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

  /** Strips "extern." suffix from the given global. */
  protected def stripExtern(n: Global): Global = {
    val id = n.id
    assert(id.startsWith("extern."))
    Global.Top(id.substring(7))
  }

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

  lazy val dispatch = sh"$dispatchTy* @${dispatchName: Global}"
  lazy val instance = sh"$instanceTy* @${instanceName: Global}"

  def genAssembly(): Res = {
    ll.start()
    genPrelude()
    assembly.foreach(genDefn(_))
    genDefn(instanceDefn)
    genDefn(dispatchDefn)
    ll.end()
  }

  def genPrelude() = {
    ll.declare(sh"declare void @scalanative_throw(i8*)")
    ll.declare(sh"declare i8* @scalanative_alloc(i8*, i64)")
    ll.declare(sh"declare i32 @llvm.eh.typeid.for(i8*)")
    ll.declare(sh"declare i32 @__gxx_personality_v0(...)")
    ll.declare(sh"declare i8* @__cxa_begin_catch(i8*)")
    ll.declare(sh"declare void @__cxa_end_catch()")
    ll.const(
        sh"@_ZTIN11scalanative16ExceptionWrapperE = external constant { i8*, i8*, i8* }")
  }

  def genDefn(defn: Defn): Unit = defn match {
    case Defn.Var(attrs, name, ty, rhs) =>
      genGlobalDefn(name, attrs.isExtern, isConst = false, ty, rhs)
    case Defn.Const(attrs, name, ty, rhs) =>
      genGlobalDefn(name, attrs.isExtern, isConst = true, ty, rhs)
    case Defn.Declare(attrs, name, sig) =>
      genFunctionDefn(attrs, name, sig, Seq())
    case Defn.Define(attrs, name, sig, blocks) =>
      genFunctionDefn(attrs, name, sig, blocks)
    case Defn.Struct(_, name, tys) =>
      genStruct(name, tys)
    case Defn.Class(_, ClassRef(cls), _, _) =>
      genClass(cls)
    case Defn.Trait(_, TraitRef(trt), _) =>
      genTrait(trt)
    case defn =>
      unsupported(defn)
  }

  def genGlobalDefn(name: nir.Global,
                    isExtern: Boolean,
                    isConst: Boolean,
                    ty: nir.Type,
                    rhs: nir.Val): Unit = {
    val stripped = if (isExtern) stripExtern(name) else name
    val external = if (isExtern) "external " else ""
    val keyword  = if (isConst) "constant" else "global"
    val init = rhs match {
      case Val.None => sh"$ty"
      case _        => sh"$rhs"
    }
    val res = sh"@$stripped = $external$keyword $init"

    if (isConst) ll.const(res) else ll.global(res)
  }

  def genFunctionDefn(attrs: Attrs,
                      name: Global,
                      sig: Type,
                      blocks: Seq[Block]): Unit = {
    val Type.Function(argtys, retty) = sig

    val returnsVoid = retty.isUnit || retty.isNothing
    val stripped    = if (attrs.isExtern) stripExtern(name) else name
    val isDecl      = blocks.isEmpty
    val keyword     = if (isDecl) "declare" else "define"
    val tag         = if (isDecl) DECLARE else DEFINE
    val params =
      if (isDecl) r(argtys, sep = ", ")
      else r(blocks.head.params: Seq[Val], sep = ", ")
    val postattrs: Seq[Attr] =
      if (attrs.inline != Attr.MayInline) Seq(attrs.inline) else Seq()
    val personality = if (attrs.isExtern || isDecl) s() else gxxpersonality
    val body: Res =
      if (isDecl) s()
      else {
        s(" ", brace(genBody(blocks, returnsVoid)))
      }
    val ret = if (returnsVoid) sh"void" else retty: Res
    val res = sh"$keyword $ret @$stripped($params)$postattrs$personality$body"

    if (isDecl) ll.declare(res) else ll.define(res)
  }

  def genStruct(name: Global, tys: Seq[Type]): Unit =
    ll.struct(sh"%$name = type {${r(tys, sep = ", ")}}")

  def genClass(cls: Class): Unit =
    genStruct(cls.classStruct.name, cls.classStruct.tys)

  def genTrait(trt: Trait): Unit = ()
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
