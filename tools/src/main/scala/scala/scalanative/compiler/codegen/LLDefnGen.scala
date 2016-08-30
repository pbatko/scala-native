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
    genMain()
    ll.end()
  }

  def genMain() = {
    val mainTy =
      Type.Function(Seq(Type.Module(entry.top), ObjectArray), Type.Unit)
    val main   = Val.Global(entry, Type.Ptr)
    val argc   = Val.Local(fresh(), Type.I32)
    val argv   = Val.Local(fresh(), Type.Ptr)
    val module = Val.Local(fresh(), Type.Module(entry.top))
    val rt     = Val.Local(fresh(), Rt)
    val arr    = Val.Local(fresh(), ObjectArray)

    val blocks =
        Seq(
            Block(fresh(),
                  Seq(argc, argv),
                  Seq(Inst(rt.name, Op.Module(Rt.name)),
                      Inst(arr.name,
                           Op.Call(initSig, init, Seq(rt, argc, argv))),
                      Inst(module.name, Op.Module(entry.top)),
                      Inst(Op.Call(mainTy, main, Seq(module, arr)))),
                  Cf.Ret(Val.I32(0))))

    genFunctionDefn(Attrs.None, mainName, mainSig, blocks)
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
    case Defn.Struct(_, name @ StructRef(struct), tys) =>
      genRuntimeTypeInfo(struct)
      genStruct(name, tys)
    case Defn.Class(_, ClassRef(cls), _, _) =>
      genRuntimeTypeInfo(cls)
      genClass(cls)
    case Defn.Module(_, ClassRef(cls), _, _) =>
      genRuntimeTypeInfo(cls)
      genModule(cls)
    case Defn.Trait(_, TraitRef(trt), _) =>
      genRuntimeTypeInfo(trt)
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

  def genClass(cls: Class): Unit = {
    genStruct(cls.classStruct.name, cls.classStruct.tys)
  }

  def genModule(cls: Class): Unit = {
    genClass(cls)
    genModuleValue(cls)
    genModuleLoad(cls)
  }

  def genModuleValue(cls: Class): Unit = {
    val clsName = cls.name
    val clsTy   = Type.Class(clsName)
    val clsNull = Val.Zero(clsTy)

    val valueName = clsName tag "value"
    val valueDefn = Defn.Var(Attrs.None, valueName, clsTy, clsNull)
    val value     = Val.Global(valueName, Type.Ptr)

    genGlobalDefn(valueName, false, false, clsTy, clsNull)
  }

  def genModuleLoad(cls: Class): Unit = {
    val name = cls.name
    val load = name tag "load"
    val body = brace {
      val entry, existing, initialize, self, cond, alloc = fresh()

      val value = genJustGlobal(name tag "value")

      ll.startBody()

      ll.block(entry)
      ll.inst(self, sh"load i8*, i8** $value")
      ll.inst(cond, sh"icmp ne i8* %$self, zeroinitializer")
      ll.branch(sh"i1 %$cond", existing, initialize)

      ll.block(existing)
      ll.ret(sh"i8* %$self")

      ll.block(initialize)
      genInst(alloc, Op.Classalloc(name))
      ll.inst(sh"store i8* %$alloc, i8** $value")
      if (top.nodes.contains(name tag "init")) {
        val init = genJustGlobal(name member "init")
        ll.invoke(sh"void (i8*) $init(i8* %$alloc)")
      }
      ll.ret(sh"i8* %$alloc")

      ll.endBody()
    }

    ll.define(sh"define i8* @$load()$gxxpersonality$body")
  }

  def genTrait(trt: Trait): Unit = ()

  def genRuntimeTypeInfo(node: Node): Unit = node match {
    case cls: Class =>
      val typeDefn = Defn.Const(Attrs.None, cls.name tag "type", cls.typeStruct, cls.typeValue)

      genDefn(typeDefn)

    case _ =>
      val typeId   = Val.I32(node.id)
      val typeStr  = Val.String(node.name.id)
      val typeVal  = Val.Struct(nir.Rt.Type.name, Seq(typeId, typeStr))
      val typeDefn = Defn.Const(Attrs.None, node.name tag "type", nir.Rt.Type, typeVal)

      genDefn(typeDefn)
  }
}

object LLDefnGen extends Depends {
  val dispatchName = Global.Top("__dispatch")
  val instanceName = Global.Top("__instance")

  val ObjectArray =
    Type.Class(Global.Top("scala.scalanative.runtime.ObjectArray"))

  val Rt       = Type.Module(Global.Top("scala.scalanative.runtime.package$"))
  val initName = Rt.name member "init_i32_ptr_class.ssnr.ObjectArray"
  val initSig  = Type.Function(Seq(Rt, Type.I32, Type.Ptr), ObjectArray)
  val init     = Val.Global(initName, initSig)

  val mainName = Global.Top("main")
  val mainSig  = Type.Function(Seq(Type.I32, Type.Ptr), Type.I32)

  val unitName = Global.Top("scala.scalanative.runtime.BoxedUnit$")
  val unit     = Val.Global(unitName, Type.Ptr)
  val unitTy   = Type.Struct(unitName, Seq(Type.Ptr))
  val unitConst =
    Val.Global(unitName tag "type", Type.Ptr)
  val unitValue = Val.Struct(unitTy.name, Seq(unitConst))
  val unitDefn  = Defn.Const(Attrs.None, unitName, unitTy, unitValue)

  override val depends = Seq(unitName, ObjectArray.name, Rt.name, init.name)
  override val injects = Seq(unitDefn)
}
