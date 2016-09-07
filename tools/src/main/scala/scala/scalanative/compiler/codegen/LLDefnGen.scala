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
  import world.{traits, classes, methods}

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

    val blocks = Seq(
        Block(fresh(),
              Seq(argc, argv),
              Seq(Inst(rt.name, Op.Module(Rt.name)),
                  Inst(arr.name, Op.Call(initSig, init, Seq(rt, argc, argv))),
                  Inst(module.name, Op.Module(entry.top)),
                  Inst(Op.Call(mainTy, main, Seq(module, arr)))),
              Cf.Ret(Val.I32(0))))

    genFunctionDefn(Attrs.None, mainName, mainSig, blocks)
  }

  def genPrelude() = {
    ll.declare(void, scalanative_throw, Seq(i8_*), Seq())
    ll.declare(i8_*, scalanative_alloc, Seq(i8_*, i64), Seq())
    ll.declare(i32, llvm_typeid_for, Seq(i8_*), Seq())
    ll.declare(i32, gxx_personality_v0, Seq(vararg), Seq())
    ll.declare(i8_*, cxa_begin_catch, Seq(i8_*), Seq())
    ll.declare(void, cxa_end_catch, Seq(), Seq())
    ll.global(scalanative_exception_wrapper,
              sh"{ i8*, i8*, i8* }",
              s(),
              isConst = true,
              isExtern = true)
  }

  def genDefn(defn: Defn): Unit = defn match {
    case Defn.Var(attrs, name, ty, rhs) =>
      genGlobalDefn(name, ty, rhs, isExtern = attrs.isExtern, isConst = false)
    case Defn.Const(attrs, name, ty, rhs) =>
      genGlobalDefn(name, ty, rhs, isExtern = attrs.isExtern, isConst = true)
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
                    ty: nir.Type,
                    init: nir.Val,
                    isExtern: Boolean,
                    isConst: Boolean): Unit = {
    val stripped = if (isExtern) stripExtern(name) else name

    ll.global(name, ty, init, isConst, isExtern)
  }

  def genFunctionDefn(attrs: Attrs,
                      name: Global,
                      sig: Type,
                      blocks: Seq[Block]): Unit = {
    val Type.Function(argtys, retty) = sig

    val retsvoid = retty.isUnit || retty.isNothing
    val llretty  = if (retsvoid) sh"void" else retty: Res
    val llname   = if (attrs.isExtern) stripExtern(name) else name
    val llattrs  = {
      val inline =
        if (attrs.inline == Attr.MayInline) Seq() else Seq((attrs.inline: Attr): Res)
      val personality = if (attrs.isExtern) Seq() else Seq(gxxpersonality: Res)
      inline ++ personality
    }

    if (blocks.isEmpty) {
      ll.declare(llretty, llname, argtys, llattrs)
    } else {
      ll.define(llretty, llname, argtys, llattrs, genBody(blocks, retsvoid))
    }
  }

  def genStruct(name: Global, tys: Seq[Type]): Unit = {
    ll.struct(name, tys)
  }

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
    val clsTy   = Type.Class(clsName): Type
    val clsNull = Val.Zero(clsTy): Val

    val valueName = clsName tag "value"
    val valueDefn = Defn.Var(Attrs.None, valueName, clsTy, clsNull)
    val value     = Val.Global(valueName, Type.Ptr)

    ll.global(valueName, clsTy, clsNull, isConst = false, isExtern = false)
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
      if (world.nodes.contains(name tag "init")) {
        val init = genJustGlobal(name member "init")
        ll.invoke(sh"void (i8*) $init(i8* %$alloc)")
      }
      ll.ret(sh"i8* %$alloc")

      ll.endBody()
    }

    ll.define(i8_*, load, Seq(), Seq(), body)
  }

  def genTrait(trt: Trait): Unit = ()

  def genRuntimeTypeInfo(node: Node): Unit = node match {
    case cls: Class =>
      val typeDefn = Defn
        .Const(Attrs.None, cls.name tag "type", cls.typeStruct, cls.typeValue)

      genDefn(typeDefn)

    case _ =>
      val typeId  = Val.I32(node.id)
      val typeStr = Val.String(node.name.id)
      val typeVal = Val.Struct(nir.Rt.Type.name, Seq(typeId, typeStr))
      val typeDefn =
        Defn.Const(Attrs.None, node.name tag "type", nir.Rt.Type, typeVal)

      genDefn(typeDefn)
  }

  implicit def genAttrSeq: Show[Seq[Attr]] = nir.Shows.showAttrSeq
  implicit def genAttr: Show[Attr] = nir.Shows.showAttr
}

object LLDefnGen extends Depends {
  val void   = sh"void"
  val i32    = sh"i32"
  val i64    = sh"i64"
  val i8_*   = sh"i8_*"
  val vararg = sh"..."

  val scalanative_throw  = Global.Top("scalanative_throw")
  val scalanative_alloc  = Global.Top("scalanative_alloc")
  val llvm_typeid_for    = Global.Top("llvm.typeid.for")
  val gxx_personality_v0 = Global.Top("__gxx_personality_v0")
  val cxa_begin_catch    = Global.Top("__cxa_begin_catch")
  val cxa_end_catch      = Global.Top("__cxa_end_catch")
  val scalanative_exception_wrapper =
    Global.Top("_ZTIN11scalanative16ExceptionWrapperE")

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

  val unitName  = Global.Top("scala.scalanative.runtime.BoxedUnit$")
  val unit      = Val.Global(unitName, Type.Ptr)
  val unitTy    = Type.Struct(unitName, Seq(Type.Ptr))
  val unitConst = Val.Global(unitName tag "type", Type.Ptr)
  val unitValue = Val.Struct(unitTy.name, Seq(unitConst))
  val unitDefn  = Defn.Const(Attrs.None, unitName, unitTy, unitValue)

  override val depends = Seq(unitName, ObjectArray.name, Rt.name, init.name)
  override val injects = Seq(unitDefn)
}
