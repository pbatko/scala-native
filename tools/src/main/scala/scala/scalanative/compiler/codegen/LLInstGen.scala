package scala.scalanative
package compiler
package codegen

import scala.collection.mutable
import util.{unsupported, unreachable, sh, Show}
import util.Show.{Sequence => s, Indent => i, Unindent => ui, Repeat => r, Newline => nl}
import nir._
import compiler.analysis._
import ClassHierarchy._
import ClassHierarchyExtractors._
import ControlFlow.{Graph => CFG}

trait LLInstGen { self: LLCodeGen =>
  import LLInstGen._
  import self.{instanceTy => ity, instance => ival, dispatchTy => dty, dispatch => dval}

  private lazy val ty = genType(Rt.Type)

  protected lazy val copy = mutable.Map.empty[Local, Val]

  def genBlocks(blocks: Seq[Block]): Seq[Res] = {
    implicit val cfg = ControlFlow(blocks)

    val blockshows = genBlocks(cfg)
    val landingpadshows: Seq[Res] = cfg.map { node =>
      node.block match {
        case Block(n, _, _, cf: Cf.Try) => genLandingPad(n, cf)
        case _                          => Seq()
      }
    }.flatten
    copy.clear

    blockshows ++ landingpadshows
  }

  private def genBlocks(implicit cfg: CFG): Seq[Res] = {
    val nodes = cfg.toSeq
    val insts = nodes.map { node =>
      val Block(_, _, insts, cf) = node.block
      r(genInsts(insts, cf).map(i(_)))
    }

    insts.zip(nodes).map {
      case (insts, node) =>
        val Block(name, params, _, _) = node.block

        val pred    = node.pred
        val isEntry = node eq cfg.entry
        val phis = if (isEntry) {
          Seq()
        } else {
          val preds = pred.map {
            case ControlFlow.Edge(from, _, _: Next.Case) =>
              (sh"%${from.block.name}", Seq())
            case ControlFlow.Edge(from, _, Next.Label(_, vals)) =>
              (sh"%${from.block.name}", vals.map(genJustVal))
            case ControlFlow.Edge(from, _, ctch: Next.Catch) =>
              val n = from.block.cf.asInstanceOf[Cf.Try].catches.indexOf(ctch)
              (sh"%${from.block.name}.catch.$n",
               Seq(sh"%${from.block.name}.exc"))
          }

          params.zipWithIndex.map {
            case (Val.Local(name, ty), n) =>
              val froms = preds.map {
                case (from, shows) =>
                  sh"[${shows(n)}, $from]"
              }

              i(sh"%$name = phi $ty ${r(froms, sep = ", ")}")
          }
        }

        sh"${nl(name)}:${r(phis)}$insts"
    }
  }

  private def genLandingPad(in: Local, cf: Cf.Try)(
      implicit cfg: CFG): Seq[Res] = {
    val landingpad      = sh"$in.landingpad"
    val resume          = sh"$in.resume"
    val exc             = sh"$in.exc"
    val rec, rec0, rec1 = fresh()
    val recid, reccmp   = fresh()
    val wrap0, wrap1    = fresh()

    val fails = cf.catches.drop(1).map(ctch => sh(ctch.name)) :+ resume
    val catches = cf.catches
      .zip(fails)
      .zipWithIndex
      .collect {
        case ((Next.Catch(ty, succ), fail), n) =>
          val catchn = sh"$in.catch.$n"
          val cond   = fresh()

          Seq(
              Seq(
                  nl(sh"$catchn:")
              ),
              withResBuf { buf =>
                genIs(buf, sh"%$cond =", ty, sh"i8* %$exc")
                buf.map(i(_))
              },
              Seq(
                  i(sh"br i1 %$cond, label %$catchn.succ, label %$fail"),
                  nl(sh"$catchn.succ:"),
                  i(sh"call i8* @__cxa_begin_catch(i8* %$rec0)"),
                  i(sh"call void @__cxa_end_catch()"),
                  i(sh"br label %$succ")
              )
          ).flatten
      }
      .flatten

    Seq(
        nl(sh"$landingpad:"),
        i(sh"%$rec = ${LLInstGen.landingpad}"),
        i(sh"%$rec0 = extractvalue $excrecty %$rec, 0"),
        i(sh"%$rec1 = extractvalue $excrecty %$rec, 1"),
        i(sh"%$recid = $typeid"),
        i(sh"%$reccmp = icmp eq i32 %$rec1, %$recid"),
        i(sh"%$wrap0 = bitcast i8* %$rec0 to i8**"),
        i(sh"%$wrap1 = getelementptr i8*, i8** %$wrap0, i32 1"),
        i(sh"%$exc = load i8*, i8** %$wrap1"),
        i(sh"br i1 %$reccmp, label %$in.catch.0, label %$resume"),
        nl(sh"$resume:"),
        i(sh"resume $excrecty %$rec")
    ) ++ catches
  }

  def genInsts(insts: Seq[Inst], cf: Cf)(implicit cfg: CFG): Seq[Res] =
    withResBuf { buf =>
      insts.foreach { inst =>
        genInst(buf, inst.name, inst.op)
      }
      genCf(buf, cf)
      buf
    }

  def genInst(buf: ResBuf, name: Local, op: Op): Unit = {
    val bind = if (isVoid(op.resty)) s() else sh"%$name = "

    op match {
      case op @ Op.Call(_, Val.Local(n, _), _) if copy.contains(n) =>
        genInst(buf, name, op.copy(ptr = copy(n)))

      case Op.Call(ty, Val.Global(pointee, _), args) =>
        buf += sh"${bind}call $ty @$pointee(${r(args, sep = ", ")})"

      case Op.Call(ty, ptr, args) =>
        val pointee = fresh()

        buf += sh"%$pointee = bitcast $ptr to $ty*"
        buf += sh"${bind}call $ty %$pointee(${r(args, sep = ", ")})"

      case Op.Load(ty, ptr) =>
        val pointee = fresh()

        buf += sh"%$pointee = bitcast $ptr to $ty*"
        buf += sh"${bind}load $ty, $ty* %$pointee"

      case Op.Store(ty, ptr, value) =>
        val pointee = fresh()

        buf += sh"%$pointee = bitcast $ptr to $ty*"
        buf += sh"${bind}store $value, $ty* %$pointee"

      case Op.Elem(ty, ptr, indexes) =>
        val pointee = fresh()
        val derived = fresh()

        buf += sh"%$pointee = bitcast $ptr to $ty*"
        buf +=
        sh"%$derived = getelementptr $ty, $ty* %$pointee, ${r(indexes, sep = ", ")}"
        buf +=
        sh"${bind}bitcast ${ty.elemty(indexes.tail)}* %$derived to i8*"

      case Op.Stackalloc(ty, n) =>
        val pointee = fresh()
        val elems   = if (n == Val.None) sh"" else sh", $n"

        buf += sh"%$pointee = alloca $ty$elems"
        buf += sh"${bind}bitcast $ty* %$pointee to i8*"

      case Op.Extract(aggr, indexes) =>
        buf += sh"${bind}extractvalue $aggr, ${r(indexes, sep = ", ")}"

      case Op.Insert(aggr, value, indexes) =>
        buf += sh"${bind}insertvalue $aggr, $value, ${r(indexes, sep = ", ")}"

      case Op.Bin(opcode, ty, l, r) =>
        val bin = opcode match {
          case Bin.Iadd => "add"
          case Bin.Isub => "sub"
          case Bin.Imul => "mul"
          case _        => opcode.toString.toLowerCase
        }

        buf += sh"${bind}$bin $l, ${genJustVal(r)}"

      case Op.Comp(opcode, ty, l, r) =>
        val cmp = opcode match {
          case Comp.Ieq => "icmp eq"
          case Comp.Ine => "icmp ne"
          case Comp.Ult => "icmp ult"
          case Comp.Ule => "icmp ule"
          case Comp.Ugt => "icmp ugt"
          case Comp.Uge => "icmp uge"
          case Comp.Slt => "icmp slt"
          case Comp.Sle => "icmp sle"
          case Comp.Sgt => "icmp sgt"
          case Comp.Sge => "icmp sge"
          case Comp.Feq => "fcmp ueq"
          case Comp.Fne => "fcmp une"
          case Comp.Flt => "fcmp ult"
          case Comp.Fle => "fcmp ule"
          case Comp.Fgt => "fcmp ugt"
          case Comp.Fge => "fcmp uge"
        }

        buf += sh"${bind}$cmp $l, ${genJustVal(r)}"

      case Op.Conv(name, ty, v) =>
        buf += sh"${bind}$name $v to $ty"

      case Op.Select(cond, v1, v2) =>
        buf += sh"${bind}select $cond, $v1, $v2"

      case Op.Classalloc(ClassRef(cls)) =>
        val size  = fresh()
        val clsty = cls.typeConst

        genInst(buf, size, Op.Sizeof(cls.classStruct))
        buf += sh"${bind}call i8* @scalanative_alloc($clsty, i64 %$size)"

      case Op.Field(ty, obj, FieldRef(cls: Class, fld)) =>
        val typtr, fieldptr = fresh()
        val ty              = cls.classStruct: Type
        val index           = sh"i32 ${fld.index + 1}"

        buf += sh"%$typtr = bitcast $obj to $ty*"
        buf += sh"%$fieldptr = getelementptr $ty, $ty* %$typtr, i32 0, $index"
        buf += sh"${bind}bitcast ${fld.ty}* %$fieldptr to i8*"

      case Op.Method(sig, obj, MethodRef(cls: Class, meth))
          if meth.isVirtual =>
        val typtrptr, typtr, methptrptr = fresh()

        val ty    = cls.typeStruct: Type
        val index = sh"i32 ${meth.vindex}"

        buf += sh"%$typtrptr = bitcast $obj to $ty**"
        buf += sh"%$typtr = load $ty*, $ty** %$typtrptr"
        buf += sh"%$methptrptr = getelementptr $ty, $ty* %$typtr, i32 0, i32 2, $index"
        buf += sh"${bind}load i8*, i8** %$methptrptr"

      case Op.Method(sig, obj, MethodRef(_: Class, meth)) if meth.isStatic =>
        copy(name) = Val.Global(meth.name, Type.Ptr)

      case Op.Method(sig, obj, MethodRef(trt: Trait, meth)) =>
        val typtrptr, typtr, idptr, id, methptrptr = fresh()

        val mid = sh"i32 ${meth.id}"

        buf += sh"%$typtrptr = bitcast $obj to $ty**"
        buf += sh"%$typtr = load $ty*, $ty** %$typtrptr"
        buf += sh"%$idptr = getelementptr $ty, $ty* %$typtr, i32 0, i32 0"
        buf += sh"%$id = load i32, i32* %$idptr"
        buf += sh"%$methptrptr = getelementptr $dty, $dval, i32 0, i32 %$id, $mid"
        buf += sh"${bind}load i8*, i8** %$methptrptr"

      case Op.Sizeof(ty) =>
        val elem = fresh()

        buf += sh"%$elem = getelementptr $ty, $ty* null, i32 1"
        buf += sh"${bind}ptrtoint $ty* %$elem to i64"

      case Op.Is(ty, value) =>
        genIs(buf, bind, ty, genVal(value))

      case Op.As(ty1, Of(v, ty2)) if ty1 == ty2 =>
        copy(name) = v

      case Op.As(_: Type.RefKind, Of(v, _: Type.RefKind)) =>
        copy(name) = v

      case Op.As(to @ Type.I(w1), Of(v, Type.I(w2))) if w1 > w2 =>
        buf += sh"${bind}sext $v to ${to: Type}"

      case Op.As(to @ Type.I(w1), Of(v, Type.I(w2))) if w1 < w2 =>
        buf += sh"${bind}trunc $v to ${to: Type}"

      case Op.As(to @ Type.I(_), Of(v, Type.F(_))) =>
        buf += sh"${bind}fptosi $v to ${to: Type}"

      case Op.As(to @ Type.F(_), Of(v, Type.I(_))) =>
        buf += sh"${bind}sitofp $v to ${to: Type}"

      case Op.As(to @ Type.F(w1), Of(v, Type.F(w2))) if w1 > w2 =>
        buf += sh"${bind}fpext $v to ${to: Type}"

      case Op.As(to @ Type.F(w1), Of(v, Type.F(w2))) if w1 < w2 =>
        buf += sh"${bind}fptrunc $v to ${to: Type}"

      case Op.As(Type.Ptr, Of(v, _: Type.RefKind)) =>
        buf += sh"${bind}bitcast $v to i8*"

      case Op.As(to @ (_: Type.RefKind), Of(v, Type.Ptr)) =>
        buf += sh"${bind}bitcast $v to ${to: Type}"

      case op =>
        unsupported(op)
    }
  }

  def genIs(buf: ResBuf, bind: Res, ofty: Type, obj: Res): Unit = ofty match {
    case ClassRef(cls) =>
      val typtrptr, typtr = fresh()

      buf += sh"%$typtrptr = bitcast $obj to $ty**"
      buf += sh"%$typtr = load $ty*, $ty** %$typtrptr"

      if (cls.range.length == 1) {
        val typtr1 = fresh()

        buf += sh"%$typtr1 = bitcast $ty* %$typtr to i8*"
        buf += sh"${bind}icmp eq i8* %$typtr1, ${genJustVal(cls.typeConst)}"

      } else {
        val idptr, id, ge, le = fresh()

        buf += sh"%$idptr = getelementptr $ty, $ty* %$typtr, i32 0, i32 0"
        buf += sh"%$id = load i32, i32* %$idptr"
        buf += sh"%$ge = icmp sle i32 ${cls.range.start}, %$id"
        buf += sh"%$le = icmp sle i32 %$id, ${cls.range.end}"
        buf += sh"${bind}and i1 %$ge, %$le"
      }

    case TraitRef(trt) =>
      val typtrptr, typtr, idptr, id, boolptr = fresh()

      buf += sh"%$typtrptr = bitcast $obj to $ty**"
      buf += sh"%$typtr = load $ty*, $ty** %$typtrptr"
      buf += sh"%$idptr = getelementptr $ty, $ty* %$typtr, i32 0, i32 0"
      buf += sh"%$id = load i32, i32* %$idptr"
      buf += sh"%$boolptr = getelementptr $ity, $ival, i32 0, i32 %$id, i32 ${trt.id}"
      buf += sh"${bind}load i1, i1* %$boolptr"
  }

  def genCf(buf: ResBuf, cf: Cf)(implicit cfg: CFG) =
    cf match {
      case Cf.Unreachable =>
        buf += "unreachable"

      case Cf.Ret(Val.None) =>
        buf += sh"ret void"

      case Cf.Ret(value) =>
        buf += sh"ret $value"

      case Cf.Jump(next) =>
        buf += sh"br $next"

      case Cf.If(cond, thenp, elsep) =>
        buf += sh"br $cond, $thenp, $elsep"

      case Cf.Switch(scrut, default, cases) =>
        buf += sh"switch $scrut, $default [${r(cases.map(i(_)))}${nl("]")}"

      case Cf.Throw(value) =>
        buf += sh"call void @scalanative_throw($value)"
        buf += sh"unreachable"

      case Cf.Try(default, cases) =>
        buf += sh"br $default"

      case cf =>
        unsupported(cf)
    }

  implicit val genNext: Show[Next] = Show {
    case Next.Case(v, n) => sh"$v, label %$n"
    case next            => sh"label %${next.name}"
  }

  implicit def genConv: Show[Conv] = nir.Shows.showConv

  implicit def genAttrSeq: Show[Seq[Attr]] = nir.Shows.showAttrSeq
}

object LLInstGen {
  val excrecty = sh"{ i8*, i32 }"

  val landingpad =
    sh"landingpad { i8*, i32 } catch i8* bitcast ({ i8*, i8*, i8* }* @_ZTIN11scalanative16ExceptionWrapperE to i8*)"

  val typeid =
    sh"call i32 @llvm.eh.typeid.for(i8* bitcast ({ i8*, i8*, i8* }* @_ZTIN11scalanative16ExceptionWrapperE to i8*))"

  def isVoid(ty: Type): Boolean =
    ty == Type.Void || ty == Type.Unit || ty == Type.Nothing

  object Of {
    def unapply(v: Val): Some[(Val, Type)] = Some((v, v.ty))
  }
}
