package scala.scalanative
package compiler
package codegen

import java.{lang => jl}
import util.{unsupported, unreachable, sh, Show}
import util.Show.{Sequence => s, Indent => i, Unindent => ui, Repeat => r, Newline => nl}
import nir._

trait LLValGen { self: LLCodeGen =>
  import LLValGen._

  protected lazy val globals = assembly.collect {
    case Defn.Var(_, n, ty, _)     => n -> ty
    case Defn.Const(_, n, ty, _)   => n -> ty
    case Defn.Declare(_, n, sig)   => n -> sig
    case Defn.Define(_, n, sig, _) => n -> sig
  }.toMap

  def genJustVal(v: Val): Res = v match {
    case Val.True                            => "true"
    case Val.False                           => "false"
    case Val.Zero(ty)                        => "zeroinitializer"
    case Val.Undef(ty)                       => "undef"
    case Val.I8(v)                           => v.toString
    case Val.I16(v)                          => v.toString
    case Val.I32(v)                          => v.toString
    case Val.I64(v)                          => v.toString
    case Val.F32(v)                          => llvmFloatHex(v)
    case Val.F64(v)                          => llvmDoubleHex(v)
    case Val.Struct(_, vs)                   => sh"{ ${r(vs, sep = ", ")} }"
    case Val.Array(_, vs)                    => sh"[ ${r(vs, sep = ", ")} ]"
    case Val.Chars(v)                        => s("c\"", v, "\\00", "\"")
    case Val.Local(n, _) if copy.contains(n) => genJustVal(copy(n))
    case Val.Local(n, ty)                    => sh"%$n"
    case Val.Global(n, ty)                   => sh"bitcast (${globals(n)}* @$n to i8*)"
    case _                                   => unsupported(v)
  }

  implicit val genVal: Show[Val] = Show { v =>
    sh"${v.ty} ${genJustVal(v)}"
  }

  implicit val genGlobal: Show[Global] = Show { g =>
    def justGlobal(g: Global): Res = g match {
      case Global.None          => unsupported(g)
      case Global.Top(id)       => id
      case Global.Member(n, id) => s(justGlobal(n), "::", id)
    }

    quoted(justGlobal(g))
  }

  implicit val genLocal: Show[Local] = Show {
    case Local(scope, id) => sh"$scope.$id"
  }
}

object LLValGen {
  def llvmFloatHex(value: Float): String =
    "0x" + jl.Long.toHexString(jl.Double.doubleToRawLongBits(value.toDouble))

  def llvmDoubleHex(value: Double): String =
    "0x" + jl.Long.toHexString(jl.Double.doubleToRawLongBits(value))

  def quoted(sh: Res) = s("\"", sh, "\"")
}
