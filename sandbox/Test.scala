import java.util.function.Function

import java.util.function.BiFunction
//trait BiFunction[T, U, R] {
//  self =>
//
//  def andThen[V](other: java.util.function.Function[R, V]): BiFunction[T, U, V] = {
//    if (other == null) throw new NullPointerException
//
//    new BiFunction[T, U, V] {
//      override def apply(t: T, u: U): V = {
//        val r = self.apply(t, u)
//        other.apply(r)
//
//      }
//    }
//  }
//
//  def apply(t: T, u: U): R
//
//}


object Test {
  def main(args: Array[String]): Unit = {

    val bifunction = new BiFunction[Int, String, List[String]] {
      override def apply(t: Int, u: String): List[String] = {
        List(t.toString, u)
      }
    }

    val function = new java.util.function.Function[List[String], String] {
      override def apply(t: List[String]): String = t.mkString("[", ",", "]")
    }

    val result = bifunction.andThen[String](function).apply(1, "abc")
    println(result)

  }

}
