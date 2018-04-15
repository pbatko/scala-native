package java.util.function

trait BiFunction[T, U, R] {
  self =>

  def andThen[V](other: java.util.function.Function[R, V]): BiFunction[T, U, V] = {
    if (other == null) throw new NullPointerException

    new BiFunction[T, U, V] {
      override def apply(t: T, u: U): V = {
        val r = self.apply(t, u)
        other.apply(r)

      }
    }
  }

  def apply(t: T, u: U): R

}