import scalanative.native._, stdlib._, stdio._

object Test {
  def main(args: Array[String]): Unit = {
    println("Hello, world!")
    foo()
  }

  def foo(): Unit = {
    try {
      try {
        // need to throw exc via function, so that this block won't end with unreachable instruction
        throwExc()
      } catch {
        case e: Throwable =>
          println(s"Block 1, caught: $e")
      }

      try {
        // ! this exc will be caught in the FIRST block
        throw new Exception("I'm from SECOND block")
      } catch {
        case e: IllegalArgumentException =>
          println("Block 2, should NOT catch")
      }
    } catch {
      case e: Throwable =>
        println("foo global catch")
    }

  }

  def throwExc(): Unit = {
      throw new RuntimeException("I'm from first block")
  }

}
