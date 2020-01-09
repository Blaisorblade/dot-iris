package positive

import reflect.Selectable.reflectiveSelectable
import scalaLibV._

object Positive {
  trait IPos { self =>
    type Pos <: Int
    val mkPos : Int => OptionT & { type T <: self.Pos }
    val divide : Int => Pos => Int
  }
  val Pos : IPos = new { self =>
    type Pos = Int
    val mkPos : Int => OptionT & { type T <: self.Pos } = n => {
      if (n > 0) {
        val x : { type A = self.Pos } = new { type A = self.Pos }
        mkSome(x)(n)
      } else {
        none
      }
    }
    val divide : Int => Pos => Int = m => n => m / n
  }
}
