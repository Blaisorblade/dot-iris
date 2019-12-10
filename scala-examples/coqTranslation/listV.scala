package listV

import reflect.Selectable.reflectiveSelectable

import typing_unstamped_derivedV._
import scalaLibV._

val bTrue : boolImplV.Boolean = skip(boolImplV.bTrue)
val bFalse : boolImplV.Boolean = skip(boolImplV.bFalse)

// type list = {
//   type A // this crashes Dotty here (but not elsewhere???)
//   val isEmpty : Any => boolImplV0.Boolean
//   val head : Any => A
// }

object sci { sci =>
  trait List { self =>
    type A
    val isEmpty : Any => boolImplV.Boolean
    val head : Any => A
    val tail : Any => sci.List & { type A <: self.A }
  }
  val nil : Later[sci.List] & { type A = Nothing } =
    upcast(new List {
      type A = Nothing
      val isEmpty = _ => bTrue
      val head = _ => loopTm
      val tail = _ => loopTm
    })
  val cons : (x : { type T } ) => x.T => sci.List & { type A <: x.T } => sci.List & { type A <: x.T } =
    x => hd => tl => new List {
      type A = x.T
      val isEmpty = _ => bFalse
      val head = _ => hd
      val tail = _ => tl
    }
}

// upcasts here are spurious
val headCons: Nat = skip(upcast(skip(upcast({
  val a : { type T = Nat } = new { type T = Nat }
  // These bindings are extra annotations
  // val x0 : Later[sci.List] & { type A = Nothing } = sci.nil
  // val x1 : sci.List & { type A = Nothing } = skip(x0)
  // val x2 : sci.List & { type A <: a.T } = x1
  // val res0 : sci.List & { type A <: a.T } = sci.cons(a)(0)(x2)
  // val res : sci.List & { type A <: Nat } = skip(upcast(res0))
  // Binding res is needed in DOT.
  val res : sci.List & { type A <: Nat } = skip(upcast(sci.cons(a)(0)(skip(sci.nil))))
  res
}.head(0)))))
