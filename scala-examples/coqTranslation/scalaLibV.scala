package scalaLibV
import reflect.Selectable.reflectiveSelectable

import typing_unstamped_derivedV._

type Nat = Int // Hack

type HashableString = { val hashCode_ : () => Nat }
// Notation HashableString := (μ {@ val "hashCode" : TUnit →: TNat }).

object loopDefV { self =>
  val loop : Any => Nothing = v => self.loop(v)
}
def loopTm : Nothing = loopDefV.loop(0)

/////////////////////
// Church-encoded Booleans.
/////////////////////

// First, "macros" (as their own definitions).

// Accurate translation:
//type IFT = (x : { type A }) => (t : x.A) => (f : x.A) => x.A
// Adapted to Dotty, to avoid first bug:
// type IFT = (x : { type B }) => x.B => x.B => x.B

// val iftTrue : IFT =
//   x => t => f => t
// val iftFalse : IFT =
//   x => t => f => f

// Adapted to Dotty, to avoid second bug (https://github.com/lampepfl/dotty/issues/7711):
type IFT = [A] => A => A => A

val iftTrue : IFT =
  [A] => (t : A) => (f : A) => t
val iftFalse : IFT =
  [A] => (t : A) => (f : A) => f

// What we typechecked in Coq.
object boolImplV {
  type Boolean = IFT
  val bTrue : Later[Boolean] = upcast(iftTrue)
  val bFalse : Later[Boolean] = upcast(iftFalse)
}
val boolImplV0 : {
  type Boolean <: IFT
  val bTrue : Later[Boolean]
  val bFalse : Later[Boolean]
} = boolImplV

/////////////////////
// Option type.
/////////////////////

// This is in fact a recursive type in DOT.
trait OptionT { self =>
  type T
  val isEmpty : IFT
  val pmatch : (x : { type U }) => x.U => (self.T => x.U) => x.U
}

val none : OptionT & { type T = Nothing } = new OptionT { self =>
  type T = Nothing
  val isEmpty = iftTrue
  val pmatch =
    x => none => some => none
}

// Accurate translation, but not Scala syntax
//val mkSome : ( x : { type A } ) => x.A => OptionT & { type T = x.A } & { self => val get : self.T } =
//  ???
// Adapted to Dotty:
trait SomeT extends OptionT { self =>
  val get : self.T
}
val mkSome : ( x : { type A } ) => x.A => SomeT & { type T = x.A } =
  x => content => new SomeT {
    type T = x.A
    val isEmpty = iftFalse
    val pmatch =
      x => none => some => some(skip(upcast(content)))
    val get = content
  }
