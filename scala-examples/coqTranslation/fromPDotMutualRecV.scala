package fromPDotMutualRecV

import reflect.Selectable.reflectiveSelectable

import typing_unstamped_derivedV._
import scalaLibV._

//Workaround Dotty bug
//type HashableString = { val hashCode : () => Nat }
abstract class HashableString { val hashCode_ : () => Nat }

object fromPDotPaperV { core =>
  // These traits are to inline in actual pDOT, but Dotty isn't happy with the result.
  trait Types {
    type Type
    type TypeRef <: Type & {
      val symb: core.symbols.Symbol
    }

    val AnyType : Later[Type]
    val newTypeRef : core.symbols.Symbol => TypeRef
  }

  trait Symbols {
    type Symbol <: {
      val tpe : core.types.Type
      val name : HashableString
    }
    val newSymbol: core.types.Type => HashableString => Symbol
  }

  final val types: Types = new Types { types =>
    type Type = Any
    type TypeRef = types.Type & {
      val symb: core.symbols.Symbol
    }
    val AnyType : Later[Type] = upcast(0) // new {}
    val newTypeRef : core.symbols.Symbol => TypeRef =
      _symb => new { val symb = _symb }
  }
  final val symbols : Symbols = new {
    type Symbol = {
      val tpe : core.types.Type
      val name : HashableString
    }
    val newSymbol: types.Type => HashableString => Symbol = _tpe => _name => new {
      val tpe = _tpe
      val name = _name
    }
  }
}

//val getAnyType : (x : fromPDotPaperV.type) => x.types.Type = x => skip(x.types.AnyType)
def getAnyType(x : fromPDotPaperV.type): x.types.Type = skip(x.types.AnyType)

