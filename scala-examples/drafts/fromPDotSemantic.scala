package fromPDotMutualRecV

import reflect.Selectable.reflectiveSelectable

import typing_unstamped_derivedV._
import scalaLibV._

object fromPDotPaperV { core =>
  // These traits are to inline in actual pDOT, but Dotty isn't happy with the result.
  trait Types {
    type Type
    type TypeRef <: Type & {
      val symb: core.symbols.Symbol
    }

    val TypeTop : Later[Type]
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
    val TypeTop : Later[Type] = upcast(0) // new {}
    val newTypeRef : core.symbols.Symbol => TypeRef =
      _symb => {
        //assert(!_symb.tpe.isEmpty)
        //assert(!_symb.tpe.isEmpty)
        new { val symb = _symb }
      }
  }
  final val symbols : Symbols = new { symbols =>
    type Symbol = {
      val tpe : OptionT & { type T = core.types.Type }
      val id : Int
    }
    val newSymbol: OptionT & { type T = core.types.Type } => Int => symbols.Symbol = _tpe => _id => new {
      val tpe = _tpe
      val id = _id
    }
  }
}

//val getAnyType : (x : fromPDotPaperV.type) => x.types.Type = x => skip(x.types.TypeTop)
def getAnyType(x : fromPDotPaperV.type): x.types.Type = skip(x.types.TypeTop)

