package scalac_inspired
import reflect.Selectable.reflectiveSelectable

trait Types { self: Symbols =>
  trait Type
  trait TypeRef extends Type {
    def symbol: Symbol
  }
}

trait Symbols { self: Types =>
  trait Symbol {
    def typ: Type
  }
  def newSymbol: Symbol
}

object FromPDotPaperScala {
  object core {
    object types {
      trait Type
      // In DOT, to make classes nominal, they become abstract types
      class TypeRef(val symb: core.symbols.Symbol) extends Type
    }
    object symbols {
      class Symbol(val tpe : core.types.Type)
    }
  }
}

object FromPDotPaperDot {
  val core = new { core =>
    // These traits are to inline in actual pDOT, but Dotty isn't happy with the result.
    trait Types {
      type Type
      type TypeRef <: Type & {
        val symb: core.symbols.Symbol
      }

      val AnyType : Type
      val newTypeRef : core.symbols.Symbol => TypeRef
    }

    trait Symbols {
      type Symbol <: {
        val tpe : core.types.Type
        val name : String
      }
      val newSymbol: core.types.Type => String => Symbol
    }

    final val types: Types = new Types {
      type Type = Any
      type TypeRef = Type & {
        val symb: core.symbols.Symbol
      }
      val AnyType : Type = 0 // new {}
      val newTypeRef : core.symbols.Symbol => TypeRef =
        _symb => new { val symb = _symb }
    }
    final val symbols : Symbols = new {
      type Symbol = {
        val tpe : core.types.Type
        val name : String
      }
      val newSymbol: types.Type => String => Symbol = _tpe => _name => new {
        val tpe = _tpe
        val name = _name
      }
    }
  }
}
