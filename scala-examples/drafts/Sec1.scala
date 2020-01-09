package Sec1
import reflect.Selectable.reflectiveSelectable

// val pcore = new {
//   val types = new {
//     class Type
//     class TypeTop extends Type
//     // In DOT, to make classes nominal, they become abstract types
//     class TypeRef(val symb: pcore.symbols.Symbol) extends Type {
//       assert(!symb.tpe.isEmpty)
//     }
//   }
//   val symbols = new {
//     class Symbol(val tpe: Option[pcore.types.Type], val id: Int)
//     // Encapsulation violation, and type error in Scala (but not pDOT)
//     val fakeTypeRef : types.TypeRef =
//       new { val symb = newSymbol(None(), 0) }
//   }
// }

// object Foo {
//   val pcore : { pcore =>
//     val types : {
//       type Type
//       type TypeTop         <: Type
//       val  newTypeTop       : () => Type
//       type TypeRef         <: Type & { val symb: pcore.symbols.Symbol }
//       val  newTypeRef       : pcore.symbols.Symbol => TypeRef
//     }
//     val symbols : {
//       type Symbol          <: {
//         val tpe : Option & { type A = pcore.types.Type }
//         val id  : Int
//       }
//       val newSymbol         : Option & { type A = pcore.types.Type } => Int => Symbol
//     }
//   } = new {
//     val types : {
//       type Type
//       type TypeTop         <: Type
//       val  newTypeTop       : () => Type
//       type TypeRef         <: Type & { val symb: pcore.symbols.Symbol }
//       val  newTypeRef       : pcore.symbols.Symbol => TypeRef
//     } = new {
//       type Type             = Any
//       type TypeTop          = Any
//       val  newTypeTop       = new {}
//       type TypeRef          = Type & { val symb: pcore.symbols.Symbol }
//       val newTypeRef        = s => {
//         assert(!s.tpe.isEmpty)
//         new { val symb = s }
//       }
//     }
//     val symbols : {
//       type Symbol          <: {
//         val tpe : Option & { type A = pcore.types.Type }
//         val id  : Int
//       }
//       val newSymbol         : Option & { type A = pcore.types.Type } => Int => Symbol
//     } = new {
//       type Symbol           = {
//         val tpe : Option & { type A = pcore.types.Type }
//         val id  : Int
//       }
//       val newSymbol         = _tpe => _id => new { val tpe = _tpe; val id = _id }
//     }
//   }
// }



object pcore {
  object types {
    class Type
    class TypeTop extends Type
    // In DOT, to make classes nominal, they become abstract types
    class TypeRef(val symb: symbols.Symbol) extends Type {
      assert(!symb.tpe.isEmpty)
    }
  }
  object symbols {
    class Symbol(val tpe: Option[types.Type], val id: Int)
    // Encapsulation violation, and type error in Scala (but not pDOT)
    // val fakeTypeRef : types.TypeRef =
    //   new { val symb = new Symbol(None, 0) }
  }
}


// object pcore {
//   object types {
//     class Type
//     // In DOT, to make classes nominal, they become abstract types
//     class TypeRef(val symb: symbols.Symbol) extends Type
//   }
//   object symbols {
//     class Symbol(val tpe: types.Type)
//     // Encapsulation violation, and type error in Scala:
//     // val fakeTypeRef : types.TypeRef =
//     //   new { val symb = new Symbol(new types.Type()) }
//   }
// }

// val pcore = new {
//   val types = new {
//     class Type
//     class TypeInt(val bitcount: Int) extends Type
//     // In DOT, to make classes nominal, they become abstract types
//     class TypeRef(val symb: pcore.symbols.Symbol) extends Type {
//       assert(!symb.tpe.isEmpty)
//     }
//     val getTypeFromTypeRef = (t: TypeRef) =>
//       t.symb.tpe.pmatch(new TypeInt(8))(x => x)
//     val getTypeFromTypeRefUnsafe = (t: TypeRef) =>
//       // relies on TypeRef invariant; only semantically well-typed.
//       t.symb.tpe.asInstanceOf[Some[pcore.types.Type]].get
//   }
//   val symbols = new {
//     class Symbol(val tpe: Option[pcore.types.Type], val id: Nat)
//   }
// }

object options1 {
  sealed abstract class Option[T] {
    def isEmpty: Boolean
    def pmatch[U](none: U)(some: T => U): U
  }

  class None[T]() extends Option[T] {
    def isEmpty = true
    def pmatch[U](none: U)(some: T => U): U = none
  }

  class Some[T](val get: T) extends Option[T] {
    def isEmpty = false
    def pmatch[U](none: U)(some: T => U): U = some(get)
  }
}

object options2 {
  sealed abstract class Option[T] {
    val isEmpty: Boolean
    val pmatch: [U] => U => (T => U) => U
  }

  class None[T]() extends Option[T] {
    val isEmpty = true
    val pmatch: [U] => U => (T => U) => U = [U] =>
      (none: U) => (some: T => U) => none
  }

  class Some[T](val get: T) extends Option[T] {
    val isEmpty = false
    val pmatch: [U] => U => (T => U) => U = [U] =>
      (none: U) => (some: T => U) => some(get)
  }
}

object options3 {
  type Option = {
    type T
    val isEmpty: Boolean
    val pmatch: [U] => U => (T => U) => U
  }

  type None = Option { type T = Nothing }
  def mkNone[T]: None = new {
    type T = Nothing
    val isEmpty = true
    val pmatch: [U] => U => (T => U) => U = [U] => (none: U) => (some: T => U) => none
  }

  //type Some = Option & { self => val get: self.T }
  type Some = Option & { type T; val get: T }
  def mkSome[S](t: S): Some { type T = S } = new {
    type T = S
    val isEmpty = false
    val get = t
    val pmatch: [U] => U => (T => U) => U = [U] => (none: U) => (some: T => U) => some(get)
  }
}

object old {
  object pcore {
    import options1._
    object types {
      class Type
      class TypeInt(val bitcount: Int) extends Type
      // In DOT, to make classes nominal, they become abstract types
      class TypeRef(val symb: pcore.symbols.Symbol) extends Type {
        assert(!symb.tpe.isEmpty)
      }
      val getTypeFromTypeRef = (t: TypeRef) =>
        t.symb.tpe.pmatch(new TypeInt(8))(x => x)
      val getTypeFromTypeRefUnsafe = (t: TypeRef) =>
        // relies on TypeRef invariant; only semantically well-typed.
        t.symb.tpe.asInstanceOf[Some[pcore.types.Type]].get
    }
    object symbols {
      class Symbol(val tpe: Option[pcore.types.Type], val id: Int)
    }
  }
}
