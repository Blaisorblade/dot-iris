import reflect.Selectable.reflectiveSelectable
/* Sec. 5
*/
object IFT {
  type IFTBody = (x : { type A }) => (t : x.A, f: x.A) => x.A
  type IFT = { val if_ : IFTBody }
  val boolImpl : {
    type MBool = IFT
    val true_ : IFT
    val false_ : IFT
  } = new {
    type MBool = IFT
    // Error:
    // val true_ = new { val if_ : IFTBody = ((x : { type A }) => (t : x.A, f : x.A) => t) }
    // val true_ = new { val if_ : IFTBody = (x : { type A }) => (t : x.A, f : x.A) => t }
    // val true_ = new { val if_ : IFTBody = x => (t, f) => t }
    val true_  : IFT = new { val if_ = (x : { type A }) => (t : x.A, f : x.A) => t }
    val false_ : IFT = new { val if_ = (x : { type A }) => (t : x.A, f : x.A) => f }
  }
  val bool : {
    type MBool <: IFT
    val true_ : MBool
    val false_ : MBool
  } = boolImpl
}

object SrcLists {
  trait List[+A] {
    def isEmpty: Boolean; def head: A; def tail: List[A]
  }
  object List {
    def nil: List[Nothing] = new List[Nothing] {
      def isEmpty = true; def head = head; def tail = tail /* infinite loops */
    }
    def cons[A](hd: A, tl: List[A]) = new List[A] {
      def isEmpty = false; def head = hd; def tail = tl
    }
  }
}

object DotLists {
  val sci = new { sci =>
    // type List = {
    //   type A
    //   val isEmpty: IFT.bool.MBool
    //   val head: Unit => this.A
    //   val tail: Unit => sci.List // & {type A <: A}
    // }
    // I use a trait as a Scala-only deviation

    trait List { self =>
      type A
      val isEmpty: IFT.bool.MBool
      val head: () => this.A
      val tail: () => sci.List & { type A <: self.A }
    }

    val nil : List & { type A = Nothing } = new List {
      type A = Nothing
      val isEmpty = IFT.bool.false_
      val head = () => head()
      val tail = () => tail()
    }

    // val cons : (x: {type A}) => List & { type A = Nothing } = ???
    def cons(x: {type A})(h: x.A, t: List & { type A = x.A }): List & { type A = x.A } = new List {
      type A = x.A
      val isEmpty = IFT.bool.true_
      val head = () => h
      val tail = () => t
    }
  }
}
