package lc_dot
import reflect.Selectable.reflectiveSelectable

object Exprs {
  sealed trait Exp
  case class Add(lhs: Exp, rhs: Exp) extends Exp
  case class Lit(n: Int) extends Exp
  case class Fun(f: Exp => Exp) extends Exp
  case class App(f: Exp, a: Exp) extends Exp
}
import Exprs._
object Values {
  trait ValueApi {
    val asInt : () => Int
    val asFun : ValueApi => ValueApi
  }
  class IntValue(n: Int) extends ValueApi {
    val asInt = () => n
    val asFun = v => asFun(v)
  }
  class FunValue(f : ValueApi => ValueApi) extends ValueApi {
    val asInt = () => asInt()
    val asFun = f
  }
}
import Values._

object cake {

  trait Eval {
    type Val
    def evaluate: Exp => Val
  }
  trait Normalizer { self: Eval =>
    def reify: Val => Exp
    def normalize: Exp => Exp = e => reify(evaluate(e))
  }

  trait EvalImpl extends Eval { self: Normalizer =>

    type Val = Int
    def evaluate = {
      case Add(l, r) => evaluate(l) + evaluate(r)
      case Lit(n)    => n
      // case App(f, a) => evaluate(f)(evaluate(a))
      // case Fun(f)    => va => evaluate(f(normalizer.reify(va)))
    }
  }
  trait NormalizerImpl extends Normalizer { self: Eval { type Val = Int } =>
    def reify = n => Lit(n)
  }

  object lc extends EvalImpl with NormalizerImpl
}

object dotCake {
  // DOT:
  // type EvalApi = {
  //   type Val
  //   val evaluate: Exp => Val
  // }
  // type NormalizerApi = EvalApi & {
  //   def reify: Val => Exp
  //   def normalize: Exp => Exp
  // }
  trait EvalApi {
    type Val
    val evaluate: Exp => Val
  }

  //val eval : EvalApi & { type Val <: ValueApi } = new EvalApi {
  val eval : EvalApi & { type Val = ValueApi } = new EvalApi {
    type Val = ValueApi
    val evaluate: Exp => Val = {
      case Add(l, r) => IntValue(evaluate(l).asInt() + evaluate(r).asInt())
      case Lit(n)    => IntValue(n)
      case App(f, a) => evaluate(f).asFun(evaluate(a))
      case Fun(f)    => FunValue(va => evaluate(f(normalizer.reify(va))))
    }
  }

  trait NormalizerApi {
    def normalize: Exp => Exp
    def reify: eval.Val => Exp
  }

  val normalizer : NormalizerApi = new NormalizerApi {
    def normalize: Exp => Exp = e => reify(eval.evaluate(e))
    def reify = n => Lit(n.asInt())
  }
}
