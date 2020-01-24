package typing_unstamped_derivedV
import reflect.Selectable.reflectiveSelectable

// We use this here to simulate skips in the code.
object LaterUtils {
  opaque type Later[A] = A
  def skip[A](x: Later[A]): x.type & A = x

  // Beware that upcast might not correspond to an upcast in gDOT (which is not
  // part of the term syntax anyway)
  def upcast[A](x: A): x.type & Later[A] = x
}
export LaterUtils._

/**
  * Vaguely approximate the [tyApp] Coq metaprogram as a Scala function.
  */
def tyApp0[T, C[_]](f : (x : { type A }) => C[x.A]): C[T] = {
  val x : { type A = T } = new { type A = T }
  f(x)
}

// Closer to the typing in Coq.
def tyApp[T, C[_], R >: C[T]](f : (x : { type A }) => C[x.A]): R = {
  val x : { type A = T } = new { type A = T }
  f(x)
}

// Definition packTV l T := (ν {@ type l = shift T }).

// Definition tyApp l t T :=
//   lett t (lett (tv (packTV l (shift T))) (tapp (tv x1) (tv x0))).

// Lemma tyApp_typed Γ T U V t l :
//   Γ u⊢ₜ t : TAll (tparam l) U →
//   (** This subtyping premise is needed to perform "avoidance", as in compilers
//     for ML and Scala: that is, producing a type [V] that does not refer to
//     variables bound by let in the expression. *)
//   (∀ L, typeEq l (shiftN 2 T) :: L :: Γ u⊢ₜ U.|[up (ren (+1))], 0 <: (shiftN 2 V), 0) →
//   is_unstamped_ty (length Γ) T →
//   is_unstamped_ty (S (length Γ)) U →
//   Γ u⊢ₜ tyApp l t T : V.

//   Like [let: x := e1 in e2], but dropping [i] laters from [e1]'s type while
//   preserving its identity by adding a singleton type. See
//
// Definition deLater e1 i e2 := lett e1 (lett (iterate tskip i (tv x0)) e2).

/**
  * Vaguely approximate the [deLater] Coq metaprogram as a Scala function.
  */
def deLater[T1, T2](e1 : => Later[T1])(e2 : T1 => T2) : T2 = {
  val x : Later[T1] = e1
  val y: x.type & T1 = skip(x)
  e2(y)
}
