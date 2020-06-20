(** * Utilities for lifting camera properties to [iProp], used in [swap_later_impl.v] and [persistence.v]. *)
From iris.algebra Require Import gmap.
From iris.base_logic Require Import iprop.

(** In practice, in this code [P] meant to abstract over _type classes_, but
this is not supported by Coq. *)
Implicit Types (P : cmraT → Type) (F : rFunctor) (Σ : gFunctors).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Notation LiftCPropToRFunctor P F :=
  (∀ A `{!Cofe A} B `{!Cofe B}, P (rFunctor_car F A B)).
Notation LiftCPropToGFunctor P Σ :=
  (∀ i, LiftCPropToRFunctor P (gFunctors_lookup Σ i)).

(** All lemmas below are used to generate typeclass instances; the
[LiftCProp*] lemmas are templates for instances, and [LiftCProp*_type] are
helpers for declaring them. See [swap_later_impl.v] for the intended usage. *)


(** *** Lift to [#[]]. *)
Notation LiftCPropToGFunctor_nil_type P := (LiftCPropToGFunctor P #[]).

Lemma LiftCPropToGFunctor_nil P : LiftCPropToGFunctor_nil_type P.
Proof. move=> i. apply fin_0_inv with (p := i). Qed.


(** *** Lift to [gFunctors.app]. *)
Notation LiftCPropToGFunctor_app_type P :=
  (∀ Σ Σ' {HΣ : LiftCPropToGFunctor P Σ} {HΣ' : LiftCPropToGFunctor P Σ'},
    LiftCPropToGFunctor P (gFunctors.app Σ Σ')).

Lemma LiftCPropToGFunctor_app P : LiftCPropToGFunctor_app_type P.
Proof.
  intros; apply fin_plus_inv with (i := i); intros;
    [rewrite /= fin_plus_inv_L|rewrite /= fin_plus_inv_R]; auto.
Qed.


(** *** Lift to [gFunctors.singleton]. *)
Notation LiftCPropToGFunctor_GFunctor_type F P :=
  (∀ (fp : LiftCPropToRFunctor P F),
  LiftCPropToGFunctor P (gFunctors.singleton (GFunctor F))).

(* We abstract over [rFunctorContractive] explicitly, to make it an implicit
parameter. *)
Lemma LiftCPropToGFunctor_GFunctor `{!rFunctorContractive F} P :
  LiftCPropToGFunctor_GFunctor_type F P.
Proof.
  intros; apply fin_S_inv with (i := i); first exact: fp.
  apply fin_0_inv.
Qed.


(** Show what's needed to lift camera properties to [iResUR] (the resources
used by [iProp]).
This could be generated by typeclass search, but
- I prefer a way to see the actual code.
- In fact, we don't want typeclass search unfolding [iResUR] to prove a
  proposition is persistent, so we make it [Typeclasses Opaque].
*)
Typeclasses Opaque iResUR.

Section lift_cprop_iResUR.
  Context {P : cmraT → Type}.
  Context {P_discrete_funUR : ∀ {A} (B : A → ucmraT) `(∀ i, P (B i)), P (discrete_funUR B)}.
  Context {P_gmapUR : ∀ `{Countable A} `(HpT : P T), P (gmapUR A T)}.

  Lemma lift_cprop_iResUR `{fp : LiftCPropToGFunctor P Σ} : P (iResUR Σ).
  Proof using Type*.
    rewrite /iResUR. apply P_discrete_funUR => i; apply P_gmapUR, fp.
  Qed.
End lift_cprop_iResUR.
