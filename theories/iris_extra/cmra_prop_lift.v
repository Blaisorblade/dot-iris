From iris.algebra Require Import gmap.
From iris.base_logic Require Import iprop.

Implicit Types (P : cmraT → Type) (F : rFunctor) (Σ : gFunctors).
Set Suggest Proof Using.
Set Default Proof Using "Type".

(* Class (∀ A `{!Cofe A} B `{!Cofe B}, (P : cmraT → Type) (rFunctor_car (F : rFunctor) A B)) :=
  lift_cprop_rfunctor : LiftCPropToRFunctor P F. *)
Notation LiftCPropToRFunctor P F :=
  (∀ A `{!Cofe A} B `{!Cofe B}, P (rFunctor_car F A B)).
(* Fail Class LiftCPropToRFunctor (P : cmraT → Type) (F : rFunctor) :=
  lift_cprop_rfunctor : LiftCPropToRFunctor P F.
Class _LiftCPropToRFunctor (P : cmraT → Type) (F : rFunctor) :=
  lift_cprop_rfunctor :> LiftCPropToRFunctor P F. *)
Notation LiftCPropToGFunctor P Σ :=
  (∀ i, LiftCPropToRFunctor P (gFunctors_lookup Σ i)).
(* Class _LiftCPropToGFunctor P Σ :=
  lift_cprop_gfunctor : LiftCPropToGFunctor P Σ. *)

Notation LiftCPropToGFunctor_nil_type P := (LiftCPropToGFunctor P #[]).

Lemma LiftCPropToGFunctor_nil P : LiftCPropToGFunctor_nil_type P.
Proof. move=> i. apply fin_0_inv with (p := i). Qed.


Notation LiftCPropToGFunctor_app_type P :=
  (∀ Σ Σ' {HΣ : LiftCPropToGFunctor P Σ} {HΣ' : LiftCPropToGFunctor P Σ'},
    LiftCPropToGFunctor P (gFunctors.app Σ Σ')).

Lemma LiftCPropToGFunctor_app P : LiftCPropToGFunctor_app_type P.
Proof.
  intros; apply fin_plus_inv with (i := i); intros;
    [rewrite /= fin_plus_inv_L|rewrite /= fin_plus_inv_R]; auto.
Qed.


Notation LiftCPropToGFunctor_GFunctor_type F P :=
  (∀ (fp : LiftCPropToRFunctor P F),
  LiftCPropToGFunctor P #[ GFunctor F ]).

Lemma LiftCPropToGFunctor_GFunctor `{!rFunctorContractive F} P :
  LiftCPropToGFunctor_GFunctor_type F P.
Proof.
  intros; apply fin_S_inv with (i := i); first exact: fp.
  apply fin_0_inv.
Qed.


Section lift_cprop_iResUR.
  Context (P : cmraT → Type).
  Context {P_discrete_funUR : ∀ {A} (B : A → ucmraT) `(∀ i, P (B i)), P (discrete_funUR B)}.
  Context {P_gmapUR : ∀ `{Countable A} `(HpT : P T), P (gmapUR A T)}.

  Lemma lift_cprop_iResUR `(fp : LiftCPropToGFunctor P Σ) : P (iResUR Σ).
  Proof using Type*.
    rewrite /iResUR.
    apply P_discrete_funUR => i; apply P_gmapUR, fp.
  Qed.
End lift_cprop_iResUR.
