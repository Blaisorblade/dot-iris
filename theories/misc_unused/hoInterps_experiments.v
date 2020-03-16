(* (* Must be loaded first, so that other modules can reset some flags. *)
Require Import Equations.Equations. *)
From Coq Require FunctionalExtensionality.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import iris_prelude.
From D Require Import saved_interp_dep asubst_intf asubst_base dlang lty.
From D Require Import swap_later_impl.

Import EqNotations.

Set Suggest Proof Using.
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (Σ : gFunctors) .
(** ssreflect postfix notation for the successor and predecessor functions.
SSreflect uses "pred" for the generic predicate type, and S as a local bound
variable.*)
Notation succn := Datatypes.S.
Notation predn := Peano.pred.

Notation "n .+1" := (succn n) (at level 2, left associativity,
  format "n .+1") : nat_scope.
Notation "n .+2" := n.+1.+1 (at level 2, left associativity,
  format "n .+2") : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2, left associativity,
  format "n .+3") : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2, left associativity,
  format "n .+4") : nat_scope.

Notation "n .-1" := (predn n) (at level 2, left associativity,
  format "n .-1") : nat_scope.
Notation "n .-2" := n.-1.-1 (at level 2, left associativity,
  format "n .-2") : nat_scope.


Module Type HoSemTypes (Import VS : VlSortsFullSig) (Import LWP : LiftWp VS) (Import L : Lty VS LWP).

Definition hoLty Σ n := vec vl n → lty Σ.
Definition hoLtyO Σ n := vec vl n -d> ltyO Σ.

Definition envApply {Σ n} : oltyO Σ n → env → hoLtyO Σ n :=
  λ T, flip T.

Definition oCurry {n} {A : ofeT} (Φ : vec vl (S n) → A) :
  vl -d> vec vl n -d> A := vcurry Φ.

Definition oUncurry {n} {A : ofeT} (Φ : vl → vec vl n → A) :
  vec vl (S n) -d> A := vuncurry Φ.
Definition oLaterN {Σ n} i (τ : olty Σ n) := Olty (eLater i τ).

Inductive skind {Σ} : nat → Type :=
  | skintv : olty Σ 0 → olty Σ 0 → skind 0
  | skpi n : olty Σ 0 → skind n → skind (S n).
Global Arguments skind: clear implicits.

Record spine_skind {Σ} {n : nat} : Type := SpineSK {
  spine_kargs : vec (olty Σ 0) n;
  spine_L : olty Σ 0;
  spine_U : olty Σ 0;
}.
Arguments spine_skind : clear implicits.

Section saved_ho_sem_type_extra.
  Context {Σ}.

  Definition sp_skintv (L U : olty Σ 0) : spine_skind Σ 0 := SpineSK vnil L U.
  Definition sp_skpi {n} (S : olty Σ 0) (K : spine_skind Σ n) : spine_skind Σ n.+1 :=
    SpineSK (vcons S (spine_kargs K)) (spine_L K) (spine_U K).

  Fixpoint skind_to_spine_skind {n} (K : skind Σ n) : spine_skind Σ n :=
    match K with
    | skintv L U => sp_skintv L U
    | skpi s K => sp_skpi s (skind_to_spine_skind K)
    end.

End saved_ho_sem_type_extra.
End HoSemTypes.

From D.Dot Require Import dot_lty unary_lr.

Implicit Types
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (vs : vls) (ρ : var → vl) (l : label).

Module HkDot.
Include HoSemTypes VlSorts dlang_inst dot_lty.

End HkDot.

