(* (* Must be loaded first, so that other modules can reset some flags. *)
Require Import Equations.Equations. *)
From Coq Require FunctionalExtensionality.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
From D Require Import iris_prelude.
From D Require Import saved_interp_dep asubst_intf asubst_base dlang lty.
From D Require Import swap_later_impl.
From D.Dot Require dot_lty unary_lr.

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

Definition oCurry {n} {A : ofeT} (Φ : vec vl n.+1 → A) :
  vl -d> vec vl n -d> A := vcurry Φ.

Definition oUncurry {n} {A : ofeT} (Φ : vl → vec vl n → A) :
  vec vl n.+1 -d> A := vuncurry Φ.
Definition oLaterN {Σ n} i (τ : olty Σ n) := Olty (eLater i τ).

(** An inductive representation of gHkDOT semantic kinds. *)
Inductive s_kind {Σ} : nat → Type :=
  | s_kintv : olty Σ 0 → olty Σ 0 → s_kind 0
  | s_kpi n : olty Σ 0 → s_kind n → s_kind n.+1.
Global Arguments s_kind: clear implicits.

(** Alternative inductive representation of gHkDOT semantic kinds. *)
Record spine_s_kind {Σ} {n : nat} : Type := SpineSK {
  spine_kargs : vec (olty Σ 0) n;
  spine_L : olty Σ 0;
  spine_U : olty Σ 0;
}.
Arguments spine_s_kind : clear implicits.

(** Semantic kinds can be interpreted into predicates. *)
(** Semantic Kinds as unary Predicates. *)
Notation sp_kind Σ n := (env → iPPred (hoLty Σ n) Σ).
Notation SpKind K := (λ ρ, IPPred (λI T, K ρ T)).

(** Semantic Kinds as relations. *)
Notation sr_kind Σ n := (env → hoLtyO Σ n → iPPred (hoLty Σ n) Σ).
Notation SrKind K := (λ ρ T1, IPPred (λI T2, K ρ T1 T2)).

Notation iRel P Σ := (P Σ → P Σ → iProp Σ).
Definition subtype_lty {Σ} : iRel ltyO Σ := λI φ1 φ2,
  □ ∀ v, φ1 v → φ2 v.

Infix "⊆" := subtype_lty : bi_scope.
Notation "X ⊆ Y ⊆ Z" := (X ⊆ Y ∧ Y ⊆ Z)%I : bi_scope.
Notation "X ⊆ Y ⊆ Z ⊆ W" := (X ⊆ Y ∧ Y ⊆ Z ∧ Z ⊆ W)%I (at level 70, Y, Z at next level) : bi_scope.

(** Semantic Full Kind. *)
Record sf_kind {Σ n} := SfKind {
  sf_kind_car :> sp_kind Σ n;
  sf_kind_sub : sr_kind Σ n;
}.
Global Arguments sf_kind : clear implicits.
Global Arguments sf_kind_car : simpl never.
Global Arguments sf_kind_sub : simpl never.

Section kinds_types.
  Context {Σ}.

  Definition sp_kintv (L U : olty Σ 0) : spine_s_kind Σ 0 := SpineSK vnil L U.
  Definition sp_kpi {n} (S : olty Σ 0) (K : spine_s_kind Σ n) : spine_s_kind Σ n.+1 :=
    SpineSK (vcons S (spine_kargs K)) (spine_L K) (spine_U K).

  Definition sf_kintv (L U : olty Σ 0) : sf_kind Σ 0 :=
    SfKind
      (SpKind (λI ρ φ,
        oClose L ρ ⊆ oClose φ ⊆ oClose U ρ))
      (SrKind (λI ρ φ1 φ2,
        oClose L ρ ⊆ oClose φ1 ⊆ oClose φ2 ⊆ oClose U ρ)).

  Definition sf_kpi {n} (S : olty Σ 0) (K : sf_kind Σ n) : sf_kind Σ n.+1 :=
    SfKind
      (SpKind (λI ρ φ,
        □∀ arg, S vnil ρ arg →
        sf_kind_car K (arg .: ρ) (vcurry φ arg)))
      (SrKind (λI ρ φ1 φ2,
        □∀ arg, S vnil ρ arg →
        sf_kind_sub K (arg .: ρ) (vcurry φ1 arg) (vcurry φ2 arg))).


  Definition sf_star : sf_kind Σ 0 := sf_kintv oBot oTop.

  Fixpoint s_kind_to_spine_s_kind {n} (K : s_kind Σ n) : spine_s_kind Σ n :=
    match K with
    | s_kintv L U => sp_kintv L U
    | s_kpi s K => sp_kpi s (s_kind_to_spine_s_kind K)
    end.

  Definition spine_s_kind_to_sf_kind {n} (K : spine_s_kind Σ n) : sf_kind Σ n :=
    vec_fold (sf_kintv (spine_L K) (spine_U K)) (@sf_kpi) n (spine_kargs K).
  Global Arguments spine_s_kind_to_sf_kind {_} !_.

  Fixpoint s_kind_to_sf_kind {n} (K : s_kind Σ n) : sf_kind Σ n :=
    match K with
    | s_kintv L U => sf_kintv L U
    | s_kpi s K => sf_kpi s (s_kind_to_sf_kind K)
    end.

  Lemma s_kind_refl {n} (K : s_kind Σ n) T (ρ : env) :
    let sfK := s_kind_to_sf_kind K in
    sfK ρ T -∗ sf_kind_sub sfK ρ T T.
  Proof.
    elim: n ρ K T => [|n IHn] ρ; cbn.
    - move E: 0 => n K T. destruct K eqn:?; simplify_eq.
      by iIntros "($&$) !>" (v) "$".
    - move E: n.+1 => m K T.
      (* case E': K T E => [|m S K'].
      case: K T E. admit. *)
      destruct K as [|m S K'] eqn:?; simplify_eq/=.
      iIntros "#H !>" (arg) "#Harg".
      iApply IHn.
      iApply ("H" with "Harg").
  Qed.

  Definition oLam {n} (τ : oltyO Σ n) : oltyO Σ n.+1 :=
    Olty (λI args ρ, τ (vtail args) (vhead args .: ρ)).
    (* vuncurry (λ v, Olty (λ args ρ, τ args (v .: ρ))). *)
  Definition oTAppV {n} (T : oltyO Σ n.+1) w : olty Σ n :=
    Olty (λI args ρ, T (vcons w.[ρ] args) ρ).

  Lemma swap_oLam_oLater {n} (τ : olty Σ n) :
    oLater (oLam τ) ≡ oLam (oLater τ).
  Proof. done. Qed.

  Lemma swap_oTApp_oLater {n} (τ : olty Σ (S n)) v:
    oLater (oTAppV τ v) ≡ oTAppV (oLater τ) v.
  Proof. done. Qed.

End kinds_types.

(** Kinded, indexed subtyping *)
Program Definition sstpk `{!dlangG Σ} {n} i j Γ T1 T2 (K : sf_kind Σ n) : iProp Σ :=
  □∀ ρ, s⟦Γ⟧*ρ → sf_kind_sub K ρ (envApply (oLaterN i T1) ρ) (envApply (oLaterN j T2) ρ).
Notation "Γ s⊨ T1 , i <: T2 , j ∷ K" := (sstpk i j Γ T1 T2 K)
  (at level 74, i, j, T1, T2, K at next level).
Definition sktp `{!dlangG Σ} {n} i Γ T (K : sf_kind Σ n) : iProp Σ :=
  □∀ ρ, s⟦Γ⟧*ρ → ▷^i K ρ (envApply T ρ).
Notation "Γ s⊨ T ∷[ i  ] K" := (sktp i Γ T K)
  (at level 74, T, K at next level).
Definition ssktp `{!dlangG Σ} {n} i Γ (K1 K2 : sf_kind Σ n) : iProp Σ :=
  □∀ ρ, s⟦Γ⟧*ρ → ∀ (T : olty Σ n), ▷^i (K1 ρ (envApply T ρ) → K2 ρ (envApply T ρ)).
Notation "Γ s⊨ K1 <∷[ i  ] K2" := (ssktp i Γ K1 K2)
  (at level 74, K1, K2 at next level).

End HoSemTypes.

Module HkDot.
Import dot_lty unary_lr.
Include HoSemTypes VlSorts dlang_inst dot_lty.
Implicit Types
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : var → vl) (l : label).

Section dot_types.
  Context `{dlangG Σ}.

  Lemma sstpk_star_eq_sstp Γ i j T1 T2 :
    Γ s⊨ T1 , i <: T2 , j ∷ sf_star ⊣⊢ Γ s⊨ T1 , i <: T2 , j.
  Proof.
    rewrite /sstpk /sf_kind_sub/= /sf_star; iSplit; iIntros "/= #Hsub !>" (ρ).
    iIntros (v) "#Hg".
    by iDestruct ("Hsub" $! ρ with "Hg") as "{Hsub} (_ & #Hsub &_)"; iApply ("Hsub" $! v).
    iIntros "#Hg"; repeat iSplit; iIntros "!>" (v); [iIntros "[]" | | iIntros "_ //"].
    by iApply ("Hsub" $! ρ v with "Hg").
  Qed.

  Definition oTApp {n} (τ : oltyO Σ n.+1) (p : path) : olty Σ n :=
    Olty (λ args ρ v, path_wp p.|[ρ] (λ w, vcurry τ w args ρ v)).
End dot_types.
End HkDot.

