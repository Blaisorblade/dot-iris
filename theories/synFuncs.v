(*
Functions for manipulating the syntax needed for the operational semantics.
This file should not load Iris code to reduce compile times.
 *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Dot.tactics.
Require Export Dot.dotsyn.
Require Import stdpp.list.
From iris.base_logic.lib Require Import invariants.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (Γ : list ty).

(* Fixpoint dms_to_list (ds: dms) : list dm := *)
(*   match ds with *)
(*   | dnil => [] *)
(*   | dcons d ds => d :: dms_to_list ds *)
(*   end. *)

(* Fixpoint vls_to_list (vs: vls) : list vl := *)
(*   match vs with *)
(*   | vlnil => [] *)
(*   | vlcons v vs => v :: vls_to_list vs *)
(*   end. *)

(* (** Reverse lookup. *) *)
(* Fixpoint indexr {X} (i: nat) (xs: list X) : option X := *)
(*   match xs with *)
(*   | [] => None *)
(*   | x :: xs => *)
(*     if decide (i = length xs) then Some x else indexr i xs *)
(*   end. *)

(* Definition index_dms (i: label) (ds: dms): option dm := *)
(*   indexr i (dms_to_list ds). *)

(* Definition dms_length ds := length (dms_to_list ds). *)

(* (** Single-variable substitution, based on the Autosubst1 notation. Priorities copied from s .[ sigma ]. *) *)
(* Notation "s .[ v /]" := (s .[ v .: var_vl ]) *)
(*   (at level 2, v at level 200, left associativity, *)
(*    format "s .[ v /]" ) : subst_scope. *)

(* (** Substitute object inside itself (to give semantics to the "self" *)
(*     variable). To use when descending under the [vobj] binder. *) *)
Definition selfSubst (ds: dms): dms := ds.|[vobj ds/].

Definition objLookup v l d: Prop :=
  ∃ ds, v = vobj ds ∧ reverse (selfSubst ds) !! l = Some d.
Notation "v @ l ↘ d" := (objLookup v l d) (at level 20).

(** Instead of letting obj_opens_to autounfold,
    provide tactics to show it's deterministic and so on. *)

Definition to_subst (ρ: list vl) : var → vl := foldr (λ v s, v .: s) ids ρ.

Lemma to_subst_cons v ρ : to_subst (v :: ρ) = v .: to_subst ρ.
Proof. trivial. Qed.
Global Hint Rewrite to_subst_cons : autosubst.

Global Typeclasses Opaque to_subst.
Global Opaque to_subst.

Lemma to_subst_weaken ρ1 ρ2 ρ3:
  upn (length ρ1) (ren (+length ρ2)) >> to_subst (ρ1 ++ ρ2 ++ ρ3) =
  to_subst (ρ1 ++ ρ3).
Proof.
  induction ρ1.
  - asimpl.
    induction ρ2; first by asimpl.
    asimpl; by rewrite IHρ2.
  - asimpl; by f_equal.
Qed.

Lemma undo_to_subst ρ : (+length ρ) >>> to_subst ρ = ids.
Proof. induction ρ; asimpl; auto. Qed.

Lemma to_subst_up ρ1 ρ2 v:
  upn (length ρ1) (v.[ren (+length ρ2)] .: ids) >> to_subst (ρ1 ++ ρ2) =
  to_subst (ρ1 ++ v :: ρ2).
Proof.
  induction ρ1.
  - by asimpl; rewrite undo_to_subst; asimpl.
  - asimpl. f_equal; by rewrite IHρ1.
Qed.

Definition subst_sigma (σ: vls) (ρ: list vl) := σ.|[to_subst ρ].

Definition push_var (σ: vls) : vls := (var_vl 0) :: σ.|[ren (+1)].

(* (** Create an identity environment vls. *)
(*  * The definition gives the right results but is not ideal to reason about. It *)
(*    is hard to prove it does what it should, and it's likely theorems using it *)
(*    should be rephrased in terms of the translation. *)
(*  *) *)
(* Fixpoint idsσ (ρ: list vl): vls := *)
(*   match ρ with *)
(*   | [] => vlnil *)
(*   | _ :: ρ1 => push_var (idsσ ρ1) *)
(*   end. *)

(* Definition wkT := toSubst_ty (+1). *)
(* Definition wkV := toSubst_vl (+1). *)
