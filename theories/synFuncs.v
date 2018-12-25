(*
Functions for manipulating the syntax needed for the operational semantics.
This file should not load Iris code to reduce compile times.
 *)
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

Lemma to_subst_nil: to_subst [] = ids.
Proof. by []. Qed.

Lemma to_subst_cons v ρ : to_subst (v :: ρ) = v .: to_subst ρ.
Proof. trivial. Qed.
Global Hint Rewrite to_subst_nil to_subst_cons : autosubst.

Global Typeclasses Opaque to_subst.
Global Opaque to_subst.

Definition subst_sigma (σ: vls) (ρ: list vl) := σ.|[to_subst ρ].

Definition push_var (σ: vls) : vls := (var_vl 0) :: σ.|[ren (+1)].

(** Create an identity environment of the given length. *)
Fixpoint idsσ n: vls :=
  match n with
  | 0 => []
  | S n => push_var (idsσ n)
  end.

(** When two substitutions are equivalent up to n. *)
Definition eq_n_s (s1 s2: var → vl) n := ∀ x, x < n → s1 x = s2 x.
Arguments eq_n_s /.

(** [n]-closedness defines when some AST has at most [n] free variables (from [0] to [n - 1]). *)
(** Here and elsewhere, we give one definition for values, using [subst], and
    another for other ASTs, using [hsubst]. *)
Definition nclosed_vl (v: vl) n :=
  ∀ s1 s2, eq_n_s s1 s2 n → v.[s1] = v.[s2].

Definition nclosed `{HSubst vl X} (t: X) n :=
  ∀ s1 s2, eq_n_s s1 s2 n → t.|[s1] = t.|[s2].

Definition cl_ρ ρ := Forall (λ v, nclosed_vl v 0) ρ.
Arguments cl_ρ /.
