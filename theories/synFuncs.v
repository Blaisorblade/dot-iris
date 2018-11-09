(*
Functions for manipulating the syntax needed for the operational semantics.
This file should not load Iris code to reduce compile times.
 *)
Require Import Dot.tactics.
Require Export Dot.dotsyn.
Require Import stdpp.list.

Module SynFuncs (gnameMod: type).
Import gnameMod.
Module SynG := Syn gnameMod.
Export SynG.

Fixpoint dms_to_list (ds: dms) : list dm :=
  match ds with
  | dnil => []
  | dcons d ds => d :: dms_to_list ds
  end.

(** Reverse lookup. *)
Fixpoint indexr {X} (i: nat) (xs: list X) : option X :=
  match xs with
  | [] => None
  | x :: xs =>
    if decide (i = length xs) then Some x else indexr i xs
  end.

Definition index_dms (i: label) (ds: dms): option dm :=
  indexr i (dms_to_list ds).

Definition dms_length ds := length (dms_to_list ds).

(** Single-variable substitution, based on the Autosubst1 notation. Priorities copied from s .[ sigma ]. *)
Notation "s .[ v /]" := (s .[ v .: var_vl ])
  (at level 2, v at level 200, left associativity,
   format "s .[ v /]" ) : subst_scope.

(** Substitute object inside itself (to give semantics to the "self"
    variable). To use when descending under the [vobj] binder. *)
Definition selfSubst (ds: dms): dms := ds.[vobj ds/].

Definition obj_opens_to v ds: Prop :=
  ∃ ds', v = vobj ds' ∧ selfSubst ds' = ds.
Notation "v ↗ ds" := (obj_opens_to v ds) (at level 20).

(* Instead of letting obj_opens_to autounfold, provide tactics to show it's deterministic and so on. *)

Definition dms_proj_val ds l v: Prop :=
  index_dms l ds = Some (dvl v).

End SynFuncs.
