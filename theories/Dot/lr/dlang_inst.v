(** * Instantiate Iris and [dlang] with our gDOT language. *)
From D Require Import iris_prelude dlang.
From D.Dot Require Export syn.
(* For local definitions. *)
From iris.program_logic Require ectx_language.
From D.pure_program_logic Require Import weakestpre lifting.

Include LiftWp VlSorts.

(**
Some tactics/proof automation for gDOT.

_Names_ are inspired by the names of Iris's HeapLang tactics, and the
behaviors are vaguely similar, but the implementations are more naive/less
efficient.
*)

(** Reduce pure computation steps. *)
Ltac wp_pure := rewrite -wp_pure_step_later -1?wp_value; last done; iNext.

(** Apply the [wp_bind] rule. *)
Tactic Notation "wp_bind" uconstr(p) :=
  iApply (wp_bind (ectx_language.fill [p])).

(** Apply a WP using the [wp_wand] rule; automatic application of [wp_bind],
as in Iris's [wp_apply], is not implemented. *)
Ltac wp_wapply spec_pat := iApply (wp_wand with spec_pat).
