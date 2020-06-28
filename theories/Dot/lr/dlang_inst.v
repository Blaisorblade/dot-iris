From D Require Import iris_prelude dlang.
From D.Dot Require Export syn.
(* For local definitions. *)
From iris.program_logic Require ectx_language.
From D.pure_program_logic Require Import weakestpre lifting.

Include LiftWp VlSorts.

Ltac wp_pure := rewrite -wp_pure_step_later -1?wp_value; last done; iNext.

Tactic Notation "wp_bind" uconstr(p) :=
  iApply (wp_bind (ectx_language.fill [p])).
Ltac wp_wapply spec_pat := iApply (wp_wand with spec_pat).

Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
  wp_bind ctx;
  iApply (wp_wand with "[-]"); [iApply Hp; trivial|]; cbn;
  iIntros (v) Hv.
