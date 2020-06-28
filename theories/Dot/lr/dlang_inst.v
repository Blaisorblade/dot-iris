From D Require Import iris_prelude dlang.
From D.Dot Require Export syn.
(* For local definitions. *)
From iris.program_logic Require Import ectx_language.

Include LiftWp VlSorts.

Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
  iApply (wp_bind (fill[ctx]));
  iApply (wp_wand with "[-]"); [iApply Hp; trivial|]; cbn;
  iIntros (v) Hv.
