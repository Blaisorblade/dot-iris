(** * Instantiate Iris and [dlang] with our gDOT language. *)
From iris.program_logic Require ectx_language.
From iris.proofmode Require Import environments. (* Internals, used for extensions! *)
From D.pure_program_logic Require Import weakestpre lifting.

From D Require Import iris_prelude dlang.
From D.Dot Require Export syn.

Include LiftWp VlSorts.

(**
Some tactics/proof automation for gDOT.

_Names_ are inspired by the names of Iris's HeapLang tactics, and the
behaviors are vaguely similar, but the implementations are more naive/less
efficient.
*)

(** Reduce pure computation steps. *)
Ltac wp_pure := rewrite -wp_pure_step_later -1?wp_value; last done; iNext.

Module Import gdot_proofmode.

  (* Taken from [iris.heap_lang.tactics] and [iris.heap_lang.proofmode]. *)

  (** The tactic [reshape_expr e tac] decomposes the expression [e] into an
  evaluation context [K] and a subexpression [e'], and calls the tactic [tac K e'].
  *)
  Ltac reshape_expr e tac :=
    let rec go K e :=
      let e := eval hnf in e in
      lazymatch e with
      | tapp (tv ?v1) ?e2      => go (AppRCtx v1 :: K) e2
      | tapp ?e1 ?e2           => go (AppLCtx e2 :: K) e1
      | tproj ?e1 ?l           => go (ProjCtx l :: K) e1
      | tskip ?e1              => go (SkipCtx :: K) e1
      | tun ?op ?e1            => go (UnCtx op :: K) e1
      | tbin ?op (tv ?v1) ?e2  => go (BinRCtx op v1 :: K) e2
      | tbin ?op ?e1 ?e2       => go (BinLCtx op e2 :: K) e1
      | tif ?e0 ?e1 ?e2        => go (IfCtx e1 e2 :: K) e0
      | _                      => tac K e
      end
    in go (@nil ectx_item) e.

  Section CoqTactics.
    Context `{!dlangG Σ}.

    Lemma tac_wp_bind K Δ Φ e f :
      f = (λ e, ectx_language.fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
      envs_entails Δ (WP e {{ v, WP f (tv v) {{ Φ }} }})%I →
      envs_entails Δ (WP ectx_language.fill K e {{ Φ }}).
    Proof. rewrite envs_entails_eq=> -> ->. by apply: wp_bind. Qed.
  End CoqTactics.

  Ltac wp_bind_core K :=
    iStartProof;
    lazymatch eval hnf in K with
    | [] => idtac
    | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
    end.
End gdot_proofmode.

(** Apply the [wp_bind] rule. *)
Tactic Notation "wp_bind" open_constr(efoc) := wp_bind_core [efoc].

Local Ltac wp_binds_core Ks :=
  lazymatch eval hnf in Ks with
  | [] => idtac
  | ?K :: ?Ks => wp_bind K; wp_binds_core Ks
  end.
Tactic Notation "wp_binds" open_constr(Ks) := wp_binds_core Ks.

(** Apply [wp_bind] automatically. *)

Ltac wp_abind :=
  lazymatch goal with
  | |- envs_entails _ ?P =>
    let P := eval cbn in P in
    lazymatch P with
    | wp ?s ?E ?e ?Q =>
      let e := eval cbn in e in
      reshape_expr e ltac:(fun Ks e' => wp_binds (reverse Ks))
    | _ => fail "wp_abind: not a 'wp'"
    end
  end.

(** Apply a WP using the [wp_wand] rule, applying [wp_bind] automatically. *)
Ltac wp_wapply spec_pat := wp_abind; iApply (wp_wand with spec_pat).
