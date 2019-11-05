From iris.program_logic Require Import language ectx_language.
From D.DSub Require Import syn.
Import asubst_base.

Implicit Types e : tm.

Section lang_rules.
  Ltac inv_head_step :=
    repeat match goal with
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : head_step ?e _ _ _ _ _ |- _ =>
       try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
       and can thus better be avoided. *)
       inversion H; subst; clear H
    end; try (repeat split; congruence).

  Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.

  Local Hint Constructors head_step : core.
  Local Hint Resolve to_of_val : core.

  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
  Local Ltac solve_pure_exec :=
    unfold IntoVal in *;
    repeat match goal with H : AsVal _ |- _ => destruct H as [??] end; subst;
    intros ?; apply nsteps_once, pure_head_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  Global Instance pure_lam e1 v2 :
    PureExec True 1 (tapp (tv (vabs e1)) (tv v2)) e1.|[v2 /].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_tskip v:
    PureExec True 1 (tskip (tv v)) (tv v).
  Proof. solve_pure_exec. Qed.

  Global Instance pure_tskip_iter v i:
    PureExec True i (iterate tskip i (tv v)) (tv v).
  Proof.
    move => _. elim: i => [|i IHi]; rewrite ?iterate_0 ?iterate_S //. by repeat constructor.
    replace (S i) with (i + 1) by lia.
    eapply nsteps_trans with (y := tskip (tv v)) => //.
    - change tskip with (fill [SkipCtx]) in *.
      by apply pure_step_nsteps_ctx; try apply _.
    - by apply pure_tskip.
  Qed.

End lang_rules.

Lemma tskip_n_to_fill i e: iterate tskip i e = fill (repeat SkipCtx i) e.
Proof. elim: i e => [|i IHi] e //; by rewrite ?iterate_0 ?iterate_Sr /= -IHi. Qed.

Instance ctx_iterate_tskip i: LanguageCtx (iterate tskip i).
Proof.
  rewrite -Proper_LanguageCtx; first last.
  symmetry; exact: tskip_n_to_fill.
  apply _.
Qed.
