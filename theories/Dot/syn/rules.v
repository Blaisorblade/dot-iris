(**
* Lift DOT operational semantics into rules for the Iris program logic.
In particular, declare instances of [PureExec], for use with
[wp_pure_step_later].
*)
From iris.program_logic Require Import language ectx_language.
From D Require Import iris_extra.det_reduction.
From D.Dot Require Import syn.

Set Suggest Proof Using.

Implicit Types e : tm.

Section lang_rules.
  (* Deriving from iris-examples. *)
  Ltac inv_head_step :=
    repeat match goal with
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : head_step ?e _ _ _ _ _ |- _ =>
       try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
       and can thus better be avoided. *)
       inversion H; subst; clear H
    end;
    (* DOT-specific addition. *)
    try objLookupDet;
    (* DOT-specific addition end. *)
    try (repeat split; congruence).

  #[local] Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.

  #[local] Hint Constructors head_step : core.
  #[local] Hint Resolve to_of_val : core.

  #[local] Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  #[local] Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
  #[local] Ltac solve_pure_exec :=
    unfold IntoVal in *;
    repeat match goal with H : AsVal _ |- _ => destruct H as [??] end; subst;
    intros ?; apply nsteps_once, pure_head_step_pure_step;
      constructor; [solve_exec_safe | solve_exec_puredet].

  #[global] Instance pure_lam e1 v2 :
    PureExec True 1 (tapp (tv (vabs e1)) (tv v2)) e1.|[v2 /].
  Proof. solve_pure_exec. Qed.

  #[global] Instance pure_tproj l v p :
    PureExec (v ,, l ↘ dpt p) 1 (tproj (tv v) l) (path2tm p).
  Proof. solve_pure_exec. Qed.

  #[global] Instance pure_tskip v :
    PureExec True 1 (tskip (tv v)) (tv v).
  Proof. solve_pure_exec. Qed.

  #[global] Instance pure_tif_true t1 t2 :
    PureExec True 1 (tif (tv $ vbool true) t1 t2) t1.
  Proof. solve_pure_exec. Qed.

  #[global] Instance pure_tif_false t1 t2 :
    PureExec True 1 (tif (tv $ vbool false) t1 t2) t2.
  Proof. solve_pure_exec. Qed.

  #[global] Instance pure_unop u v v' :
    PureExec (un_op_eval u v = Some v') 1 (tun u (tv v)) (tv v').
  Proof. solve_pure_exec. Qed.

  #[global] Instance pure_binop b v1 v2 v' :
    PureExec (bin_op_eval b v1 v2 = Some v') 1 (tbin b (tv v1) (tv v2)) (tv v').
  Proof. solve_pure_exec. Qed.

  #[global] Instance pure_tskip_iter v i :
    PureExec True i (iterate tskip i (tv v)) (tv v).
  Proof.
    move => _. elim: i => [|i IHi]; rewrite ?iterate_0 ?iterate_S //. by repeat constructor.
    replace (i.+1) with (i + 1) by lia.
    eapply nsteps_trans with (y := tskip (tv v)) => //.
    - change tskip with (fill [SkipCtx]) in *.
      by apply pure_step_nsteps_ctx; try apply _.
    - by apply pure_tskip.
  Qed.

End lang_rules.

Lemma tskip_n_to_fill i e : iterate tskip i e = fill (repeat SkipCtx i) e.
Proof. elim: i e => [|i IHi] e //; by rewrite ?iterate_0 ?iterate_Sr /= -IHi. Qed.

#[global] Instance ctx_iterate_tskip i : LanguageCtx (iterate tskip i).
Proof.
  rewrite -LanguageCtx_proper; first last.
  symmetry; exact: tskip_n_to_fill.
  apply _.
Qed.

Lemma head_step_pure e1 e2 σ1 κ σ2 efs :
  head_step e1 σ1 κ e2 σ2 efs → PureExec True 1 e1 e2.
Proof. inversion 1; intros ?; exact: pure_exec. Qed.

#[global] Instance : EctxLangDet dlang_ectx_lang.
Proof. repeat split; [intros; exact: head_step_pure|apply _]. Qed.
