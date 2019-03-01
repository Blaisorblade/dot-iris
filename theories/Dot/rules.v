From iris.program_logic Require Import ectx_language.
From D.Dot Require Import operational.

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

  Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl.

  Local Hint Constructors head_step.
  Local Hint Resolve to_of_val.

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

  Global Instance pure_tproj ds l v :
    PureExec (dms_lookup l (selfSubst ds) = Some (dvl v)) 1 (tproj (tv (vobj ds)) l) (tv v).
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

(* Copied from F_mu *)
Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

From iris.proofmode Require Import tactics.
Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
  iApply (wp_bind (fill[ctx]));
  iApply (wp_wand with "[-]"); [iApply Hp; trivial|]; cbn;
  iIntros (v) Hv.

Lemma tskip_n_to_fill i e: iterate tskip i e = fill (repeat SkipCtx i) e.
Proof. elim: i e => [|i IHi] e //; by rewrite ?iterate_0 ?iterate_Sr /= -IHi. Qed.
