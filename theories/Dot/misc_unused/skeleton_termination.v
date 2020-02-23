From iris.program_logic Require Import
     ectx_lifting ectx_language ectxi_language.
From D.Dot Require Import syn traversals skeleton.
From D.Dot Require rules.

Set Implicit Arguments.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Implicit Types (e t : tm) (efs : list tm) (σ : ()).

Module AlternativeDef.
Import Trav2.
Definition same_skeleton_trav: Traversal unit :=
  {|
    upS := id;
    varP := λ s i1 i2, i1 = i2;
    dtyP := λ s tm1 tm2, True;
  |}.

Notation same_skeleton_tm := (forall_traversal_tm same_skeleton_trav ()).
Notation same_skeleton_vl := (forall_traversal_vl same_skeleton_trav ()).
Notation same_skeleton_dm := (forall_traversal_dm same_skeleton_trav ()).
Notation same_skeleton_path := (forall_traversal_path same_skeleton_trav ()).
Notation same_skeleton_ty := (forall_traversal_ty same_skeleton_trav ()).
End AlternativeDef.

Section prim_step_det.
Import rules.
Lemma head_step_pure e1 e2 σ1 κ σ2 efs :
  head_step e1 σ1 κ e2 σ2 efs → PureExec True 1 e1 e2.
Proof. inversion 1; intros ?; exact: pure_exec. Qed.

Lemma prim_step_pure e1 e2 σ1 κ σ2 efs :
  prim_step e1 σ1 κ e2 σ2 efs → PureExec True 1 e1 e2.
Proof. inversion 1; simplify_eq/=. by eapply pure_exec_fill, head_step_pure. Qed.

Lemma prim_step_det e e1 e2 σ1 κ σ2 efs :
  prim_step e σ1 κ e1 σ2 efs →
  prim_step e σ1 κ e2 σ2 efs → e1 = e2.
Proof.
  move => /prim_step_pure /(_ I) /(nsteps_once_inv _ _) [_ /(_ ()) Hdet]
    Hstep; destruct σ1, σ2.
  by edestruct Hdet => //; destruct_and!; simplify_eq/=.
Qed.
End prim_step_det.

Lemma pure_step_prim (t1 t1' : tm) :
  pure_step t1 t1' →
  reducible_no_obs t1 () ∧ prim_step t1 () [] t1' () [].
Proof.
  move => [/= /(_ ()) Hred /(_ ()) Hpure].
  destruct (Hred) as (t1''&[]&efs&Hstep); simpl in *.
  prim_step_inversion Hstep.
  edestruct Hpure as (?&?&?&?) => // {Hpure}; naive_solver.
Qed.

Theorem simulation_skeleton_pure_step {t1 t1' t2 : tm} :
  same_skel_tm t1 t2 →
  pure_step t1 t1' → ∃ t2', pure_step t2 t2' ∧ same_skel_tm t1' t2'.
Proof.
  move => Hskel /pure_step_prim [Hred Hstep].
  pose proof simulation_skeleton as (t2' & ? & ?) => //.
  exists t2'; int.
  have Hred' := (same_skel_reducible_no_obs Hskel Hred).
  constructor; intros [] *; cbn; first done; destruct σ2.
  intros Hstep'; prim_step_inversion Hstep'.
  int; exact: prim_step_det.
Qed.

Theorem simulation_skeleton_pure_steps {t_s t_r u_s : tm} :
  same_skel_tm t_s u_s →
  rtc pure_step t_s t_r →
  ∃ u_r, rtc pure_step u_s u_r ∧ same_skel_tm t_r u_r.
Proof.
  move => /= Hst Hsteps; move: u_s Hst.
  dependent induction Hsteps; intros; first by exists u_s; eauto.
  rename H into Hstep, x into t_s, y into t', z into t_r.
  have [/= u' [? Hst']] := simulation_skeleton_pure_step Hst Hstep.
  pose proof (IHHsteps _ Hst') as (u_r&?&?).
  exists u_r; split_and!; by [|exact: rtc_l].
Qed.

Lemma terminates_same_skel {e e_s}:
  same_skel_tm e e_s → terminates e_s → terminates e.
Proof.
  rewrite /terminates /= => /same_skel_symm_tm Hst [v Hsteps].
  have [/= e' [? ?]] := simulation_skeleton_pure_steps Hst Hsteps.
  destruct e'; naive_solver.
Qed.


From D.Dot Require Import stampingDefsCore astStamping typingStamping path_repl_lemmas.

Lemma terminates_stamp {n e g e_s}:
  stamps_tm' n e g e_s → terminates e_s → terminates e.
Proof. move => [/unstamp_same_skel_tm Hs _] Hsafe. exact: terminates_same_skel. Qed.

Hint Resolve is_stamped_path2tm is_unstamped_path2tm' unstamp_path2tm : core.

Lemma stamps_path2tm n p g p' :
  stamps_path' n p g p' → stamps_tm' n (path2tm p) g (path2tm p').
Proof.
  intros; destruct_and!; induction p; destruct p'; with_is_stamped inverse;
    with_is_unstamped inverse; split_and! => //; eauto.
Qed.
