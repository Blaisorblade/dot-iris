(** Define matching between terms which only differ in type members,
    following Sec. 3.5 of the PDF. *)
From iris.program_logic Require Import ectx_lifting ectx_language ectxi_language.
From D Require Import tactics.
From D.Dot Require Import operational traversals.

Import Trav2.

Definition same_skeleton_trav: Traversal unit :=
  {|
    upS := id;
    varP := λ s i1 i2, i1 = i2;
    dtyP := λ s tm1 tm2, True;
  |}.

Notation same_skel_tm := (forall_traversal_tm same_skeleton_trav ()).
Notation same_skel_vl := (forall_traversal_vl same_skeleton_trav ()).
Notation same_skel_dm := (forall_traversal_dm same_skeleton_trav ()).
Notation same_skel_dms := (forall_traversal_dms same_skeleton_trav ()).
Notation same_skel_path := (forall_traversal_path same_skeleton_trav ()).
Notation same_skel_ty := (forall_traversal_ty same_skeleton_trav ()).

Fixpoint same_skel_ectx K K' :=
  match K, K' with
  | AppLCtx e2, AppLCtx e2' => same_skel_tm e2 e2'
  | AppRCtx v1, AppRCtx v1' => same_skel_vl v1 v1'
  | ProjCtx l, ProjCtx l' => l = l'
  | SkipCtx, SkipCtx => True
  | _, _ => False
  end.

Definition same_skel_list_ectx Ks Ks' :=
  List.Forall2 same_skel_ectx Ks Ks'.

Lemma same_skel_list_ectx_app Ks Ks' K K' :
  same_skel_list_ectx Ks Ks' →
  same_skel_ectx K K' →
  same_skel_list_ectx (Ks ++ [K]) (Ks' ++ [K']).
Proof. intros ? ?; apply Forall2_app; auto. Qed.

Lemma same_skel_list_ectx_empty : same_skel_list_ectx [] [].
Proof. constructor. Qed.

Lemma same_skel_fill Ks e t':
  same_skel_tm (fill Ks e) t' →
  exists Ks' e',  t' = fill Ks' e' ∧ same_skel_tm e e' ∧ same_skel_list_ectx Ks Ks'.
Proof.
  revert e t'.
  induction Ks using rev_ind => e t'; simpl.
  {intros ?. exists [], t'; simpl; repeat split; auto using same_skel_list_ectx_empty. }
  rewrite fill_app /= => HKe.
  destruct x; destruct t';
    inversion HKe; subst;
    simpl in *; try done.
  - apply IHKs in H3.
    destruct H3 as (Ks' & e' & -> & He' & HKs').
    exists (Ks' ++ [AppLCtx t'2]), e'.
    rewrite fill_app /=; repeat split; auto using same_skel_list_ectx_app.
  - destruct t'1; inversion_clear H3; try done.
    apply IHKs in H5.
    destruct H5 as (Ks' & e' & -> & He' & HKs').
    exists (Ks' ++ [AppRCtx v]), e'.
    rewrite fill_app /=; repeat split; auto using same_skel_list_ectx_app.
  - apply IHKs in H1.
    destruct H1 as (Ks' & e' & -> & He' & HKs').
    exists (Ks' ++ [ProjCtx l0]), e'.
    rewrite fill_app /=; repeat split; trivial.
    apply same_skel_list_ectx_app; simpl; auto.
  - apply IHKs in H2.
    destruct H2 as (Ks' & e' & -> & He' & HKs').
    exists (Ks' ++ [SkipCtx]), e'.
    rewrite fill_app /=; repeat split; trivial.
    apply same_skel_list_ectx_app; simpl; auto.
Qed.

Lemma same_skel_fill_item Ks Ks' e e':
  same_skel_list_ectx Ks Ks' →
  same_skel_tm e e' →
  same_skel_tm (fill Ks e) (fill Ks' e').
Proof.
  revert Ks' e e'.
  induction Ks using rev_ind => Ks' e e'; simpl.
  { by inversion 1; subst. }
  rewrite fill_app /=; destruct x;
    intros (Ks'' & Ks3 & HKs &
            (z & ? & ? & ->%Forall2_nil_inv_l & ->)%Forall2_cons_inv_l & ->)
           %List.Forall2_app_inv_l; simpl in *;
      destruct z; subst; try done; rewrite fill_app /=; auto.
Qed.

(* Generalize over all the syntax, and same_skeleton environments. I proved
    same_skel_tm_subst just as a minimal sanity check. *)
Lemma same_skel_vl_subst e e' v v':
  same_skel_vl e e' → same_skel_vl v v' →
  same_skel_vl (e.[v/]) (e'.[v'/]).
Proof.
  move: e'; induction e; destruct e';
  move => Hske Hskv;
    cbn; inversion Hske; ev; cbn in *; subst; auto.
  (* asimpl. *)
Admitted.

(* Just a test proof. *)
Lemma same_skel_tm_subst e e' v v':
  same_skel_tm e e' → same_skel_vl v v' →
  same_skel_tm (e.|[v/]) (e'.|[v'/]).
Proof.
  move: e'; induction e; destruct e';
  move => Hske Hskv /=;
    inversion Hske; ev; auto using same_skel_vl_subst.
Qed.

Lemma same_skel_dms_index ds ds' v l:
  same_skel_dms ds ds' →
  dms_lookup l (selfSubst ds) = Some (dvl v) →
  exists v', dms_lookup l (selfSubst ds') = Some (dvl v') ∧ same_skel_vl v v'.
Proof.
Admitted.

Ltac destruct_matches :=
  repeat progress match goal with
                  | H: match ?t with | _ => _ end |- _ => destruct t; try done
                  | H: ?A ∧ ?B |- _ => destruct H
                  end.

(** Apply [tac] to any [same_skel_*] hypothesis. *)
Ltac with_same_skel tac :=
  match goal with
    | H: same_skel_ty _ _ |- _ => tac H
    | H: same_skel_tm _ _ |- _ => tac H
    | H: same_skel_vl _ _ |- _ => tac H
    | H: same_skel_dm _ _ |- _ => tac H
    | H: same_skel_path _ _ |- _ => tac H
  end.

(** Loop applying [tac] to all [same_skel_*] hypotheses,
    but once per each.
  *)
Ltac with_same_skel_loop tac :=
  repeat progress with_same_skel
    ltac:(fun H => try_once_tac H (tac H));
  un_usedLemma.

Lemma simulation_skeleton_head t1' t1 t2 σ σ' ts:
  same_skel_tm t1 t1' →
  head_step t1 σ [] t2 σ' ts →
  exists t2', head_step t1' σ [] t2' σ' ts ∧ same_skel_tm t2 t2'.
Proof.
  move=> Hsk Hhs. inversion Hhs; subst; with_same_skel_loop ltac:(fun P => nosplit (inverse P); cbn in * ).
  - eexists. split; first by econstructor. by eapply same_skel_tm_subst.
  - destruct (same_skel_dms_index ds ds2 v l) as [? [? ?]]; try done.
    by eexists; split; econstructor.
  - eexists. split; by [econstructor|].
Qed.

Theorem simulation_skeleton t1 t1' t2 σ σ' ts:
  same_skel_tm t1 t1' →
  prim_step t1 σ [] t2 σ' ts →
  exists t2', prim_step t1' σ [] t2' σ' ts ∧ same_skel_tm t2 t2'.
Proof.
  move=> Hsk Hstep. simpl in *.
  inversion Hstep; subst; simpl in *.
  apply same_skel_fill in Hsk as [Ks' [e' [Hfill [Hskel Hsklsit]]]]; simpl in *.
  eapply simulation_skeleton_head in H1 as [e'' [Hhs Hskk]]; last by eauto.
  exists (fill Ks' e''). subst. split; [econstructor; eauto | by apply same_skel_fill_item].
Qed.
