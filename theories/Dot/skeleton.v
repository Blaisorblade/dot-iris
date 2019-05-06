(** Define translation from syntactic terms/values to semantic ones, following Sec. 3.2 of the PDF. *)
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

Notation same_skeleton_tm := (forall_traversal_tm same_skeleton_trav ()).
Notation same_skeleton_vl := (forall_traversal_vl same_skeleton_trav ()).
Notation same_skeleton_dm := (forall_traversal_dm same_skeleton_trav ()).
Notation same_skeleton_path := (forall_traversal_path same_skeleton_trav ()).
Notation same_skeleton_ty := (forall_traversal_ty same_skeleton_trav ()).

Fixpoint same_skel_tm (t1 t2: tm): Prop :=
  match (t1, t2) with
  | (tv v1, tv v2) => same_skel_vl v1 v2
  | (tapp t11 t12, tapp t21 t22) =>
    same_skel_tm t11 t21 ∧ same_skel_tm t12 t22
  | (tproj t1 l1, tproj t2 l2) =>
    same_skel_tm t1 t2 ∧ l1 = l2
  | (tskip t1, tskip t2) =>
    same_skel_tm t1 t2
  | _ => False
  end
with
same_skel_vl (v1 v2: vl): Prop :=
  match (v1, v2) with
  | (var_vl i1, var_vl i2) => i1 = i2
  | (vabs t1, vabs t2) => same_skel_tm t1 t2
  | (vobj ds1, vobj ds2) =>
    let fix same_skel_dms (ds1 ds2: dms): Prop :=
        match (ds1, ds2) with
        | (nil, nil) => True
        | (cons (l1, d1) ds1, cons (l2, d2) ds2) =>
          l1 = l2 ∧ same_skel_dm d1 d2 ∧ same_skel_dms ds1 ds2
        | _ => False
        end
    in same_skel_dms ds1 ds2
  | (vnat n1, vnat n2) => n1 = n2
  | _ => False
  end
with
same_skel_dm (d1 d2: dm): Prop :=
  match (d1, d2) with
  | (dtysyn T1, dtysem σ2 γ2) =>
    (* Only nontrivial case *)
    True
  | (dvl v1, dvl v2) => same_skel_vl v1 v2
  | _ => False
  end.
Fixpoint same_skel_path (p1 p2: path): Prop :=
  match (p1, p2) with
  | (pv v1, pv v2) => same_skel_vl v1 v2
  | (pself p1 l1, pself p2 l2) => same_skel_path p1 p2 ∧ l1 = l2
  | _ => False
  end.
Fixpoint same_skel_ty (T1 T2: ty): Prop :=
  match (T1, T2) with
  | (TTop, TTop) => True
  | (TBot, TBot) => True
  | (TAnd T11 T12, TAnd T21 T22) =>
    same_skel_ty T11 T21 ∧ same_skel_ty T12 T22
  | (TOr T11 T12, TOr T21 T22) =>
    same_skel_ty T11 T21 ∧ same_skel_ty T12 T22
  | (TLater T1, TLater T2) =>
    same_skel_ty T1 T2
  | (TAll T11 T12, TAll T21 T22) =>
    same_skel_ty T11 T21 ∧ same_skel_ty T12 T22
  | (TMu T1, TMu T2) =>
    same_skel_ty T1 T2
  | (TVMem l1 T1, TVMem l2 T2) => l1 = l2 ∧ same_skel_ty T1 T2
  | (TTMem l1 T11 T12, TTMem l2 T21 T22) => l1 = l2 ∧ same_skel_ty T11 T21 ∧ same_skel_ty T12 T22
  | (TSel p1 l1, TSel p2 l2) => same_skel_path p1 p2 ∧ l1 = l2
  | (TNat, TNat) => True
  | _ => False
  end.

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
  destruct x; destruct t'; simpl in *; try done.
  - destruct HKe as [HKe Ht'].
    apply IHKs in HKe.
    destruct HKe as (Ks' & e' & -> & He' & HKs').
    exists (Ks' ++ [AppLCtx t'2]), e'.
    rewrite fill_app /=; repeat split; auto using same_skel_list_ectx_app.
  - destruct HKe as [Ht HKe'].
    destruct t'1; try done.
    apply IHKs in HKe'.
    destruct HKe' as (Ks' & e' & -> & He' & HKs').
    exists (Ks' ++ [AppRCtx v]), e'.
    rewrite fill_app /=; repeat split; auto using same_skel_list_ectx_app.
  - destruct HKe as [HKe <-].
    apply IHKs in HKe.
    destruct HKe as (Ks' & e' & -> & He' & HKs').
    exists (Ks' ++ [ProjCtx l]), e'.
    rewrite fill_app /=; repeat split; trivial.
    apply same_skel_list_ectx_app; simpl; auto.
  - apply IHKs in HKe.
    destruct HKe as (Ks' & e' & -> & He' & HKs').
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
      destruct z; try done; rewrite fill_app /=; auto.
Qed.

(* Generalize over all the syntax, and same_skeleton environments. I proved
    same_skel_tm_subst just as a minimal sanity check. *)
Lemma same_skel_vl_subst e e' v v':
  same_skel_vl e e' → same_skel_vl v v' →
  same_skel_vl (e.[v/]) (e'.[v'/]).
Proof.
  move: e'; induction e; destruct e';
  move => Hske Hskv;
    cbn in Hske |- *; try inversion Hske; ev; asimpl; auto.
Admitted.

(* Just a test proof. *)
Lemma same_skel_tm_subst e e' v v':
  same_skel_tm e e' → same_skel_vl v v' →
  same_skel_tm (e.|[v/]) (e'.|[v'/]).
Proof.
  move: e'; induction e; destruct e';
  move => Hske Hskv;
    cbn in Hske |- *; try inversion Hske; ev; asimpl; auto using same_skel_vl_subst.
  Qed.

(* Maybe copy-paste instead same_skel_dms from above. Or switch everything to an inductive definition, *)
Definition same_skel_dms (ds1 ds2: dms): Prop :=
  Forall2 (λ '(l1, d1) '(l2, d2), l1 = l2 ∧ same_skel_dm d1 d2) ds1 ds2.

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

Lemma simulation_skeleton_head t1' t1 t2 σ σ' ts:
  same_skel_tm t1 t1' →
  head_step t1 σ [] t2 σ' ts →
  exists t2', head_step t1' σ [] t2' σ' ts ∧ same_skel_tm t2 t2'.
Proof.
  move=> Hsk Hhs. inversion Hhs; subst; simpl in *.
  - destruct_matches. eexists. split; first by econstructor. by eapply same_skel_tm_subst.
  - destruct_matches. subst. destruct (same_skel_dms_index ds l1 v l0) as [? [? ?]]; try done.
    + clear Hhs H. red; generalize dependent l1; induction ds; destruct l1; try constructor; ev; try apply IHds; done.
    + eexists.
    split; [by econstructor | done].
  - destruct_matches. eexists. split; by [econstructor|idtac].
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
