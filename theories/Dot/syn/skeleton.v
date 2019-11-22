(** Define matching between terms which only differ in type members,
    following Sec. 3.5 of the PDF. *)
From iris.program_logic Require Import
     ectx_lifting ectx_language ectxi_language.
From D.Dot Require Import syn traversals.

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

Fixpoint same_skel_tm (t1 t2: tm) {struct t1} : Prop :=
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
same_skel_vl (v1 v2: vl) {struct v1} : Prop :=
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
same_skel_dm (d1 d2: dm) {struct d1} : Prop :=
  match (d1, d2) with
  | (dvl v1, dvl v2) => same_skel_vl v1 v2
  | (dvl _, _) => False
  | (_, dvl _) => False
    (* Only nontrivial cases. Could be replaced by a catchall. *)
  | (dtysyn _, dtysyn _) => True
  | (dtysyn _, dtysem _ _) => True
  | (dtysem _ _, dtysyn _) => True
  | (dtysem _ _, dtysem _ _) => True
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
  | (TTMem l1 T11 T12, TTMem l2 T21 T22) =>
    l1 = l2 ∧ same_skel_ty T11 T21 ∧ same_skel_ty T12 T22
  | (TSel p1 l1, TSel p2 l2) => same_skel_path p1 p2 ∧ l1 = l2
  | (TNat, TNat) => True
  | (TSing p1, TSing p2) => same_skel_path p1 p2
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

Definition same_skel_tm_up_ren_def t : Prop :=
  ∀ n m t', same_skel_tm t t' →
            same_skel_tm t.|[upn n (ren (+m))] t'.|[upn n (ren (+m))].

Definition same_skel_vl_up_ren_def v : Prop :=
  ∀ n m v', same_skel_vl v v' →
            same_skel_vl v.[upn n (ren (+m))] v'.[upn n (ren (+m))].

Definition same_skel_dm_up_ren_def d : Prop :=
  ∀ n m d', same_skel_dm d d' →
            same_skel_dm d.|[upn n (ren (+m))] d'.|[upn n (ren (+m))].

Definition same_skel_path_up_ren_def p : Prop :=
  ∀ n m p', same_skel_path p p' →
            same_skel_path p.|[upn n (ren (+m))] p'.|[upn n (ren (+m))].

Definition same_skel_ty_up_ren_def T : Prop :=
  ∀ n m T', same_skel_ty T T' →
            same_skel_ty T.|[upn n (ren (+m))] T'.|[upn n (ren (+m))].

Lemma same_skel_up_ren :
  (∀ t, same_skel_tm_up_ren_def t) ∧ (∀ v, same_skel_vl_up_ren_def v) ∧
  (∀ d, same_skel_dm_up_ren_def d) ∧ (∀ p, same_skel_path_up_ren_def p) ∧
  (∀ T, same_skel_ty_up_ren_def T).
Proof.
  apply syntax_mut_ind;
    try by (repeat intros ?; simpl in *; case_match;
            simpl in *; intuition (asimpl; auto)).
  - intros x n m v' Hv'; destruct v'; simpl in *; subst; intuition auto.
    rewrite iter_up; destruct lt_dec; simpl; auto.
  - intros ds Hds n m ds' Hds'; simpl in *.
    destruct ds' as [| | | ds']; simpl in *; intuition auto.
    revert Hds m n ds' Hds'.
    induction ds as [|[lbl dm] ds]; intros Hds m n ds' Hds';
      simpl in *; first by destruct ds'.
    destruct ds' as [|[lbl' dm'] ds']; simpl in *; first done.
    asimpl.
    inversion Hds; simplify_eq.
    destruct Hds' as [-> [Hdm Hds']].
    repeat split; auto.
    apply IHds; auto.
Qed.

Lemma same_skel_vl_up_ren v : same_skel_vl_up_ren_def v.
Proof. apply same_skel_up_ren. Qed.

Definition same_skel_tm_subst_def t : Prop :=
  ∀ f f' t', same_skel_tm t t' → (∀ x, same_skel_vl (f x) (f' x)) →
            same_skel_tm (t.|[f]) (t'.|[f']).

Definition same_skel_vl_subst_def v : Prop :=
  ∀ f f' v', same_skel_vl v v' → (∀ x, same_skel_vl (f x) (f' x)) →
            same_skel_vl (v.[f]) (v'.[f']).

Definition same_skel_dm_subst_def d : Prop :=
  ∀ f f' d', same_skel_dm d d' → (∀ x, same_skel_vl (f x) (f' x)) →
             same_skel_dm (d.|[f]) (d'.|[f']).

Definition same_skel_path_subst_def p : Prop :=
  ∀ f f' p', same_skel_path p p' → (∀ x, same_skel_vl (f x) (f' x)) →
             same_skel_path (p.|[f]) (p'.|[f']).

Definition same_skel_ty_subst_def T : Prop :=
  ∀ f f' T', same_skel_ty T T' → (∀ x, same_skel_vl (f x) (f' x)) →
            same_skel_ty (T.|[f]) (T'.|[f']).

Lemma same_skel_subst_up f f' :
  (∀ x, same_skel_vl (f x) (f' x)) →
  (∀ x, same_skel_vl (up f x) (up f' x)).
Proof.
  intros Hf x; destruct x as [|x]; asimpl; simpl; auto.
  by apply (same_skel_vl_up_ren (f x) 0 1 (f' x)).
Qed.

Lemma same_skel_subst :
  (∀ t, same_skel_tm_subst_def t) ∧ (∀ v, same_skel_vl_subst_def v) ∧
  (∀ d, same_skel_dm_subst_def d) ∧ (∀ p, same_skel_path_subst_def p) ∧
  (∀ T, same_skel_ty_subst_def T).
Proof.
  apply syntax_mut_ind;
    try by repeat intros ?; simpl in *; case_match;
      simpl in *; try subst; intuition auto using same_skel_subst_up.
  - intros ds Hds f f' ds' Hds' Hf; simpl in *.
    destruct ds' as [| | | ds']; simpl in *; intuition auto.
    revert Hds f f' ds' Hds' Hf.
    induction ds as [|[lbl dm] ds]; intros Hds f f' ds' Hds' Hf;
      simpl in *; first by destruct ds'.
    destruct ds' as [|[lbl' dm'] ds']; simpl in *; first done.
    asimpl.
    inversion Hds as [|? ? Hdm Hds_rest]; simplify_eq.
    destruct Hds' as [-> [Hdm' Hds']].
    repeat split; auto using same_skel_subst_up.
    apply IHds; auto.
Qed.

Lemma same_skel_vl_subst v : same_skel_vl_subst_def v.
Proof. apply same_skel_subst. Qed.

Lemma same_skel_dm_subst v : same_skel_dm_subst_def v.
Proof. apply same_skel_subst. Qed.

(* Just a test proof. *)
Lemma same_skel_tm_subst e e' v v':
  same_skel_tm e e' → same_skel_vl v v' →
  same_skel_tm (e.|[v/]) (e'.|[v'/]).
Proof.
  move: e'; induction e; destruct e';
  move => Hske Hskv;
    cbn in Hske |- *; try inversion Hske; ev; asimpl;
      auto.
  - apply same_skel_vl_subst; auto.
    intros x; destruct x as [|x]; asimpl; simpl; auto.
Qed.

Fixpoint same_skel_dms (ds1 ds2 : dms) {struct ds1} : Prop :=
  match ds1 with
  | [] => match ds2 with
         | [] => True
         | _ :: _ => False
         end
  | (l1, d1) :: ds3 =>
    match ds2 with
    | [] => False
    | (l2, d2) :: ds4 => l1 = l2 ∧ same_skel_dm d1 d2 ∧ same_skel_dms ds3 ds4
    end
  end.

Lemma same_skel_dms_subst dms :
  ∀ f f' dms', same_skel_dms dms dms' → (∀ x, same_skel_vl (f x) (f' x)) →
               same_skel_dms dms.|[f] dms'.|[f'].
Proof.
  induction dms as [|[l d] dms]; intros f f' dms' Hdms Hf;
    simpl in *; destruct dms' as [|[l' d'] dms']; simpl in *;
      intuition (asimpl; auto).
  apply same_skel_dm_subst; auto.
Qed.

Lemma same_skel_dms_selfSubst ds ds' :
  same_skel_dms ds ds' → same_skel_dms (selfSubst ds) (selfSubst ds').
Proof.
  intros Hds.
  apply same_skel_dms_subst; auto.
  - intros x; destruct x as [|x]; simpl; auto.
Qed.

Lemma same_skel_dms_index_gen {ds ds' v l}:
  same_skel_dms ds ds' →
  dms_lookup l ds = Some (dvl v) →
  exists v', dms_lookup l ds' = Some (dvl v') ∧ same_skel_vl v v'.
Proof.
  revert ds' l v.
  induction ds as [|[lbl d] ds]; intros ds' l v Hds Hlu; simpl in *; first done.
  destruct decide; subst.
  - destruct ds' as [|[l' d'] ds']; first done.
    destruct Hds as [? [Hd hds]]; simplify_eq; auto.
    destruct d'; simpl in *; try done.
    eexists; split; eauto.
    destruct decide; intuition auto.
  - destruct ds' as [|[l' d'] ds']; first done.
    destruct Hds as [? [Hd Hds]]; simplify_eq; auto.
    destruct (IHds ds' l v Hds Hlu) as [v' [? ?]].
    eexists; split; eauto.
    simpl; destruct decide; intuition auto.
Qed.

Lemma same_skel_obj_lookup v v' w l:
  same_skel_vl v v' →
  v @ l ↘ dvl w →
  ∃ w', v' @ l ↘ dvl w' ∧ same_skel_vl w w'.
Proof.
  intros Hv [ds [-> Hl]]. case: v' Hv => // ds' Hv.
  have [w' [Hl' Hw]]: ∃ w', dms_lookup l (selfSubst ds') = Some (dvl w') ∧ same_skel_vl w w'.
  eapply (@same_skel_dms_index_gen (selfSubst ds)); by [|apply same_skel_dms_selfSubst].
  exists w'; split; by [|exists ds'].
Qed.

Lemma simulation_skeleton_head t1' t1 t2 σ σ' ts:
  same_skel_tm t1 t1' →
  head_step t1 σ [] t2 σ' ts →
  exists t2', head_step t1' σ [] t2' σ' ts ∧ same_skel_tm t2 t2'.
Proof.
  move=> Hsk Hhs. inversion Hhs; subst; simpl in *.
  - repeat (case_match; intuition auto; simplify_eq).
    eexists; split; eauto using head_step, same_skel_tm_subst.
  - repeat (case_match; intuition auto; simplify_eq).
    edestruct same_skel_obj_lookup as [? [? ?]]; eauto using head_step.
  - repeat (case_match; intuition eauto using head_step).
Qed.

Theorem simulation_skeleton t1 t1' t2 σ σ' ts:
  same_skel_tm t1 t1' →
  prim_step t1 σ [] t2 σ' ts →
  ∃ t2', prim_step t1' σ [] t2' σ' ts ∧ same_skel_tm t2 t2'.
Proof.
  move=> Hsk Hstep; inversion Hstep; simplify_eq/=.
  apply same_skel_fill in Hsk as [Ks' [e' [Hfill [Hskel Hsklsit]]]].
  eapply simulation_skeleton_head in H1 as [e'' [Hhs Hskk]]; last by eauto.
  exists (fill Ks' e'').
  split; [econstructor; eauto | exact: same_skel_fill_item].
Qed.

Set Implicit Arguments.

Definition same_skel_tm_symm_def e1 : Prop := ∀ e2,
  same_skel_tm e1 e2 → same_skel_tm e2 e1.
Definition same_skel_vl_symm_def v1 : Prop := ∀ v2,
  same_skel_vl v1 v2 → same_skel_vl v2 v1.
Definition same_skel_dm_symm_def d1 : Prop := ∀ d2,
  same_skel_dm d1 d2 → same_skel_dm d2 d1.
Definition same_skel_path_symm_def p1 : Prop := ∀ p2,
  same_skel_path p1 p2 → same_skel_path p2 p1.
Definition same_skel_ty_symm_def T1 : Prop := ∀ T2,
  same_skel_ty T1 T2 → same_skel_ty T2 T1.

Lemma same_skel_symm :
  (∀ t, same_skel_tm_symm_def t) ∧ (∀ v, same_skel_vl_symm_def v) ∧
  (∀ d, same_skel_dm_symm_def d) ∧ (∀ p, same_skel_path_symm_def p) ∧
  (∀ T, same_skel_ty_symm_def T).
Proof.
  apply syntax_mut_ind; intros ** E; destruct E =>//=; hnf in *; intuition.
  generalize dependent ds; elim: l => [|[l2 d2] ds2 IHds2] [|[l1 d1] ds1] //.
  rewrite Forall_cons; naive_solver.
Qed.

Lemma same_skel_symm_tm e1 e2: same_skel_tm e1 e2 → same_skel_tm e2 e1.
Proof. apply same_skel_symm. Qed.

Lemma step_inversion (t1 : tm) thp σ σ' κ :
  step ([t1], σ) κ (thp, σ') →
  ∃ t2, thp = [t2] ∧ κ = [] ∧ prim_step t1 σ [] t2 σ' [].
Proof.
  destruct 1 as [????? t0 ??? Hstep]; destruct t0 as [|?[]]; try naive_solver.
  generalize dependent thp => -[|x[|a b]];
    inversion Hstep as [????? Hhstep]; inversion Hhstep; naive_solver.
Qed.

Lemma step_inversion' (t1 t2: tm) thp σ σ' κ :
  step ([t1], σ) κ (thp, σ') → t2 ∈ thp →
  thp = [t2] ∧ κ = [] ∧ prim_step t1 σ [] t2 σ' [].
Proof.
  move => /step_inversion [t2' [-> [->]]].
  rewrite elem_of_list_singleton. naive_solver.
Qed.

Lemma erased_step_prim (t1 t2: tm) thp σ σ' :
  erased_step ([t1], σ) (thp, σ') ∧ t2 ∈ thp ↔
  prim_step t1 σ [] t2 σ' [] ∧ thp = [t2].
Proof. split.
  - move => [[os Hstep] Hin]; move: (step_inversion' Hstep Hin); naive_solver.
  - move => [Hstep ->]. split; last constructor; exists [].
    by eapply @step_atomic with (t1 := []) (t2 := []).
Qed.

Theorem simulation_skeleton_erased_step {t1 t1' t2 σ σ' thp} :
  same_skel_tm t1 t1' →
  erased_step ([t1], σ) (thp, σ') ∧ t2 ∈ thp →
  ∃ t2' thp', (erased_step ([t1'], σ) (thp', σ') ∧ t2' ∈ thp') ∧
    same_skel_tm t2 t2'.
Proof.
  setoid_rewrite erased_step_prim; intros Hskel [Hstep ->].
  efeed pose proof simulation_skeleton as (t2' & ? & ?) => //.
  by exists t2', [t2'].
Qed.

Theorem simulation_skeleton_erased_steps {t1 t1' t2 σ σ' thp} :
  same_skel_tm t1 t1' →
  rtc erased_step ([t1], σ) (thp, σ') → t2 ∈ thp →
  ∃ t2', rtc erased_step ([t1'], σ) ([t2'], σ') ∧ same_skel_tm t2 t2'.
Proof.
  intros Hst Hsteps; revert t1' Hst; dependent induction Hsteps; intros ??.
  by rewrite elem_of_list_singleton => ->;
    exists t1'; split_and!; try constructor; eauto.
  intros Hin; destruct y as [l σ'']; have ?: σ'' = σ by destruct σ, σ''.
  subst. move: H (H) => [k Hstep] Hestep.
  move: (step_inversion Hstep) => [ti ?]; destruct_and!; simplify_eq.
  pose proof (simulation_skeleton_erased_step Hst
    (conj Hestep (elem_of_list_here _ _))) as (ti' & thpi'&(Hestep'&Hti')&?).
  efeed pose proof IHHsteps as (t2' &?&?) => //.
  exists t2'; split_and! => //.
  suff ?: thpi' = [ti'] by subst; eapply rtc_l with (y := ([ti'], _)).
  move: Hestep' => [k' Hstep'].
  move: (step_inversion Hstep') Hti' => [ti'' [-> _]].
  rewrite elem_of_list_singleton; naive_solver.
Qed.

Lemma same_skel_reducible e e_s σ:
  same_skel_tm e e_s → reducible e_s σ → reducible e σ.
Proof.
  intros Hskel%same_skel_symm_tm (k&e'&σ'&efs&Hstep).
  efeed pose proof step_inversion as [t2 Hinv]; first
    by eapply @step_atomic with (t1 := []) (t2 := []).
  destruct_and!; simplify_eq/=.
  efeed pose proof simulation_skeleton as (e' & ? & ?) => //.
  exists [], e'; eauto.
Qed.

Lemma safe_same_skel {e e_s}:
  same_skel_tm e e_s → safe e_s → safe e.
Proof.
  rewrite /safe; intros Hst Hsafe * Hred Hin.
  destruct (simulation_skeleton_erased_steps Hst Hred Hin)
    as (e_s' & Hst_s & Hskel').
  edestruct Hsafe; [apply Hst_s|apply elem_of_list_here|left|right].
  - destruct e_s', e'; naive_solver.
  - exact: same_skel_reducible.
Qed.
