(** * Define correspondence between terms which only differ in type members.
Show it's a bisimulation and it preserves safety. *)
From iris.program_logic Require Import
     language ectx_language ectxi_language.
From D Require Import iris_extra.det_reduction.
From D.Dot Require Import syn rules.

Set Implicit Arguments.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Implicit Types (efs : list tm) (σ : ()) (e : tm).
Implicit Types (t : tm) (v : vl) (d : dm) (ds : dms) (p : path) (T : ty).

Fixpoint same_skel_tm (t1 t2: tm) {struct t1} : Prop :=
  match (t1, t2) with
  | (tv v1, tv v2) => same_skel_vl v1 v2
  | (tapp t11 t12, tapp t21 t22) =>
    same_skel_tm t11 t21 ∧ same_skel_tm t12 t22
  | (tproj t1 l1, tproj t2 l2) =>
    same_skel_tm t1 t2 ∧ l1 = l2
  | (tskip t1, tskip t2) =>
    same_skel_tm t1 t2
  | (tun u1 t1, tun u2 t2) =>
    u1 = u2 ∧ same_skel_tm t1 t2
  | (tbin b1 t11 t12, tbin b2 t21 t22) =>
    b1 = b2 ∧ same_skel_tm t11 t21 ∧ same_skel_tm t12 t22
  | (tif t11 t12 t13, tif t21 t22 t23) =>
    same_skel_tm t11 t21 ∧ same_skel_tm t12 t22 ∧ same_skel_tm t13 t23
  | _ => False
  end
with
same_skel_vl (v1 v2: vl) {struct v1} : Prop :=
  match (v1, v2) with
  | (vvar i1, vvar i2) => i1 = i2
  | (vabs t1, vabs t2) => same_skel_tm t1 t2
  | (vobj ds1, vobj ds2) =>
    let fix same_skel_dms (ds1 ds2: dms) {struct ds1}: Prop :=
        match ds1, ds2 with
        | [], [] => True
        | (l1, d1) :: ds1, (l2, d2) :: ds2 =>
          l1 = l2 ∧ same_skel_dm d1 d2 ∧ same_skel_dms ds1 ds2
        | _, _ => False
        end
    in same_skel_dms ds1 ds2
  | (vlit l1, vlit l2) => l1 = l2
  | _ => False
  end
with
same_skel_dm (d1 d2: dm) {struct d1} : Prop :=
  match (d1, d2) with
  | (dpt p1, dpt p2) => same_skel_path p1 p2
  | (dpt _, _) => False
  | (_, dpt _) => False
    (* Only nontrivial cases. Could be replaced by a catchall. *)
  | (dtysyn _, dtysyn _) => True
  | (dtysyn _, dtysem _ _) => True
  | (dtysem _ _, dtysyn _) => True
  | (dtysem _ _, dtysem _ _) => True
  end
with same_skel_path (p1 p2: path): Prop :=
  match (p1, p2) with
  | (pv v1, pv v2) => same_skel_vl v1 v2
  | (pself p1 l1, pself p2 l2) => same_skel_path p1 p2 ∧ l1 = l2
  | _ => False
  end.

Fixpoint same_skel_ectx K K' :=
  match K, K' with
  | AppLCtx e2, AppLCtx e2' => same_skel_tm e2 e2'
  | AppRCtx v1, AppRCtx v1' => same_skel_vl v1 v1'
  | ProjCtx l, ProjCtx l' => l = l'
  | SkipCtx, SkipCtx => True
  | UnCtx u, UnCtx u' => u = u'
  | BinLCtx b e2, BinLCtx b' e2' => b = b' ∧ same_skel_tm e2 e2'
  | BinRCtx b v1, BinRCtx b' v1' => b = b' ∧ same_skel_vl v1 v1'
  | IfCtx e1 e2, IfCtx e1' e2' => same_skel_tm e1 e1' ∧ same_skel_tm e2 e2'
  | _, _ => False
  end.

Local Notation same_skel_dms' :=
  (fix same_skel_dms (ds1 ds2 : dms) {struct ds1} : Prop :=
  match ds1 with
  | [] => match ds2 with
         | [] => True
         | _ :: _ => False
         end
  | p :: ds3 =>
    let (l1, d1) := p in
    match ds2 with
    | [] => False
    | p0 :: ds4 =>
      let (l2, d2) := p0 in
        l1 = l2 ∧ same_skel_dm d1 d2 ∧ same_skel_dms ds3 ds4
    end
  end).
Definition same_skel_dms : dms → dms → Prop := same_skel_dms'.

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
  - destruct HKe as [<- HKe].
    apply IHKs in HKe.
    destruct HKe as (Ks' & e' & -> & He' & HKs').
    exists (Ks' ++ [UnCtx u]), e'.
    rewrite fill_app /=; repeat split; trivial.
    apply same_skel_list_ectx_app; simpl; auto.
  - destruct HKe as [<- [HKe Ht']].
    apply IHKs in HKe.
    destruct HKe as (Ks' & e' & -> & He' & HKs').
    exists (Ks' ++ [BinLCtx b t'2]), e'.
    rewrite fill_app /=; repeat split; trivial.
    apply same_skel_list_ectx_app; simpl; auto.
  - destruct HKe as [<- [Ht' HKe]].
    destruct t'1; try done.
    apply IHKs in HKe.
    destruct HKe as (Ks' & e' & -> & He' & HKs').
    exists (Ks' ++ [BinRCtx b v]), e'.
    rewrite fill_app /=; repeat split; trivial.
    apply same_skel_list_ectx_app; simpl; auto.
  - destruct HKe as [HKe [Ht' Ht'']].
    apply IHKs in HKe.
    destruct HKe as (Ks' & e' & -> & He' & HKs').
    exists (Ks' ++ [IfCtx t'2 t'3]), e'.
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
      destruct z; try done; rewrite fill_app /=; intuition auto.
Qed.

Local Notation same_skel_tm_up_ren_def t :=
  (∀ n m t', same_skel_tm t t' →
            same_skel_tm t.|[upn n (ren (+m))] t'.|[upn n (ren (+m))]).

Local Notation same_skel_vl_up_ren_def v :=
  (∀ n m v', same_skel_vl v v' →
            same_skel_vl v.[upn n (ren (+m))] v'.[upn n (ren (+m))]).

Local Notation same_skel_dm_up_ren_def d :=
  (∀ n m d', same_skel_dm d d' →
            same_skel_dm d.|[upn n (ren (+m))] d'.|[upn n (ren (+m))]).

Local Notation same_skel_path_up_ren_def p :=
  (∀ n m p', same_skel_path p p' →
            same_skel_path p.|[upn n (ren (+m))] p'.|[upn n (ren (+m))]).

Lemma same_skel_up_ren :
  (∀ t, same_skel_tm_up_ren_def t) ∧ (∀ v, same_skel_vl_up_ren_def v) ∧
  (∀ d, same_skel_dm_up_ren_def d) ∧ (∀ p, same_skel_path_up_ren_def p) ∧
  (∀ T, True).
Proof.
  apply syntax_mut_ind;
    try by [intros; exact I | intros; simpl in *; case_match;
            simpl in *; destruct_and?; split_and?; auto 2].
  - intros x n m v' Hv'; destruct v'; simpl in *; subst; intuition auto.
    rewrite iter_up; destruct lt_dec; simpl; auto.
  - move=> t1 IHt1 n m v2' Hskv; destruct v2'; simplify_eq => //.
    rewrite /= -iterate_S. exact: IHt1.
  - cbn; move => ds Hds n m [//|//|//|ds'] Hds'.
    elim: ds ds' Hds Hds' =>
      [|[l d] ds IHds] [|[l' d'] ds'] /= Hds //= [Heq [Hd Hds']].
    inverse Hds.
    rewrite -iterate_S.
    split_and!; last apply IHds; auto.
Qed.

Lemma same_skel_vl_up_ren v : same_skel_vl_up_ren_def v.
Proof. apply same_skel_up_ren. Qed.

Local Notation same_skel_tm_subst_def t :=
  (∀ f f' t', same_skel_tm t t' → (∀ x, same_skel_vl (f x) (f' x)) →
            same_skel_tm (t.|[f]) (t'.|[f'])).

Local Notation same_skel_vl_subst_def v :=
  (∀ f f' v', same_skel_vl v v' → (∀ x, same_skel_vl (f x) (f' x)) →
            same_skel_vl (v.[f]) (v'.[f'])).

Local Notation same_skel_dm_subst_def d :=
  (∀ f f' d', same_skel_dm d d' → (∀ x, same_skel_vl (f x) (f' x)) →
             same_skel_dm (d.|[f]) (d'.|[f'])).

Local Notation same_skel_path_subst_def p :=
  (∀ f f' p', same_skel_path p p' → (∀ x, same_skel_vl (f x) (f' x)) →
             same_skel_path (p.|[f]) (p'.|[f'])).

Lemma same_skel_subst_up f f' :
  (∀ x, same_skel_vl (f x) (f' x)) →
  (∀ x, same_skel_vl (up f x) (up f' x)).
Proof.
  move=> Hf [//|x]. asimpl.
  by apply (same_skel_vl_up_ren (f x) 0 1 (f' x)).
Qed.

Lemma same_skel_subst :
  (∀ t, same_skel_tm_subst_def t) ∧ (∀ v, same_skel_vl_subst_def v) ∧
  (∀ d, same_skel_dm_subst_def d) ∧ (∀ p, same_skel_path_subst_def p) ∧
  (∀ T, True).
Proof.
  apply syntax_mut_ind;
    try by [intros; exact I | simpl; intros; case_match;
      simpl in *; try subst; intuition auto using same_skel_subst_up].
  - cbn; move => ds Hds f f' [//|//|//|ds'] Hds' Hf.
    elim: ds ds' Hds Hds' => [|[l d] ds IHds] [|[l' d'] ds'] Hds
      /ltac:(cbn) // -[He [Hd' Hds']]; inverse Hds.
    split_and!; last apply IHds; auto using same_skel_subst_up.
Qed.

Lemma same_skel_vl_subst v : same_skel_vl_subst_def v.
Proof. apply same_skel_subst. Qed.

Lemma same_skel_dm_subst d : same_skel_dm_subst_def d.
Proof. apply same_skel_subst. Qed.

Lemma same_skel_tm_subst' e : same_skel_tm_subst_def e.
Proof. apply same_skel_subst. Qed.
Lemma same_skel_tm_subst e e' v v':
  same_skel_tm e e' → same_skel_vl v v' →
  same_skel_tm (e.|[v/]) (e'.|[v'/]).
Proof. by intros; apply same_skel_tm_subst' => // -[|x]. Qed.

Lemma same_skel_dms_subst ds :
  ∀ f f' ds', same_skel_dms ds ds' → (∀ x, same_skel_vl (f x) (f' x)) →
               same_skel_dms ds.|[f] ds'.|[f'].
Proof.
  elim: ds => [|[l d] ds IHds] f f' [|[l' d'] ds'] Hds Hf; cbn in *; intuition.
  apply same_skel_dm_subst; auto.
Qed.

Lemma same_skel_dms_selfSubst ds ds' :
  same_skel_dms ds ds' → same_skel_dms (selfSubst ds) (selfSubst ds').
Proof.
  intros Hds.
  apply same_skel_dms_subst; auto.
  by move=> [|x].
Qed.

Lemma same_skel_dms_index_gen {ds1 ds2 p1 l}:
  same_skel_dms ds1 ds2 →
  dms_lookup l ds1 = Some (dpt p1) →
  ∃ p2, dms_lookup l ds2 = Some (dpt p2) ∧ same_skel_path p1 p2.
Proof.
  elim: ds1 ds2 => [//|[l1 d1] ds1 IHds] /= [//|[l2 d2] ds2]
    [? [Hd Hds]] Hlu; destruct decide; simplify_eq.
  - case: d2 Hd => //= p2 Hp.
    exists p2; destruct decide; intuition auto.
  - case: (IHds ds2 Hds Hlu) => [p2 [? ?]] /=.
    exists p2; destruct decide; intuition auto.
Qed.

Lemma same_skel_path2tm p p' :
  same_skel_path p p' → same_skel_tm (path2tm p) (path2tm p').
Proof. elim: p p' => [v|p IHp l] [v'|p' l'] //=. naive_solver. Qed.

Lemma same_skel_obj_lookup v v' p l:
  same_skel_vl v v' →
  v @ l ↘ dpt p →
  ∃ p', v' @ l ↘ dpt p' ∧ same_skel_tm (path2tm p) (path2tm p').
Proof.
  intros Hv [ds [-> Hl]]. case: v' Hv => // ds' Hv.
  have [p' [Hl' /same_skel_path2tm Hp]]: ∃ p', dms_lookup l (selfSubst ds') = Some (dpt p') ∧ same_skel_path p p'.
  eapply (@same_skel_dms_index_gen (selfSubst ds)); by [|apply same_skel_dms_selfSubst].
  exists p'; split; by [|exists ds'].
Qed.

Lemma same_skel_un_op_eval u v v' w:
  same_skel_vl v v' →
  un_op_eval u v = Some w →
  ∃ w', un_op_eval u v' = Some w' ∧ same_skel_vl w w'.
Proof. intros; destruct u, v, v' => //=; case_match; naive_solver. Qed.

Lemma same_skel_bin_op_eval b v1 v1' v2 v2' w:
  same_skel_vl v1 v1' →
  same_skel_vl v2 v2' →
  bin_op_eval b v1 v2 = Some w →
  ∃ w', bin_op_eval b v1' v2' = Some w' ∧ same_skel_vl w w'.
Proof.
  intros; destruct v1, v1' => //=; destruct v2, v2' => //=; simplify_eq/=;
    repeat (case_match; try done); simplify_eq/=;
    destruct b; simplify_eq/=; try case_decide; try case_match; try naive_solver.
Qed.

Hint Constructors head_step : core.
Lemma simulation_skeleton_head t1' t1 t2 σ σ' ts:
  same_skel_tm t1 t1' →
  head_step t1 σ [] t2 σ' ts →
  exists t2', head_step t1' σ [] t2' σ' ts ∧ same_skel_tm t2 t2'.
Proof.
  move=> Hsk Hhs. inversion Hhs; subst; clear Hhs; simpl in *.
  5: {
    destruct t1' as [| | | | | b' |]; intuition.
    subst b'; repeat (case_match => //).
    edestruct (same_skel_bin_op_eval b v1); intuition eauto.
  }
  all: repeat (case_match; int; simplify_eq/=; try done); eauto.
  - intuition eauto using same_skel_tm_subst.
  - edestruct same_skel_obj_lookup; naive_solver.
  - ev; simplify_eq; edestruct same_skel_un_op_eval; naive_solver.
Qed.

Theorem simulation_skeleton t1' {t1 t2 σ σ' ts} :
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

Local Notation same_skel_tm_refl_def := (∀ e, same_skel_tm e e).
Local Notation same_skel_vl_refl_def := (∀ v, same_skel_vl v v).
Local Notation same_skel_dm_refl_def := (∀ d, same_skel_dm d d).
Local Notation same_skel_path_refl_def := (∀ p, same_skel_path p p).

Lemma same_skel_refl :
  same_skel_tm_refl_def ∧ same_skel_vl_refl_def ∧
  same_skel_dm_refl_def ∧ same_skel_path_refl_def ∧
  (∀ T, True).
Proof.
  apply syntax_mut_ind; try by cbn; intuition.
  elim => [//|[l d] ds IHds]; rewrite Forall_cons; naive_solver.
Qed.

Lemma same_skel_refl_tm e : same_skel_tm e e.
Proof. apply same_skel_refl. Qed.
Lemma same_skel_refl_dm d : same_skel_dm d d.
Proof. apply same_skel_refl. Qed.
Lemma same_skel_refl_vl v : same_skel_vl v v.
Proof. apply same_skel_refl. Qed.
Hint Resolve same_skel_refl_tm same_skel_refl_dm same_skel_refl_vl : core.
Lemma same_skel_refl_dms ds  : same_skel_dms ds ds.
Proof. elim: ds => [//|[l d] ds IHds]; naive_solver. Qed.
Hint Resolve same_skel_refl_dms : core.

Lemma same_skel_ectx_refl K : same_skel_ectx K K.
Proof. destruct K; naive_solver. Qed.
Hint Resolve same_skel_ectx_refl : core.

Lemma same_skel_list_ectx_refl Ks : same_skel_list_ectx Ks Ks.
Proof. rewrite /same_skel_list_ectx; elim: Ks; naive_solver. Qed.
Hint Resolve same_skel_list_ectx_refl : core.

Lemma same_skel_tm_tskips e1 e2 i :
  same_skel_tm e1 e2 → same_skel_tm (iterate tskip i e1) (iterate tskip i e2).
Proof. rewrite !tskip_n_to_fill. exact: same_skel_fill_item. Qed.


Definition same_skel_tm_symm_def e1 : Prop := ∀ e2,
  same_skel_tm e1 e2 → same_skel_tm e2 e1.
Definition same_skel_vl_symm_def v1 : Prop := ∀ v2,
  same_skel_vl v1 v2 → same_skel_vl v2 v1.
Definition same_skel_dm_symm_def d1 : Prop := ∀ d2,
  same_skel_dm d1 d2 → same_skel_dm d2 d1.
Definition same_skel_path_symm_def p1 : Prop := ∀ p2,
  same_skel_path p1 p2 → same_skel_path p2 p1.

Lemma same_skel_symm :
  (∀ t, same_skel_tm_symm_def t) ∧ (∀ v, same_skel_vl_symm_def v) ∧
  (∀ d, same_skel_dm_symm_def d) ∧ (∀ p, same_skel_path_symm_def p) ∧
  (∀ T, True).
Proof.
  apply syntax_mut_ind; try done; intros ** E; destruct E =>//=; hnf in *; intuition.
  generalize dependent ds; elim: l => [|[l2 d2] ds2 IHds2] [|[l1 d1] ds1] //.
  rewrite Forall_cons; naive_solver.
Qed.

Lemma same_skel_symm_tm e1 e2: same_skel_tm e1 e2 → same_skel_tm e2 e1.
Proof. apply same_skel_symm. Qed.

Lemma same_skel_symm_dm d1 d2: same_skel_dm d1 d2 → same_skel_dm d2 d1.
Proof. apply same_skel_symm. Qed.

Definition same_skel_tm_trans_def e1 : Prop := ∀ e2 e3,
  same_skel_tm e1 e2 → same_skel_tm e2 e3 → same_skel_tm e1 e3.
Definition same_skel_vl_trans_def v1 : Prop := ∀ v2 v3,
  same_skel_vl v1 v2 → same_skel_vl v2 v3 → same_skel_vl v1 v3.
Definition same_skel_dm_trans_def d1 : Prop := ∀ d2 d3,
  same_skel_dm d1 d2 → same_skel_dm d2 d3 → same_skel_dm d1 d3.
Definition same_skel_path_trans_def p1 : Prop := ∀ p2 p3,
  same_skel_path p1 p2 → same_skel_path p2 p3 → same_skel_path p1 p3.

Local Lemma same_skel_trans_dms ds1 ds2 ds3 :
  Forall same_skel_dm_trans_def (map snd ds1) →
  same_skel_dms ds1 ds2 →
  same_skel_dms ds2 ds3 →
  same_skel_dms ds1 ds3.
Proof.
  elim: ds1 ds2 ds3 => [|[l1 d1] ds1 IHds1] [|[l2 d2] ds2] [|[l3 d3] ds3] //.
  rewrite Forall_cons; naive_solver.
Qed.

Section same_skel_trans.
  Local Hint Immediate same_skel_trans_dms : core.
  Local Ltac prepare :=
    try first [assumption | contradiction | hnf in *]; intuition idtac; subst.

  Lemma same_skel_trans :
    (∀ t, same_skel_tm_trans_def t) ∧ (∀ v, same_skel_vl_trans_def v) ∧
    (∀ d, same_skel_dm_trans_def d) ∧ (∀ p, same_skel_path_trans_def p) ∧
    (∀ T, True).
  Proof.
    apply syntax_mut_ind; try done; intros ** E2 E3 **; hnf in *; fold same_skel_dms in *.
    all: destruct E2, E3; prepare; eauto 2.
  Qed.

  Lemma same_skel_trans_dm d1 d2 d3 :
    same_skel_dm d1 d2 → same_skel_dm d2 d3 → same_skel_dm d1 d3.
  Proof. apply same_skel_trans. Qed.
End same_skel_trans.

Section same_skel_inversion.
  Lemma same_skel_tv_tv {v_u e_s} (Hsk : same_skel_tm (tv v_u) e_s) :
    ∃ v_s, e_s = tv v_s.
  Proof. destruct e_s; naive_solver. Qed.

  Lemma same_skel_dpt_dpt {p_u d_s} (Hsk : same_skel_dm (dpt p_u) d_s) :
    ∃ p_s, d_s = dpt p_s.
  Proof. destruct d_s; naive_solver. Qed.

  Lemma same_skel_var_var {x v_s} (Hsk : same_skel_vl (vvar x) v_s) :
    v_s = vvar x.
  Proof. destruct v_s; naive_solver. Qed.

  Lemma same_skel_vlit_vlit {x v_s} (Hsk : same_skel_vl (vlit x) v_s) :
    v_s = vlit x.
  Proof. destruct v_s; naive_solver. Qed.

  Lemma same_skel_tv_var_tv_var {x e_s} (Hs : same_skel_tm (tv (vvar x)) e_s) :
    e_s = tv (vvar x).
  Proof.
    by case (same_skel_tv_tv Hs) as [? ->]; rewrite (same_skel_var_var Hs).
  Qed.

  Lemma same_skel_tv_vlit_tv_vlit {x e_s}
    (Hs : same_skel_tm (tv (vlit x)) e_s) : e_s = tv (vlit x).
  Proof.
    by case (same_skel_tv_tv Hs) as [? ->]; rewrite (same_skel_vlit_vlit Hs).
  Qed.

End same_skel_inversion.

Ltac prim_step_inversion H :=
  destruct (prim_step_inversion H); ev; simplify_eq/=.

Theorem simulation_skeleton_pure_step {t1 t1' t2} :
  same_skel_tm t1 t1' →
  pure_step t1 t2 →
  ∃ t2', pure_step t1' t2' ∧ same_skel_tm t2 t2'.
Proof.
  setoid_rewrite <-(prim_step_pure_eq dummyState)=> Hskel Hstep.
  edestruct simulation_skeleton as (t2' & ? & ?) => //.
  exists t2'. naive_solver.
Qed.

Theorem simulation_skeleton_nsteps_pure_step {t1 t1' t2 n} :
  same_skel_tm t1 t1' →
  nsteps pure_step n t1 t2 →
  ∃ t2', nsteps pure_step n t1' t2' ∧ same_skel_tm t2 t2'.
Proof.
  move=>+ Hsteps. move: t1'.
  induction Hsteps as [|n t1 t2 tn Hstep Hsteps]; intros t1' Hsk1; first
  by exists t1'; split_and!; try constructor; eauto.
  destruct (simulation_skeleton_pure_step Hsk1 Hstep) as (t2' &Hstep' & Hsk2).
  edestruct (IHHsteps _ Hsk2) as (tn' & Hsteps' & Hskn).
  exists tn'; split_and; last done. exact: nsteps_l.
Qed.

Lemma prim_step_step t1 σ κ t2 σ' efs :
  prim_step t1 σ κ t2 σ' efs → step ([t1], σ) [] ([t2], σ').
Proof. exact: prim_step_step. Qed.
Hint Immediate prim_step_step : core.

Lemma erased_step_prim (t1 t2: tm) σ σ' :
  erased_step ([t1], σ) ([t2], σ') ↔
  prim_step t1 σ [] t2 σ' [].
Proof.
  split; rewrite /erased_step; last by eauto.
  move => [os Hstep]. have := !!step_inversion Hstep. naive_solver.
Qed.

Theorem simulation_skeleton_erased_step {t1 t1' t2 σ σ'} :
  same_skel_tm t1 t1' →
  erased_step ([t1], σ) ([t2], σ') →
  ∃ t2', erased_step ([t1'], σ) ([t2'], σ') ∧ same_skel_tm t2 t2'.
Proof.
  setoid_rewrite erased_step_prim; intros Hskel Hstep.
  edestruct simulation_skeleton as (t2' & ? & ?) => //.
  exists t2'. naive_solver.
Qed.

(** ** [same_skel_tm] is a simulation.
Since it's symmetric by [same_skel_symm_tm], it's also a
bisimulation. *)
Theorem simulation_skeleton_erased_steps {t1 t1' t2 σ σ' } :
  same_skel_tm t1 t1' →
  rtc L.erased_step ([t1], σ) ([t2], σ') →
  ∃ t2', rtc erased_step ([t1'], σ) ([t2'], σ') ∧ same_skel_tm t2 t2'.
Proof.
  uniqueState; setoid_rewrite <-pure_steps_erased'.

  intros Hst Hsteps; revert t1' Hst.
  induction Hsteps; intros ??.
  exists t1'; split_and!; try constructor; eauto.
  move: H => /pure_step_erased H.
  move: H (H) => [k Hstep] Hestep.
  have [ti ?] := step_inversion Hstep; destruct_and!; simplify_eq.
  destruct (simulation_skeleton_erased_step Hst Hestep) as (ti' &Hestep'&?).
  edestruct IHHsteps as (t2' &?&?) => //.
  exists t2'; split_and => //.
  by eapply rtc_l with (y := ti'); [apply pure_step_erased|].
Qed.

Lemma reducible_reducible_no_obs (e : tm) σ:
  reducible e σ → reducible_no_obs e σ.
Proof.
  rewrite /reducible_no_obs; intros (k&e'&σ'&efs&Hstep); simpl in *.
  prim_step_inversion Hstep. eauto.
Qed.

Lemma same_skel_reducible_no_obs {e e_s σ}:
  same_skel_tm e_s e → reducible_no_obs e_s σ → reducible_no_obs e σ.
Proof.
  intros Hskel (e_s'&σ'&efs&Hstep); prim_step_inversion Hstep.
  destruct (simulation_skeleton _ Hskel Hstep) as (e' & ? & ?).
  exists e'; eauto.
Qed.

Lemma same_skel_reducible {e e_s σ}:
  same_skel_tm e_s e → reducible e_s σ → reducible e σ.
Proof.
  move => Hskel /reducible_reducible_no_obs Hred.
  by eapply reducible_no_obs_reducible, same_skel_reducible_no_obs.
Qed.

Lemma same_skel_safe_n_impl n e_u:
  (∃ e_s, safe_n n e_s ∧ same_skel_tm e_u e_s) → safe_n n e_u.
Proof.
  intros (e_s & Hsafe & Hskel) e_u' Hred.
  destruct (simulation_skeleton_nsteps_pure_step Hskel Hred)
    as (e_s' & Hst_s & Hskel').
  edestruct (Hsafe _ Hst_s) as [Hs|Hs]; [left|right].
  - destruct e_s'; try by case (is_Some_None Hs).
    destruct e_u' => //; naive_solver.
  - eapply same_skel_reducible, Hs; exact: same_skel_symm_tm.
Qed.

Lemma same_skel_safe_impl {e e_s}:
  same_skel_tm e e_s → safe e_s → safe e.
Proof.
  rewrite /safe => Hskel Hsafe e' /pure_steps_erased' Hred.
  destruct (simulation_skeleton_erased_steps Hskel Hred)
    as (e_s' & Hst_s & Hskel').
  edestruct Hsafe as [Hs|Hs]; [apply pure_steps_erased', Hst_s|left|right].
  - destruct e_s'; try by case (is_Some_None Hs).
    destruct e' => //; naive_solver.
  - eapply same_skel_reducible, Hs; exact: same_skel_symm_tm.
Qed.

Lemma same_skel_safe_equiv {e e_s} :
  same_skel_tm e e_s → safe e_s ↔ safe e.
Proof. split; apply same_skel_safe_impl; by [>|apply: same_skel_symm_tm]. Qed.
