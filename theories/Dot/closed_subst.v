From D Require Import tactics.
From D.Dot Require Import syn synLemmas.

Implicit Types
         (T: ty) (v: vl) (e: tm) (p: path) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx).
Set Implicit Arguments.

Definition nclosed_sub n m s :=
  ∀ i, i < n → nclosed_vl (s i) m.
Definition nclosed_ren n m (r: var → var) := nclosed_sub n m (ren r).

Lemma compose_sub_closed s s1 s2 i j:
  nclosed_sub i j s → eq_n_s s1 s2 j → eq_n_s (s >> s1) (s >> s2) i.
Proof. move => /= Hs Heqs x Hxi. exact: Hs. Qed.

Lemma nclosed_ren_shift n m j:
  m >= j + n → nclosed_ren n m (+j).
Proof. move=>???/=; eauto with lia. Qed.
Hint Resolve nclosed_ren_shift.

Lemma nclosed_sub_vl v s i j:
  nclosed_sub i j s →
  nclosed_vl v i → nclosed_vl v.[s] j.
Proof. move => Hcls Hclv s1 s2 Heqs; asimpl. by eapply Hclv, compose_sub_closed. Qed.

Lemma nclosed_sub_x `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) s i j:
  nclosed_sub i j s →
  nclosed a i → nclosed a.|[s] j.
Proof. move => Hcls Hcla s1 s2 Heqs; asimpl. by eapply Hcla, compose_sub_closed. Qed.

Lemma nclosed_ren_vl v r i j:
  nclosed_ren i j r →
  nclosed_vl v i → nclosed_vl (rename r v) j.
Proof. asimpl; exact: nclosed_sub_vl. Qed.

Lemma nclosed_sub_up i j s:
  nclosed_sub i j s →
  nclosed_sub (S i) (S j) (up s).
Proof.
  move => //= Hs [|x] Hx. by eauto with lia.
  asimpl; rewrite -rename_subst.
  eapply nclosed_ren_vl; by eauto with lia.
Qed.
Hint Resolve nclosed_sub_up.

Lemma nclosed_ren_up n m r:
  nclosed_ren n m r →
  nclosed_ren (S n) (S m) (upren r).
Proof. move => //= Hr [|i] Hi; asimpl; eauto with lia. Qed.
Hint Resolve nclosed_ren_up.

Lemma nclosed_sub_inv_var x w i j k: j + k <= i →
  nclosed_vl (ids x).[upn j (w .: ids) >> ren (+k)] i →
  nclosed_vl (ids x) (S i).
Proof.
  rewrite /= !nclosed_vl_ids_equiv iter_up.
  case: (lt_dec x j) => [?|Hge]; first lia.
  case: (decide (x = j)) => [->|Hne]; first lia.
  case (x - j) as [|xj] eqn:Hxj; first lia.
  rewrite nclosed_vl_ids_equiv /=. lia.
Qed.

Lemma nclosed_sub_inv_mut w:
  (∀ e i j,
      j <= i →
      nclosed e.|[upn j (w .: ids)] i → nclosed e (S i)) /\
  (∀ v i j,
      j <= i →
      nclosed_vl v.[upn j (w .: ids)] i → nclosed_vl v (S i)) /\
  (∀ d i j,
      j <= i →
      nclosed d.|[upn j (w .: ids)] i → nclosed d (S i)) /\
  (∀ p i j,
      j <= i →
      nclosed p.|[upn j (w .: ids)] i → nclosed p (S i)) /\
  (∀ T i j,
      j <= i →
      nclosed T.|[upn j (w .: ids)] i → nclosed T (S i)).
Proof.
  apply syntax_mut_ind => //=
    [v1 IH1 | t1 t2 IH1 IH2 | t1 l IH1 | t1 IH1
    | x | t1 IH1 | ds IHds
    | T1 IH1 | vs s IHvs | v1 IH1
    | v1 IH1 | p1 l IH1
    | T1 T2 IH1 IH2
    | T1 T2 IH1 IH2
    | T1 IH1
    | T1 T2 IH1 IH2
    | T1 IH1
    | l T1 IH1
    | l T1 T2 IH1 IH2
    | p1 l IH1
    ] i j Hle Hcl.
  - by eapply fv_tv, IH1, fv_tv_inv.
  - eapply fv_tapp; [> eapply IH1 | eapply IH2]; eauto with fv.
  - eapply fv_tproj, IH1; eauto with fv.
  - eapply fv_tskip, IH1; eauto with fv.
  - eapply (nclosed_sub_inv_var _ _ j 0); asimpl; by [lia|].
  - eapply fv_vabs, (IH1 (S i) (S j)), fv_vabs_inv, Hcl; lia.
  - eapply fv_vobj, Forall_to_closed_dms.
    move: Hcl => /fv_vobj_inv.
    generalize dependent ds => ds.
    rewrite /= !Forall_fmap => *.
    decompose_Forall.
    destruct x; cbn in *.
    eapply (H1 (S i) (S j)); eauto with lia.
  - eapply fv_dtysyn, IH1; eauto with fv.
  - eapply fv_dtysem.
    move: Hcl => /fv_dtysem_inv.
    rewrite /= Forall_fmap => Hcl.
    decompose_Forall; eauto.
  - eapply fv_dvl, IH1; eauto with fv.
  - eapply fv_pv, IH1; eauto with fv.
  - eapply fv_pself, IH1; eauto with fv.
  - eapply fv_TAnd; [> eapply IH1 | eapply IH2]; eauto with fv.
  - eapply fv_TOr; [> eapply IH1 | eapply IH2]; eauto with fv.
  - eapply fv_TLater, IH1; eauto with fv.
  - eapply fv_TAll;
      [> eapply IH1, fv_TAll_inv_1 | eapply (IH2 (S i) (S j)), fv_TAll_inv_2];
      eauto with lia.
  - eapply fv_TMu, (IH1 (S i) (S j)), fv_TMu_inv; eauto with lia.
  - eapply fv_TVMem, IH1;
      eauto with fv lia.
  - eapply fv_TTMem;
      [> eapply IH1 | eapply IH2];
      eauto with fv lia.
  - eapply fv_TSel, IH1; eauto with fv.
Qed.

Lemma nclosed_sub_inv_ty T v n j: j <= n → nclosed T.|[upn j (v .: ids)] n → nclosed T (S n).
Proof. unmut_lemma (nclosed_sub_inv_mut v). Qed.

Lemma nclosed_sub_inv_ty_one T v n: nclosed T.|[v/] n → nclosed T (S n).
Proof. apply nclosed_sub_inv_ty with (j := 0); lia. Qed.

Lemma nclosed_ren_rev_var i j k x:
  nclosed_vl (ids x).[upn k (ren (+j))] (i + j + k) → nclosed_vl (ids x) (i + k).
Proof.
  rewrite /= !nclosed_vl_ids_equiv iter_up.
  case_match; rewrite /= nclosed_vl_ids_equiv /=; omega.
Qed.

Lemma nclosed_ren_rev_mut i j:
  (∀ e k,
    nclosed (e.|[upn k (ren (+j))]) (i + j + k) →
    nclosed e (i + k)) ∧
  (∀ v k,
    nclosed_vl (v.[upn k (ren (+j))]) (i + j + k) →
    nclosed_vl v (i + k)) ∧
  (∀ d k,
    nclosed (d.|[upn k (ren (+j))]) (i + j + k) →
    nclosed d (i + k)) ∧
  (∀ p k,
    nclosed (p.|[upn k (ren (+j))]) (i + j + k) →
    nclosed p (i + k)) ∧
  (∀ T k,
    nclosed (T.|[upn k (ren (+j))]) (i + j + k) →
    nclosed T (i + k)).
Proof.
  apply syntax_mut_ind => //
    [v1 IH1 | t1 t2 IH1 IH2 | t1 l IH1 | t1 IH1
    | x | t1 IH1 | ds IHds
    | T1 IH1 | vs s IHvs | v1 IH1
    | v1 IH1 | p1 l IH1
    | T1 T2 IH1 IH2
    | T1 T2 IH1 IH2
    | T1 IH1
    | T1 T2 IH1 IH2
    | T1 IH1
    | l T1 IH1
    | l T1 T2 IH1 IH2
    | p1 l IH1
    ] k Hcl /=.
  - by eapply fv_tv, IH1, fv_tv_inv.
  - eapply fv_tapp; [> eapply IH1 | eapply IH2]; eauto with fv.
  - eapply fv_tproj, IH1; eauto with fv.
  - eapply fv_tskip, IH1; eauto with fv.
  - exact: nclosed_ren_rev_var.
  - specialize (IH1 (S k)); rewrite ?plusnS in IH1.
    eapply fv_vabs, IH1, fv_vabs_inv, Hcl.
  - eapply fv_vobj, Forall_to_closed_dms.
    move: Hcl IHds => /fv_vobj_inv.
    rewrite /= !Forall_fmap => *.
    decompose_Forall.
    specialize (H0 (S k)); rewrite ?plusnS in H0.
    destruct x; cbn in *.
    eauto with lia.
  - eapply fv_dtysyn, IH1; eauto with fv.
  - eapply fv_dtysem.
    move: Hcl => /fv_dtysem_inv.
    rewrite /= Forall_fmap => Hcl.
    decompose_Forall; eauto.
  - eapply fv_dvl, IH1; eauto with fv.
  - eapply fv_pv, IH1; eauto with fv.
  - eapply fv_pself, IH1; eauto with fv.
  - eapply fv_TAnd; [> eapply IH1 | eapply IH2]; eauto with fv.
  - eapply fv_TOr; [> eapply IH1 | eapply IH2]; eauto with fv.
  - eapply fv_TLater, IH1; eauto with fv.
  - specialize (IH2 (S k)); rewrite ?plusnS in IH2.
    eapply fv_TAll; eauto 3 using fv_TAll_inv_1, fv_TAll_inv_2 with lia.
  - specialize (IH1 (S k)); rewrite ?plusnS in IH1.
    eapply fv_TMu, IH1, fv_TMu_inv; eauto with lia.
  - eapply fv_TVMem, IH1;
      eauto with fv lia.
  - eapply fv_TTMem;
      [> eapply IH1 | eapply IH2];
      eauto with fv lia.
  - eapply fv_TSel, IH1; eauto with fv.
Qed.

Lemma nclosed_ren_inv_ty T i j k:
    nclosed (T.|[upn k (ren (+j))]) (i + j + k) →
    nclosed T (i + k).
Proof. unmut_lemma (nclosed_ren_rev_mut i j). Qed.

Lemma nclosed_ren_inv_ty_one T i: nclosed T.|[ren (+1)] (S i) → nclosed T i.
Proof.
  pose proof (nclosed_ren_inv_ty T i 1 0) as H.
  asimpl in H; eauto.
Qed.
