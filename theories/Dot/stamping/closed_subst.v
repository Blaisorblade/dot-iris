From D Require Import tactics.
From D.Dot Require Import syn synLemmas.

Implicit Types
         (T: ty) (v: vl) (e: tm) (p: path) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx).
Set Implicit Arguments.

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
    | u t1 IH1 | b t1 t2 IH1 IH2 | t1 t2 t3 IH1 IH2 IH3
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
    | p1 IH1
    ] i j Hle Hcl.
  - by eapply fv_of_val, IH1, fv_of_val_inv.
  - eapply fv_tapp; [> eapply IH1 | eapply IH2]; eauto with fv.
  - eapply fv_tproj, IH1; eauto with fv.
  - eapply fv_tskip, IH1; eauto with fv.
  - eapply fv_tun, IH1; eauto with fv.
  - eapply fv_tbin; [> eapply IH1 | eapply IH2]; eauto with fv.
  - eapply fv_tif; [> eapply IH1 | eapply IH2 | eapply IH3 ]; eauto with fv.
  - apply (nclosed_sub_inv_var w j (k := 0)); asimpl; by [lia|].
  - eapply fv_vabs, (IH1 (S i) (S j)), fv_vabs_inv, Hcl; lia.
  - eapply fv_vobj. move: Hcl => /fv_vobj_inv. rewrite -!nclosed_axs_to_nclosed.
    generalize dependent ds => ds.
    rewrite /= !Forall_fmap => *.
    decompose_Forall; destruct x; cbn in *.
    eapply (H1 (S i) (S j)); eauto with lia.
  - eapply fv_dtysyn, IH1; eauto with fv.
  - eapply fv_dtysem.
    move: Hcl => /fv_dtysem_inv.
    rewrite /= Forall_fmap => Hcl.
    decompose_Forall; eauto.
  - eapply fv_dpt, IH1; eauto with fv.
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
  - eapply fv_TSing, IH1; eauto with fv.
Qed.

Lemma nclosed_sub_inv_ty T v n j: j <= n → nclosed T.|[upn j (v .: ids)] n → nclosed T (S n).
Proof. apply (nclosed_sub_inv_mut v). Qed.

Lemma nclosed_sub_inv_ty_one T v n: nclosed T.|[v/] n → nclosed T (S n).
Proof. apply nclosed_sub_inv_ty with (j := 0); lia. Qed.

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
    | u t1 IH1 | b t1 t2 IH1 IH2 | t1 t2 t3 IH1 IH2 IH3
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
    | p1 IH1
    ] k Hcl /=.
  - by eapply fv_of_val, IH1, fv_of_val_inv.
  - eapply fv_tapp; [> eapply IH1 | eapply IH2]; eauto with fv.
  - eapply fv_tproj, IH1; eauto with fv.
  - eapply fv_tskip, IH1; eauto with fv.
  - eapply fv_tun, IH1; eauto with fv.
  - eapply fv_tbin; [> eapply IH1 | eapply IH2]; eauto with fv.
  - eapply fv_tif; [> eapply IH1 | eapply IH2 | eapply IH3 ]; eauto with fv.
  - exact: nclosed_ren_rev_var.
  - specialize (IH1 (S k)); rewrite ?plusnS in IH1.
    eapply fv_vabs, IH1, fv_vabs_inv, Hcl.
  - eapply fv_vobj. move: Hcl => /fv_vobj_inv. rewrite -!nclosed_axs_to_nclosed.
    generalize dependent ds => ds; rewrite /= !Forall_fmap => *.
    decompose_Forall; destruct x; cbn in *.
    specialize (H1 (S k)); rewrite ?plusnS in H1.
    eauto with lia.
  - eapply fv_dtysyn, IH1; eauto with fv.
  - eapply fv_dtysem.
    move: Hcl => /fv_dtysem_inv.
    rewrite /= Forall_fmap => Hcl.
    decompose_Forall; eauto.
  - eapply fv_dpt, IH1; eauto with fv.
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
  - eapply fv_TSing, IH1; eauto with fv.
Qed.

Lemma nclosed_ren_inv_ty T i j k:
    nclosed (T.|[upn k (ren (+j))]) (i + j + k) →
    nclosed T (i + k).
Proof. apply (nclosed_ren_rev_mut i j). Qed.

Lemma nclosed_ren_inv_ty_one T i: nclosed (shift T) (S i) → nclosed T i.
Proof.
  pose proof (nclosed_ren_inv_ty T i 1 0) as H.
  asimpl in H; eauto.
Qed.
