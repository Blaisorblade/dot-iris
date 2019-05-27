From D Require Import tactics.
From D.DSub Require Import syn synLemmas.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx).
Set Implicit Arguments.

Lemma nclosed_sub_inv_mut w:
  (∀ e i j,
      j <= i →
      nclosed e.|[upn j (w .: ids)] i → nclosed e (S i)) /\
  (∀ v i j,
      j <= i → nclosed_vl v.[upn j (w .: ids)] i →
      nclosed_vl v (S i)) /\
  (∀ T i j,
      j <= i →
      nclosed T.|[upn j (w .: ids)] i → nclosed T (S i)).
Proof.
  apply syntax_mut_ind
  => //= [v1 IH1|t1 t2 IH1 IH2|t1 IH1|
         x|t1 IH1|T1 IH1|vs s IHvs|
         T1 IH1 |T1 T2 IH1 IH2|T1 T2 IH1 IH2|v1 IH1]
        i j Hle Hcl.
  - by eapply fv_tv, IH1, fv_tv_inv.
  - eapply fv_tapp; [> eapply IH1 | eapply IH2]; eauto with fv.
  - eapply fv_tskip, IH1; eauto with fv.
  - apply (nclosed_sub_inv_var w j (k := 0)); asimpl; by [lia|].
  - eapply fv_vabs, (IH1 (S i) (S j)), fv_vabs_inv, Hcl; lia.
  - eapply fv_vty, IH1; eauto with fv.
  - eapply fv_vstamp.
    move: Hcl => /fv_vstamp_inv.
    rewrite /= Forall_fmap => Hcl.
    decompose_Forall; eauto.
  - eapply fv_TLater, IH1; eauto with fv.
  - eapply fv_TAll;
      [> eapply IH1, fv_TAll_inv_1 | eapply (IH2 (S i) (S j)), fv_TAll_inv_2];
      eauto with lia.
  - eapply fv_TTMem;
      [> eapply IH1 | eapply IH2];
      eauto with fv lia.
  - eapply fv_TSel, IH1; eauto with fv.
Qed.

Lemma nclosed_sub_inv_ty T v n j: j <= n → nclosed T.|[upn j (v .: ids)] n → nclosed T (S n).
Proof. unmut_lemma (nclosed_sub_inv_mut v). Qed.

Lemma nclosed_sub_inv_ty_one T v n: nclosed T.|[v/] n → nclosed T (S n).
Proof. apply nclosed_sub_inv_ty with (j := 0); lia. Qed.

Lemma nclosed_ren_rev_mut i j:
  (∀ e k,
    nclosed (e.|[upn k (ren (+j))]) (i + j + k) →
    nclosed e (i + k)) ∧
  (∀ v k,
    nclosed_vl (v.[upn k (ren (+j))]) (i + j + k) →
    nclosed_vl v (i + k)) ∧
  (∀ T k,
    nclosed (T.|[upn k (ren (+j))]) (i + j + k) →
    nclosed T (i + k)).
Proof.
  apply syntax_mut_ind => // [v1 IH1|t1 t2 IH1 IH2|t1 IH1|
                             x|t1 IH1|T1 IH1|vs s IHvs|
                             T1 IH1 |T1 T2 IH1 IH2|T1 T2 IH1 IH2|v1 IH1]
                            k Hcl /=.
  - eauto using fv_tv, fv_tv_inv.
  - eapply fv_tapp; eauto using fv_tapp_inv_1, fv_tapp_inv_2.
  - specialize (IH1 k); eapply fv_tskip; eauto using fv_tskip_inv.
  - exact: nclosed_ren_rev_var.
  - specialize (IH1 (S k)); rewrite ?plusnS in IH1.
    eauto using fv_vabs_inv, fv_vabs.
  - eapply fv_vty, IH1; eauto with fv.
  - eapply fv_vstamp.
    move: Hcl => /fv_vstamp_inv.
    rewrite /= Forall_fmap => Hcl.
    decompose_Forall; eauto.
  - eapply fv_TLater, IH1; eauto with fv.
  - specialize (IH2 (S k)); rewrite ?plusnS in IH2.
    eapply fv_TAll; eauto 3 using fv_TAll_inv_1, fv_TAll_inv_2 with lia.
  - eapply fv_TTMem; eauto 3 using fv_TTMem, fv_TTMem_inv_1, fv_TTMem_inv_2 with lia.
  - eapply fv_TSel; eauto using fv_TSel_inv.
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
