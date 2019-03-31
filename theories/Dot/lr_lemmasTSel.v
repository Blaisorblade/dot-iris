From iris.proofmode Require Import tactics.
From D Require Import tactics.
From D.Dot Require Import unary_lr synLemmas.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section Sec.
  Context `{HdotG: dotG Σ} Γ.

  (* Next step: proper lemma on arbitrary-length paths. *)
  Lemma mem_stp_sel_sub_path1 L U va l1 l2:
    (ivtp Γ (TVMem l1 (TTMem l2 L U)) va -∗
    ivstp Γ (TLater L) ((TSel (pself (pv va) l1) l2)))%I.
  Proof.
    iIntros "/= #[% Hva] !> * #Hg #[% HvL]". move: H H0 => Hclva Hclv.
    iDestruct ("Hva" $! ρ with "Hg") as (Hclvas d Hl Hcld vmem) "#[-> #[_ H1]]"; iClear "Hva".
    iDestruct "H1" as (d1) "[Hl2 [_ H]]".
    iDestruct "H" as (φ) "#[Hl [#HLφ #HφU]]".
    iDestruct ("HLφ" $! _ Hclv with "HvL") as "HLφ'".
    iSplit; first done.
    iExists vmem.
    iSplit => //.
    iExists φ, d1. repeat iModIntro; by repeat iSplit.
  Qed.

  Lemma Sub_Sel L U va l i:
    Γ ⊨ tv va : TTMem l L U, i -∗
    Γ ⊨ [TLater L, i] <: [TSel (pv va) l, i].
  Proof.
    iIntros "/= #[% #Hva] !> * % #Hg #[Hclv HvL]". move: H => Hclva. iFrame "Hclv".
    iSpecialize ("Hva" $! ρ with "Hg").
    iPoseProof (interp_env_ρ_closed with "Hg") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in *.

    iPoseProof (wp_value_inv' with "Hva") as "Hva'";  iClear "Hva".

    rewrite iterate_TLater_later //=; last by eauto using fv_to_subst_vl, fv_tv_inv.
    iNext.

    iDestruct "Hva'" as (Hclvas' d Hl Hcld φ) "#[Hlφ [#HLφ #HφU]]".
    repeat iSplit => //.
    iExists φ, d.
    iDestruct ("HLφ" $! _  with "Hclv HvL") as "#HLφ'".
    by repeat iSplit.
  Qed.

  Lemma Sel_Sub L U va l i:
    Γ ⊨ tv va : TTMem l L U, i -∗
    Γ ⊨ [TSel (pv va) l, i] <: [TLater U, i].
  Proof.
    iIntros "/= #[% #Hva] !> * % #Hg [$ #Hφ]". move: H => Hclva.
    iSpecialize ("Hva" $! ρ with "Hg").
    iPoseProof (interp_env_ρ_closed with "Hg") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in *.
    iPoseProof (wp_value_inv' with "Hva") as "Hva'";  iClear "Hva".
    rewrite iterate_TLater_later //=; last by eauto using fv_to_subst_vl, fv_tv_inv.
    iNext.
    iDestruct "Hva'" as (Hclvas d Hl Hcld φ) "#[Hlφ [#HLφ #HφU]]".
    iDestruct "Hφ" as (φ1 d1 Hva) "[Hγ #HΦ1v]".
    objLookupDet; subst. iPoseProof (stored_pred_agree d _ _ v with "Hlφ Hγ") as "#Hag".
    iApply "HφU" => //. repeat iModIntro. by iRewrite "Hag".
  Qed.
End Sec.
