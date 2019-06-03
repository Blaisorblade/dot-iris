From iris.proofmode Require Import tactics.
From D Require Import tactics.
From D.Dot Require Import unary_lr synLemmas.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section Sec.
  Context `{HdlangG: dlangG Σ} Γ.

  Lemma Sub_Sel L U va l i:
    Γ ⊨ tv va : TTMem l L U, i -∗
    Γ ⊨ [TLater L, i] <: [TSel (pv va) l, i].
  Proof.
    iIntros "/= [% #Hva] !>" (ρ v Hclv) "#Hg #[_ HvL]"; move: H =>?; iFrame (Hclv).
    iDestruct (interp_env_props with "Hg") as %[Hclp Hlen]; rewrite <- Hlen in *.

    iSpecialize ("Hva" with "Hg"); rewrite wp_value_inv'.
    iNext.
    iDestruct "Hva" as (Hclvas' d Hl Hcld φ) "#[Hlφ [#HLφ #HφU]]".

    iSpecialize ("HLφ" $! _ Hclv with "HvL").
    iExists φ, d; by repeat iSplit.
  Qed.

  Lemma Sel_Sub L U va l i:
    Γ ⊨ tv va : TTMem l L U, i -∗
    Γ ⊨ [TSel (pv va) l, i] <: [TLater U, i].
  Proof.
    iIntros "/= #[% #Hva] !>" (ρ v Hclv) "#Hg [$ #Hφ]". move: H =>?.
    iDestruct (interp_env_props with "Hg") as %[Hclp Hlen]; rewrite <- Hlen in *.

    iSpecialize ("Hva" with "Hg"); rewrite wp_value_inv'.
    iNext.
    iDestruct "Hva" as (Hclvas d Hl Hcld φ) "#[Hlφ [_ #HφU]]".
    iDestruct "Hφ" as (φ1 d1 Hva) "[Hγ #HΦ1v]".

    objLookupDet.
    iDestruct (stored_pred_agree d _ _ v with "Hlφ Hγ") as "#Hag".
    iApply "HφU" => //. repeat iModIntro. by iRewrite "Hag".
  Qed.
End Sec.
