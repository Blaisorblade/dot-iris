From iris.proofmode Require Import tactics.
From D Require Import tactics.
From D.Dot Require Import unary_lr.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section Sec.
  Context `{HdotG: dotG Σ} Γ.

  Lemma mem_stp_sel_sub L U va l:
    ivtp Γ (TTMem l L U) va -∗
    Γ ⊨ TLater L <: TSel (pv va) l.
  Proof.
    iIntros "/= #[% Hva] !> * #Hg #[% HvL]". move: H H0 => Hclva Hclv.
    iDestruct ("Hva" $! ρ with "Hg") as (Hclvas d Hl Hcld φ) "#H"; iClear "Hva".
    iDestruct "H" as "#[Hl [#HLφ #HφU]]".
    repeat iSplit => //.
    iExists φ, d.
    iDestruct ("HLφ" $! _ Hclv with "HvL") as "#HLφ'".
    by repeat iSplit.
  Qed.

  Instance Inhϕ: Inhabited (listVlC -n> vlC -n> iProp Σ).
  Proof. constructor. exact (λne _ _, False)%I. Qed.

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

  Lemma mem_stp_sub_sel L U va l:
    ivtp Γ (TTMem l L U) va -∗
    ivstp Γ (TSel (pv va) l) (TLater U).
  Proof.
    cbn.
    iIntros "/= #[% Hva] !> * #Hg #[$ #Hφ]". move: H => Hclva.
    iDestruct ("Hva" $! ρ with "Hg") as (Hclvas d Hl Hcld φ) "#[#Hlφ [#HLφ #HφU]]"; iClear "Hva".
    iDestruct "Hφ" as (φ1 d1 Hva) "[Hγ #HΦ1v]".
    objLookupDet; subst. iPoseProof (stored_pred_agree d _ _ v with "Hlφ Hγ") as "#Hag".
    iApply "HφU" => //. repeat iModIntro. by iRewrite "Hag".
  Qed.
End Sec.
