Require Import Dot.tactics.
Require Import Dot.unary_lr.

Section Sec.
  Context `{HdotG: dotG Σ}.

  Context (Γ: list ty).
  Implicit Types T: ty.

  Lemma mem_stp_sela_sub L U va l:
    ivtp Γ (TTMem l L U) va -∗
    Γ ⊨ L <: TSelA (pv va) l L U.
  Proof.
    iIntros "/= #Hva !>" (v ρ) "#Hg #HvL !>".
    iDestruct ("Hva" $! ρ with "Hg") as (ds) "#[% #H]"; iClear "Hva".
    iDestruct "H" as (φ) "#[Hl [HLφ HφU]]".
    simplOpen ds'; simpl.
    iExists (vobj ds'), φ, ds.
    repeat iSplit; trivial.
    - iApply "HφU"; iApply "HLφ"; iApply "HvL".
    -
      (* Either *)
      (* by iLeft. *)
      (* Or *)
      iRight; iApply "HLφ"; iApply "HvL".
  Qed.

  Lemma mem_stp_sel_sub L U va l:
    ivtp Γ (TTMem l L U) va -∗
    ivstp Γ (TLater L) (TSel (pv va) l).
  Proof.
    iIntros "/= #Hva !>" (v ρ) "#Hg #HvL !>".
    iDestruct ("Hva" $! ρ with "Hg") as (ds) "#[% #H]"; iClear "Hva".
    iDestruct "H" as (φ) "#[Hl [HLφ HφU]]".
    simplOpen ds'; simpl.
    iExists (vobj ds'), φ, ds.
    repeat iSplit; trivial.
    iRight; iApply "HLφ". iApply "HvL".
  Qed.

  Lemma mem_stp_sub_sel L U va l:
    ivtp Γ (TTMem l L U) va -∗
    ivstp Γ (TSel (pv va) l) (TLater U).
  Proof.
    iIntros "/= #Hva !>" (v ρ) "#Hg #Hφ".
    iDestruct ("Hva" $! ρ with "Hg") as (ds) "#[% #H]"; iClear "Hva".
    iDestruct "H" as (φ) "#[Hlφ [HLφ HφU]]".
    iDestruct "Hlφ" as (γ) "[% Hγφ]".

    iApply "HφU".
    simplOpen ds'; simpl.
    iDestruct "Hφ" as (va1 φ1 ds1) "[% [% [Hlφ1 [_ [[] | Hφ1v]]]]] /=".
    iDestruct "Hlφ1" as (γ1) "[% Hγφ1]".

    injectHyps; openDet; optFuncs_det.

    iAssert (▷ (φ v ≡ φ1 v))%I as "#Hag".
    { by iApply saved_pred_agree. }
    iNext; by iRewrite "Hag".
  Qed.
End Sec.
