Require Import Dot.tactics.
Require Import Dot.unary_lr.
Require Import Dot.synLemmas.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section Sec.
  Context `{HdotG: dotG Σ}.

  Context (Γ: list ty).

  Lemma mem_stp_sela_sub L U va l:
    ivtp Γ (TTMem l L U) va -∗
    Γ ⊨ L <: TSelA (pv va) l L U.
  Proof.
    iIntros "#Hva".
    iApply istpEqIvstp.
    (* cbn [interp uinterp interp_tmem]. *)
    (* cbn [interp_tmem]. *)
    (* unfold interp_tmem, defs_interp_tmem. *)
    iIntros "/= !>" (v ρ) "#Hg #HvL".
    iDestruct ("Hva" $! ρ with "Hg") as (ds) "#[% #H]"; iClear "Hva".
    iDestruct "H" as (φ σ) "#[Hl [#HLφ [#HφU #HLU]]]".
    simplOpen ds'; simpl.
    iExists (vobj ds'), σ, φ, ds.
    (* TODO: prove a variant of istpEqIvstp, but one that is applicable here. *)
  Admitted.
  (*   repeat iModIntro. *)
  (*   repeat iSplit; trivial. *)
  (*   - iApply "HLU"; iApply "HvL". *)
  (*   - *)
  (*     (* Either *) *)
  (*     (* by iLeft. *) *)
  (*     (* Or *) *)
  (*     iRight; iApply "HLφ"; iApply "HvL". *)
  (* Qed. *)

  Lemma mem_stp_sel_sub L U va l:
    ivtp Γ (TTMem l L U) va -∗
    ivstp Γ (TLater L) (TSel (pv va) l).
  Proof.
    iIntros "/= #Hva !>" (v ρ) "#Hg #HvL !>".
    iDestruct ("Hva" $! ρ with "Hg") as (ds) "#[% #H]"; iClear "Hva".
    iDestruct "H" as (φ σ) "#[Hl [#HLφ [#HφU #HLU]]]".
    simplOpen ds'; simpl.
    iExists (vobj ds'), σ , φ, ds.
    repeat iSplit; trivial.
  Admitted.
  (*   iRight; iApply "HLφ". iApply "HvL". *)
  (* Qed. *)

  Lemma mem_stp_sub_sel L U va l:
    ivtp Γ (TTMem l L U) va -∗
    ivstp Γ (TSel (pv va) l) (TLater U).
  Proof.
    iIntros "/= #Hva !>" (v ρ) "#Hg #Hφ".
    iDestruct ("Hva" $! ρ with "Hg") as (ds) "#[% #H]"; iClear "Hva".
    iDestruct "H" as (φ σ) "#[Hlφ [HLφ [HφU #HLU]]]".
    iDestruct "Hlφ" as (γ) "[% Hγφ]".
  Admitted.

  (*   iApply "HφU". *)
  (*   simplOpen ds'; simpl. *)
  (*   iDestruct "Hφ" as (va1 σ1 φ1 ds1) "[% [% [Hlφ1 [_ [[] | Hφ1v]]]]] /=". *)
  (*   iDestruct "Hlφ1" as (γ1) "[% Hγφ1]". *)

  (*   injectHyps; openDet; optFuncs_det. *)

  (*   iAssert (▷ (subst_phi σ ρ φ v ≡ subst_phi σ ρ φ1 v))%I as "#Hag"; simpl. *)
  (*   { by iApply saved_pred_agree. } *)
  (*   iNext; by iRewrite "Hag". *)
  (* Qed. *)
End Sec.
