From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.
From Dot Require Import operational tactics unary_lr synLemmas.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section Sec.
  Context `{HdotG: dotG Σ}.

  Context (Γ: list ty).

  (** Show that inclusion between postconditions is equivalent to inclusion
      between value predicates *with an update modality. This is useful to show
      equivalent value and expression subtyping, both for a fixed environment and
      for environments matching a [Γ].
   *)
  Lemma mem_stp_sela_sub L U va l:
    ivtp Γ (TTMem l L U) va -∗
    Γ ⊨ L <: TSelA (pv va) l L U.
  Proof.
    iIntros "[% #Hva] /= !> * #Hg" (Hclv) "#HvL". move: H => Hclva.
    iDestruct ("Hva" $! ρ with "Hg") as (d) "#[% #H]"; iClear "Hva".
    iDestruct "H" as (φ σ) "#[Hl [#HLφ [#HφU #HLU]]]".
    repeat iSplit; first by iApply "HLU".
    iRight.
    iExists σ, φ, d.
    iDestruct ("HLφ" with "HvL") as "#HLφ'".
    iDestruct ("HLU" with "HvL") as "#HLU'".
    repeat iModIntro; by repeat iSplit.
  Qed.

  Lemma mem_stp_sel_sub L U va l:
    ivtp Γ (TTMem l L U) va -∗
    ivstp Γ (TLater L) (TSel (pv va) l).
  Proof.
    iIntros "/= [% #Hva] !> * #Hg" (Hclv) "#HvL".
    iDestruct ("Hva" $! ρ with "Hg") as (d) "#[% #H]"; iClear "Hva".
    iDestruct "H" as (φ σ) "#[Hl [#HLφ [#HφU #HLU]]]".
    repeat iSplit; first done.
    iRight.
    iExists σ , φ, d.
    iDestruct ("HLφ" with "HvL") as "#HLφ'".
    repeat iModIntro; by repeat iSplit.
  Qed.

  Instance Inhϕ: Inhabited (list vl * vl → iProp Σ).
  Proof. constructor. exact (λ _, False)%I. Qed.

  (* Next step: proper lemma on arbitrary-length paths. *)
  Lemma mem_stp_sel_sub_path1 L U va l1 l2:
    (ivtp Γ (TVMem l1 (TTMem l2 L U)) va -∗
    ivstp Γ (TLater L) ((TSel (pself (pv va) l1) l2)))%I.
  Proof.
    iIntros "/= [% #Hva] !> * #Hg % #HvL".

    iDestruct ("Hva" $! ρ with "Hg") as (d) "#[% #Hvb]"; iClear "Hva".
    iDestruct "Hvb" as (vmem) "[-> H1]".
    iDestruct "H1" as (d) "[Hl2 H]".
    iDestruct "H" as (φ σ) "#[Hl [#HLφ [#HφU #HLU]]]".
    iDestruct ("HLφ" with "HvL") as "HLφ'".
    repeat iSplit; first done.
    iRight.
    iExists vmem.
    repeat iSplit; try done.
    iExists σ , φ, d.
    repeat iModIntro; by repeat iSplit.
  Qed.

  Lemma mem_stp_sub_sel L U va l:
    ivtp Γ (TTMem l L U) va -∗
    ivstp Γ (TSel (pv va) l) (TLater U).
  Proof.
    iIntros "/= [% #Hva] !> * #Hg % #[_ [[] | Hφ]]".
    iDestruct ("Hva" $! ρ with "Hg") as (d) "#[% #H]"; iClear "Hva".
    iDestruct "H" as (φ σ) "#[Hlφ [HLφ [HφU #HLU]]]".
    iDestruct "Hlφ" as (γ) "[% Hγφ]".

    iApply "HφU".
    iDestruct "Hφ" as (σ1 φ1 d1 Hva) "[Hγ #HΦ1v]".
    (* " [_ [False | #HΦ1v]]]"; try done. *)
    iDestruct "Hγ" as (γ' Hd1) "HγΦ1".

    injectHyps; subst; objLookupDet.

    iAssert (∀ ρ v, ▷ (φ ρ v ≡ φ1 ρ v))%I as "#Hag".
    { iIntros.
      (* Paolo: This manual eta-expansion is needed to get coercions to apply. *)
      by iApply (saved_interp_agree_eta γ (λ a, φ a) (λ a, φ1 a) ρ0 v0).
    }

    (* iAssert (▷ (subst_phi σ ρ φ v ≡ subst_phi σ ρ φ1 v))%I as "#Hag"; simpl. *)
    (*  ▷ (subst_phi σ ρ φ v ≡ subst_phi σ ρ φ1 v))%I as "#Hag". simpl. *)
    (* { qy iApply saved_pred_agree. } *)
    repeat iModIntro.
    by iRewrite ("Hag" $! σ v).
  Qed.
End Sec.
