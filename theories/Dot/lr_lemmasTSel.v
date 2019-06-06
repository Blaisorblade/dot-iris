From iris.proofmode Require Import tactics.
From D Require Import tactics proofmode_extra.
From D.Dot Require Import unary_lr synLemmas.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section Sec.
  Context `{HdlangG: dlangG Σ} Γ.

  Lemma Sub_Sel_Path L U p l i:
    Γ ⊨p p : TTMem l L U, i -∗
    Γ ⊨ [iterate TLater (S (plength p)) L, i] <: [TSel p l, i].
  Proof.
    rewrite iterate_S.
    iIntros "/= [% #Hp] !>" (ρ v Hclv) "#Hg [$ #Hφ] /=". move: H => Hclp.
    iDestruct (interp_env_props with "Hg") as %[Hclρ Hlen]; rewrite <- Hlen in *.
    iSpecialize ("Hp" with "Hg").
    iNext i.

    rewrite iterate_TLater_later //
      strong_path_wp_wand plength_subst_inv -swap_later.
    iApply "Hp"; iClear "Hp".
    iNext (plength p); iIntros (w) "#Hp";
      iDestruct "Hp" as (Hclvas d Hl φ) "#[Hlφ [#HLφ #HφU]]".
    iExists φ, d; repeat iSplit => //.
    by iApply "HLφ".
  Qed.

  Lemma Sel_Sub_Path L U p l i:
    Γ ⊨p p : TTMem l L U, i -∗
    Γ ⊨ [TSel p l, i] <: [iterate TLater (S (plength p)) U, i].
  Proof.
    rewrite iterate_S.
    iIntros "/= #[% #Hp] !>" (ρ v Hclv) "#Hg [$ #Hφ] /=". move: H => Hclp.
    iDestruct (interp_env_props with "Hg") as %[Hclρ Hlen]; rewrite <- Hlen in *.
    iSpecialize ("Hp" with "Hg").
    iNext i.
    rewrite iterate_TLater_later // !path_wp_eq.
    iDestruct "Hp" as (w) "[Hw [Hclw Hp]]".
    iDestruct "Hφ" as (w') "[Hw' Hφ]".
    iDestruct (path_wp_det with "Hw Hw'") as "Heqw"; iClear "Hw Hw'".
    rewrite !plength_subst_inv -swap_later; iNext (plength p).
    iDestruct "Heqw" as %<-.
    iDestruct "Hp" as (d Hl φ) "#[Hlφ [_ #HφU]]".
    iDestruct "Hφ" as (φ1 d1 Hva) "[Hγ #HΦ1v]".
    objLookupDet.
    iDestruct (stored_pred_agree d _ _ v with "Hlφ Hγ") as "#Hag".
    iApply "HφU" => //. iNext. by iRewrite "Hag".
  Qed.

  Lemma P_Val v T:
    Γ ⊨ tv v : T -∗
    Γ ⊨p pv v : T, 0.
  Proof.
    iIntros "/= #[% #Hp]". iSplit; eauto using fv_tv_inv, fv_pv.
    iIntros "!>" (ρ) "#Hg".
    iSpecialize ("Hp" with "Hg"); rewrite wp_value_inv'. by [].
  Qed.

  Lemma P_Mem_E p T l i:
    Γ ⊨p p : TVMem l T, i -∗
    (*─────────────────────────*)
    Γ ⊨p pself p l : T, i.
  Proof.
    iIntros "[% #HE]"; iSplit; auto using fv_pself. iIntros " !>" (ρ) "#HG /=".
    iApply (path_wp_wand with "(HE HG)"); iClear "HE".
    iNext.
    iIntros (v) "#[_ Hv]".
    iDestruct "Hv" as (d Hl vmem ->) "Hv".
    iExists vmem. iSplit; eauto.
  Qed.
  (* In the above proof, in contrast with T_Mem_E, lots of the lemmas
     needed of path_wp hold simply by computation. *)

  Lemma P_DLater p T i :
    Γ ⊨p p : TLater T, i -∗
    Γ ⊨p p : T, S i.
  Proof.
    iIntros "/= [$ #Hp] !>" (ρ) "#Hg".
    rewrite -swap_later -path_wp_later_swap.
    iApply (path_wp_wand with "(Hp Hg)"); iNext i.
    by iIntros (v) "[% $]".
  Qed.

  Lemma P_Sub p T1 T2 i j:
    Γ ⊨p p : T1, i -∗
    Γ ⊨ [T1, i] <: [T2, i + j] -∗
    (*───────────────────────────────*)
    Γ ⊨p p : T2, i + j.
  Proof.
    iIntros "/= * #[% #HpT1] #Hsub"; iSplit => //; iIntros "!> * #Hg".
    iDestruct (interp_env_props with "Hg") as %[Hclp Hlen]; rewrite <- Hlen in *.
    iSpecialize ("HpT1" with "Hg").
    rewrite !path_wp_eq plength_subst_inv.
    iDestruct "HpT1" as (v) "Hpv"; iExists v; iDestruct "Hpv" as "[$ HpT1]".
    rewrite (path_wp_cl 0) plength_subst_inv -!(swap_laterN (plength p)).
    iNext (plength p).
    iApply (strip_pure_laterN_wand' i j _ with "[] Hpv"); iIntros (Hclpv).
    have Hclv: nclosed_vl v 0. by apply Hclpv, fv_to_subst.
    by iApply "Hsub".
  Qed.
End Sec.
