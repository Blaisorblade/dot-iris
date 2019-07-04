From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr synLemmas.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section Sec.
  Context `{HdlangG: dlangG Σ} Γ.

  Lemma Sub_Sel_Path L U p l i:
    Γ ⊨p p : TTMem l L U, i -∗
    Γ ⊨ [TLater L, i] <: [TSel p l, i].
  Proof.
    iDestruct 1 as (j ->) "#Hp".
    iIntros "/= !>" (ρ v) "#Hg #Hφ /=".
    iSpecialize ("Hp" with "Hg").
    rewrite path_wp_wand.
    rewrite !laterN_plus.
    iApply "Hp"; iClear "Hp".
    iNext j. iNext (plength p).
    iIntros (w) "#Hp";
      iDestruct "Hp" as (d Hl φ) "#[Hlφ [#HLφ #HφU]]".
    iExists φ, d; repeat iSplit => //.
    by iApply "HLφ".
  Qed.

  Lemma Sel_Sub_Path L U p l i j:
    Γ ⊨p p : TTMem l L U, j -∗
    Γ ⊨ [TSel p l, i] <: [iterate TLater (j + 1) U, i].
  Proof.
    iDestruct 1 as (k ->) "#Hp".
    iIntros "/= !>" (ρ v) "#Hg #Hφ /=".
    rewrite iterate_TLater_later.
    iSpecialize ("Hp" with "Hg").
    rewrite !path_wp_eq !laterN_plus.
    iNext i.
    iDestruct "Hp" as (w) "[Hw Hp]".
    iDestruct "Hφ" as (w') "[Hw' Hφ]".
    rewrite !plength_subst_inv. iNext k.
    iDestruct (path_wp_det with "Hw Hw'") as "Heqw {Hw Hw'}".
    rewrite !plength_subst_inv.
    iNext (plength p).
    iDestruct "Heqw" as %<-.
    iDestruct "Hp" as (d Hl φ) "#[Hlφ [_ #HφU]]".
    iDestruct "Hφ" as (φ1 d1 Hva) "[Hγ #HΦ1v]".
    objLookupDet.
    iDestruct (dm_to_type_agree d _ _ v with "Hlφ Hγ") as "#Hag".
    iApply "HφU" => //. iNext. by iRewrite "Hag".
  Qed.

  Lemma P_Val v T:
    Γ ⊨ tv v : T -∗
    Γ ⊨p pv v : T, 0.
  Proof.
    iIntros "/= #Hp". iExists 0. iSplit => //.
    iIntros "!>" (ρ) "#Hg". iApply (wp_value_inv' with "(Hp Hg)").
  Qed.

  Lemma P_Mem_E p T l i:
    Γ ⊨p p : TVMem l T, i -∗
    (*─────────────────────────*)
    Γ ⊨p pself p l : T, S i.
  Proof.
    iDestruct 1 as (j ->) "#Hp /=". iExists j.
    iSplit; first auto with lia.
    iIntros "!>" (ρ) "#HG /=".
    iApply (path_wp_wand with "(Hp HG)").
    iNext. iIntros (v) "{Hp}".
    iDestruct 1 as (d Hl vmem ->) "Hv".
    iExists vmem. iSplit; eauto.
  Qed.
  (* In the above proof, in contrast with T_Mem_E, lots of the lemmas
     needed of path_wp hold simply by computation. *)

  Lemma P_DLater p T i :
    Γ ⊨p p : TLater T, i -∗
    Γ ⊨p p : T, S i.
  Proof.
    iDestruct 1 as (j ->) "#Hp".
    iExists (j + 1). iSplit; first auto with lia.
    iIntros "/= !>" (ρ) "#Hg".
    rewrite laterN_plus /= -path_wp_later_swap.
    iApply (path_wp_wand with "(Hp Hg)"); iNext j.
    by iIntros (v) "$".
  Qed.

  Lemma P_Sub0 p T1 T2 i j:
    Γ ⊨p p : T1, i -∗
    Γ ⊨ [T1, i - plength p] <: [T2, i + j - plength p] -∗
    (*───────────────────────────────*)
    Γ ⊨p p : T2, i + j.
  Proof.
    iDestruct 1 as (k ->) "#HpT1".
    iIntros "/= * #Hsub". iExists (k + j); iSplit; first auto with lia.
    iIntros "!> * #Hg".
    iSpecialize ("HpT1" with "Hg").
    rewrite !path_wp_eq plength_subst_inv.
    iDestruct "HpT1" as (v) "Hpv"; iExists v; iDestruct "Hpv" as "[$ HpT1]".
    rewrite -!(swap_laterN (plength p)).
    iNext (plength p).
    replace (k + plength p - plength p) with k by lia.
    replace (k + plength p + j - plength p) with (k + j) by lia.
    by iApply "Hsub".
  Qed.

  Lemma P_Sub p T1 T2 i j:
    Γ ⊨p p : T1, i -∗
    Γ ⊨ [T1, 0] <: [T2, j] -∗
    (*───────────────────────────────*)
    Γ ⊨p p : T2, i + j.
  Proof.
    iIntros "#HpT1 #Hsub". iApply (P_Sub0 with "HpT1").
    iIntros "!>" (vs v) "#Hg HT1".
    iDestruct "HpT1" as (k Heq) "_".
    rewrite (Nat.add_sub_swap _ j); last lia.
    rewrite laterN_plus. iNext (_ - plength p).
    by iApply "Hsub".
  Qed.
End Sec.
