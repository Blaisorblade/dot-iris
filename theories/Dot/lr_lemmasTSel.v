From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr synLemmas.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section Sec.
  Context `{HdlangG: dlangG Σ} Γ.

  Lemma Sub_Sel_Path L U p l i:
    Γ ⊨ p : TTMem l L U, i -∗
    Γ ⊨ iterate TLater (S (plength p)) L, i <: TSel p l, i.
  Proof.
    rewrite iterate_S.
    iIntros "/= #Hp !>" (ρ v) "#Hg #Hφ /=".
    iSpecialize ("Hp" with "Hg").
    iNext i.

    rewrite iterate_TLater_later
      strong_path_wp_wand plength_subst_inv -swap_later.
    iApply "Hp".
    iNext (plength p); iIntros (w).
    iDestruct 1 as (d Hl φ) "{Hp} #(Hlφ & #HLφ & #HφU)".
    iExists φ, d; repeat iSplit => //.
    by iApply "HLφ".
  Qed.

  Lemma Sel_Sub_Path L U p l i:
    Γ ⊨ p : TTMem l L U, i -∗
    Γ ⊨ TSel p l, i <: iterate TLater (S (plength p)) U, i.
  Proof.
    rewrite iterate_S.
    iIntros "/= #Hp !>" (ρ v) "#Hg #Hφ /=".
    iSpecialize ("Hp" with "Hg").
    iNext i.
    rewrite iterate_TLater_later !path_wp_eq.
    iDestruct "Hp" as (w) "[Hw Hp]".
    iDestruct "Hφ" as (w') "[Hw' Hφ]".
    iDestruct (path_wp_det with "Hw Hw'") as "{Hw Hw'} Heqw".
    rewrite !plength_subst_inv -swap_later; iNext (plength p).
    iDestruct "Heqw" as %<-.
    iDestruct "Hp" as (d Hl φ) "#[Hlφ [_ #HφU]]".
    iDestruct "Hφ" as (φ1 d1 Hva) "[Hγ #HΦ1v]".
    objLookupDet.
    iDestruct (dm_to_type_agree d _ _ v with "Hlφ Hγ") as "#Hag".
    iApply "HφU" => //. iNext. by iRewrite "Hag".
  Qed.

  Lemma P_Val v T:
    Γ ⊨ tv v : T -∗
    Γ ⊨ pv v : T, 0.
  Proof.
    iIntros "/= #Hp !>" (ρ) "#Hg".
    iSpecialize ("Hp" with "Hg"); rewrite wp_value_inv'. by [].
  Qed.

  Lemma P_Mem_E p T l i:
    Γ ⊨ p : TVMem l T, i -∗
    (*─────────────────────────*)
    Γ ⊨ pself p l : T, i.
  Proof.
    iIntros "#HE !>" (ρ) "#HG /=".
    iApply (path_wp_wand with "(HE HG)"); iNext i.
    iIntros (v) "{HE} #Hv".
    iDestruct "Hv" as (d Hl vmem ->) "Hv".
    iExists vmem. iSplit; eauto.
  Qed.
  (* In the above proof, in contrast with T_Mem_E, lots of the lemmas
     needed of path_wp hold simply by computation. *)

  Lemma P_DLater p T i :
    Γ ⊨ p : TLater T, i -∗
    Γ ⊨ p : T, S i.
  Proof.
    iIntros "/= #Hp !>" (ρ) "#Hg".
    rewrite -swap_later -path_wp_later_swap.
    iApply (path_wp_wand with "(Hp Hg)"); iNext i.
    by iIntros (v) "$".
  Qed.

  Lemma P_Sub p T1 T2 i j:
    Γ ⊨ p : T1, i -∗
    Γ ⊨ T1, i <: T2, i + j -∗
    (*───────────────────────────────*)
    Γ ⊨ p : T2, i + j.
  Proof.
    iIntros "/= * #HpT1 #Hsub !> * #Hg".
    iSpecialize ("HpT1" with "Hg").
    rewrite !path_wp_eq plength_subst_inv.
    iDestruct "HpT1" as (v) "Hpv"; iExists v; iDestruct "Hpv" as "[$ HpT1] {Hpv}".
    rewrite -!(swap_laterN (plength p)); iNext (plength p).
    by iApply "Hsub".
  Qed.
End Sec.
