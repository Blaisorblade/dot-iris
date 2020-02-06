From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms).

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  Lemma sSub_Sel_Path {Γ L U p l i}:
    Γ s⊨p p : cTMem l L U, i -∗
    Γ s⊨ oLater L, i <: oSel p l, i.
  Proof.
    iIntros "/= #Hp !>" (ρ v) "Hg #Hφ /=".
    iSpecialize ("Hp" with "Hg").
    iApply (path_wp_wand with "Hp").
    iIntros "!> !>" (w).
    iDestruct 1 as (d Hl φ) "#(Hlφ & #HLφ & #HφU)".
    iExists φ, d; repeat iSplit => //.
    by iApply "HLφ".
  Qed.

  Lemma Sub_Sel_Path {Γ L U p l i}:
    Γ ⊨p p : TTMem l L U, i -∗
    Γ ⊨ TLater L, i <: TSel p l, i.
  Proof. apply sSub_Sel_Path. Qed.

  Lemma sSel_Sub_Path {Γ L U p l i}:
    Γ s⊨p p : cTMem l L U, i -∗
    Γ s⊨ oSel p l, i <: oLater U, i.
  Proof.
    iIntros " #Hp !>" (ρ v) "Hg Hφ".
    iSpecialize ("Hp" with "Hg").
    iNext i.
    rewrite /= !path_wp_eq.
    iDestruct "Hp" as (w Hw d Hl φ) "#[Hlφ [_ #HφU]]".
    iDestruct "Hφ" as (w' Hw' φ1 d1 Hl') "[Hγ #HΦ1v]".
    rewrite -(path_wp_pure_det Hw Hw') {Hw Hw'} in Hl'.
    objLookupDet.
    iDestruct (dm_to_type_agree vnil v with "Hlφ Hγ") as "#Hag".
    iApply "HφU" => //. iNext. by iRewrite "Hag".
  Qed.

  Lemma Sel_Sub_Path {Γ L U p l i}:
    Γ ⊨p p : TTMem l L U, i -∗
    Γ ⊨ TSel p l, i <: TLater U, i.
  Proof. apply sSel_Sub_Path. Qed.

  Lemma sP_Fld_E {Γ} p T l i:
    Γ s⊨p p : cVMem l T, i -∗
    (*─────────────────────────*)
    Γ s⊨p pself p l : T, i.
  Proof.
    iIntros "#HE !>" (ρ) "HG /=".
    iSpecialize ("HE" with "HG"); iNext i.
    rewrite path_wp_eq path_wp_pself.
    iDestruct "HE" as (vp Hpv d Hlook pmem ->) "#H".
    iExists vp, pmem; eauto.
  Qed.
  (* In the above proof, in contrast with T_Obj_E, lots of the lemmas
     needed of path_wp hold simply by computation. *)

  Lemma sP_Later {Γ} p T i :
    Γ s⊨p p : oLater T, i -∗
    Γ s⊨p p : T, S i.
  Proof.
    iIntros "/= #Hp !>" (ρ) "Hg".
    rewrite -swap_later -path_wp_later_swap.
    iApply (path_wp_wand with "(Hp Hg)"); iNext i.
    by iIntros (v) "!> $".
  Qed.

  Lemma sP_Sub {Γ} p T1 T2 i j:
    Γ s⊨p p : T1, i -∗
    Γ s⊨ T1, i <: T2, i + j -∗
    (*───────────────────────────────*)
    Γ s⊨p p : T2, i + j.
  Proof.
    iIntros "/= * #HpT1 #Hsub !> * #Hg".
    iSpecialize ("HpT1" with "Hg").
    rewrite !path_wp_eq.
    iDestruct "HpT1" as (v) "Hpv"; iExists v; iDestruct "Hpv" as "[$ HpT1] {Hpv}".
    by iApply "Hsub".
  Qed.

  Lemma sP_Sub' {Γ} p T1 T2 i:
    Γ s⊨p p : T1, i -∗
    Γ s⊨ T1, i <: T2, i -∗
    (*───────────────────────────────*)
    Γ s⊨p p : T2, i.
  Proof. have := sP_Sub p T1 T2 i 0. by rewrite (plusnO i). Qed.
End Sec.
