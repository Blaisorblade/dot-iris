From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section Sec.
  Context `{HdlangG: dlangG Σ} Γ.

  Lemma Sub_Sel_Path L U p l i:
    Γ ⊨p p : TTMem l L U, i -∗
    Γ ⊨ TLater L, i <: TSel p l, i.
  Proof.
    iIntros "/= #Hp !>" (ρ v) "Hg Hφ /=".
    iSpecialize ("Hp" with "Hg").
    iApply (path_wp_wand with "Hp").
    iIntros "!>" (w).
    iDestruct 1 as (d Hl φ) "#(Hlφ & #HLφ & #HφU)".
    iExists φ, d; repeat iSplit => //.
    by iApply "HLφ".
  Qed.

  Lemma Sel_Sub_Path L U p l i:
    Γ ⊨p p : TTMem l L U, i -∗
    Γ ⊨ TSel p l, i <: TLater U, i.
  Proof.
    iIntros "/= #Hp !>" (ρ v) "Hg Hφ".
    iSpecialize ("Hp" with "Hg").
    iNext i.
    rewrite !path_wp_eq.
    iDestruct "Hp" as (w Hw d Hl φ) "#[Hlφ [_ #HφU]]".
    iDestruct "Hφ" as (w' Hw' φ1 d1 Hl') "[Hγ #HΦ1v]".
    rewrite -(path_wp_pure_det Hw Hw') {Hw Hw'} in Hl'.
    objLookupDet.
    iDestruct (dm_to_type_agree d _ _ v with "Hlφ Hγ") as "#Hag".
    iApply "HφU" => //. iNext. by iRewrite "Hag".
  Qed.

  Lemma P_Mem_E p T l i:
    Γ ⊨p p : TVMem l T, i -∗
    (*─────────────────────────*)
    Γ ⊨p pself p l : T, i.
  Proof.
    iIntros "#HE !>" (ρ) "HG /=".
    iSpecialize ("HE" with "HG"); iNext i.
    rewrite path_wp_eq path_wp_pself.
    iDestruct "HE" as (vp Hpv d Hlook pmem ->) "H".
    iExists vp, pmem; eauto.
  Qed.
  (* In the above proof, in contrast with T_Mem_E, lots of the lemmas
     needed of path_wp hold simply by computation. *)

  Lemma P_DLater p T i :
    Γ ⊨p p : TLater T, i -∗
    Γ ⊨p p : T, S i.
  Proof.
    iIntros "/= #Hp !>" (ρ) "Hg".
    rewrite -swap_later -path_wp_later_swap.
    iApply (path_wp_wand with "(Hp Hg)"); iNext i.
    by iIntros (v) "$".
  Qed.

  Lemma P_Sub p T1 T2 i j:
    Γ ⊨p p : T1, i -∗
    Γ ⊨ T1, i <: T2, i + j -∗
    (*───────────────────────────────*)
    Γ ⊨p p : T2, i + j.
  Proof.
    iIntros "/= * #HpT1 #Hsub !> * #Hg".
    iSpecialize ("HpT1" with "Hg").
    rewrite !path_wp_eq.
    iDestruct "HpT1" as (v) "Hpv"; iExists v; iDestruct "Hpv" as "[$ HpT1] {Hpv}".
    by iApply "Hsub".
  Qed.

  Lemma P_Sub' p T1 T2 i:
    Γ ⊨p p : T1, i -∗
    Γ ⊨ T1, i <: T2, i -∗
    (*───────────────────────────────*)
    Γ ⊨p p : T2, i.
  Proof. have := P_Sub p T1 T2 i 0. by rewrite (plusnO i). Qed.
End Sec.
