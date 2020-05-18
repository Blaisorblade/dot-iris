(** * Semantic typing lemmas about type selections (and path typing). *)
From D.Dot Require Import unary_lr.

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Section Sec.
  Context `{HdlangG: !dlangG Σ}.

  (* Suppose path typing required termination *now* rather than later:

    Definition sptp `{!dlangG Σ} p i Γ (T : oltyO Σ 0): iProp Σ :=
     □∀ ρ, sG⟦Γ⟧* ρ →
-      ▷^i path_wp (p.|[ρ]) (λ v, oClose T ρ v).
+      path_wp (p.|[ρ]) (λ v, ▷^i oClose T ρ v).

  Then this lemma would already fail: the hypothesis implies that [p]
  terminates now, but that [pself p l] terminates *only under later^i*!
  *)
  Lemma sP_Fld_E {Γ} p T l i:
    Γ s⊨p p : cVMem l T, i -∗
    (*─────────────────────────*)
    Γ s⊨p pself p l : T, i.
  Proof.
    iIntros "#HE !> %ρ HG /=".
    iSpecialize ("HE" with "HG"); iNext i.
    rewrite path_wp_eq path_wp_pself_eq.
    iDestruct "HE" as (vp Hpv d Hlook pmem ->) "#H".
    iExists vp, pmem; eauto.
  Qed.
  (* In the above proof, in contrast with T_Obj_E, lots of the lemmas
     needed of path_wp hold simply by computation. *)

  Lemma sP_Sub {Γ p T1 T2 i j}:
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
  Proof. have := @sP_Sub Γ p T1 T2 i 0. by rewrite (plusnO i). Qed.

  (* Derivable, kept for examples. *)
  Lemma sP_Later {Γ} p T i :
    Γ s⊨p p : oLater T, i -∗
    Γ s⊨p p : T, S i.
  Proof.
    rewrite (sP_Sub (j := 1) (T1 := oLater T) (T2 := T)); iIntros "Hsub".
    rewrite (plusnS i 0) (plusnO i).
    iApply "Hsub".
    iIntros "/= !> %ρ %v Hg $".
  Qed.
End Sec.
