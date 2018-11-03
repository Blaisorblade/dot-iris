Require Import Dot.dotsyn.
Require Import Dot.operational.
Require Import Dot.unary_lr.
Import lang.

From iris Require Import base_logic.lib.saved_prop.
(* From iris Require Import base_logic.base_logic. *)

From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.algebra Require Import list.
From iris.base_logic Require Import invariants.

Section Sec.
  Context `{HdotG: dotG Σ}.
  Definition vstp Γ T1 T2 := ∀ v ρ, interp_env Γ ρ -> interp T1 ρ v -> interp T2 ρ v.
  Definition ivstp Γ T1 T2: iProp Σ := (□∀ v ρ, interp_env Γ ρ -∗ interp T1 ρ v -∗ interp T2 ρ v)%I.
  Arguments vstp /.
  Arguments ivstp /.
  Context (Γ: list ty).

  (* Lemma stp_later T ρ v: interp T ρ v -∗ interp (TLater T) ρ v. *)
  (* Proof. iIntros; by iNext. Qed. *)
  Lemma ivstp_later T: ivstp Γ T (TLater T).
  Proof. iIntros "!> ** /="; by iNext. Qed.

  Lemma ivstp_ande1 T1 T2: ivstp Γ (TAnd T1 T2) T1.
  Proof. by iIntros "/= !> * ? [? ?]". Qed.
  Lemma ivstp_ande2 T1 T2: ivstp Γ (TAnd T1 T2) T2.
  Proof. by iIntros "/= !> * ? [? ?]". Qed.

  Lemma stp_andi T1 T2 ρ v:
    interp T1 ρ v -∗
    interp T2 ρ v -∗
    interp (TAnd T1 T2) ρ v.
  Proof. iIntros; by iSplit. Qed.

  Lemma vstp_andi S T1 T2:
    vstp Γ S T1 ->
    vstp Γ S T2 ->
    vstp Γ S (TAnd T1 T2).
  Proof. move => /= H1 H2 v ρ Hg HS; by iSplit; [iApply H1 | iApply H2]. Qed.

  Lemma ivstp_andi S T1 T2:
    ivstp Γ S T1 -∗
    ivstp Γ S T2 -∗
    ivstp Γ S (TAnd T1 T2).
  Proof.
    iIntros "/= #H1 #H2 !> * #Hg #HS".
    iApply stp_andi; [iApply "H1" | iApply "H2"]; done.
  Qed.

  Lemma stp_ori1 T1 T2 ρ v: interp T1 ρ v -∗ interp (TOr T1 T2) ρ v.
  Proof. iIntros "? /="; by iLeft. Qed.
  Lemma stp_ori2 T1 T2 ρ v: interp T2 ρ v -∗ interp (TOr T1 T2) ρ v.
  Proof. iIntros "? /="; by iRight. Qed.

  Lemma ivstp_ore S T1 T2:
    ivstp Γ T1 S -∗
    ivstp Γ T2 S -∗
    ivstp Γ (TOr T1 T2) S.
  Proof. iIntros "/= #H1 #H2 !> * #Hg #[HT1 | HT2]"; [iApply "H1" | iApply "H2"]; done. Qed.

  Lemma ivstp_ori1 T1 T2: ivstp Γ T1 (TOr T1 T2).
  Proof. iIntros "!> ** /="; by iLeft. Qed.
  Lemma ivstp_ori2 T1 T2: ivstp Γ T2 (TOr T1 T2).
  Proof. iIntros "!> ** /="; by iRight. Qed.

  Definition ivtp Γ T v: iProp Σ := (□∀ ρ, interp_env Γ ρ -∗ interp T ρ v)%I.
  Arguments ivtp /.

  Lemma mem_stp_sela_sub L U va l:
    ivtp Γ (TTMem l L U) va -∗
    ivstp Γ L (TSelA (pv va) l L U).
  Proof.
    iIntros "/= #Hva !>" (v ρ) "#Hg #HvL !>".
    iPoseProof ("Hva" $! ρ with "Hg") as (ϕ) "#[Hlookup [HLϕ HϕU]]"; iClear "Hva".
    iDestruct "Hlookup" as (γ ds) "[[-> %] HSP] /=".
    iExists γ, ϕ, ds.
    repeat iSplit; try done.
    - iApply "HϕU". iApply "HLϕ". iApply "HvL".
    -
      (* Either *)
      (* by iLeft. *)
      (* Or *)
      iRight; iApply "HLϕ"; iApply "HvL".
  Qed.

  (* XXX this is weaker than we want: we should be able to prove that even (TLater L). *)
  (* Very weird: we can use a saved predicate *now*, not later, because we do
     not need to prove that ϕ agrees with anything else.
     So either we get an issue elsewhere (and must readd the missing later from the definition),
     or somehow this model is more powerful than expected. *)
  Lemma mem_stp_sel_sub L U va l:
    ivtp Γ (TTMem l L U) va -∗
    ivstp Γ L (TSel (pv va) l).
  Proof.
    iIntros "/= #Hva !>" (v ρ) "#Hg #HvL !>".
    iPoseProof ("Hva" $! ρ with "Hg") as (ϕ) "#[Hlookup [HLϕ HϕU]]"; iClear "Hva".
    iDestruct "Hlookup" as (γ ds) "[[-> %] HSP] /=".
    iExists γ, ϕ, ds.
    repeat iSplit; try done.
    iRight; iApply "HLϕ"; iApply "HvL".
  Qed.

  Lemma mem_stp_sub_sel L U va l:
    ivtp Γ (TTMem l L U) va -∗
    ivstp Γ (TSel (pv va) l) (TLater U).
  Proof.
    iIntros "/= #Hva !>" (v ρ) "#Hg #Hϕ".
    iPoseProof ("Hva" $! ρ with "Hg") as (ϕ) "#[Hlookup [HLϕ HϕU]]"; iClear "Hva".
    iDestruct "Hlookup" as (γ ds) "[[-> %] HSPϕ] /=". move:H=>Hγ.
    iApply "HϕU".
    iDestruct "Hϕ" as (γ1 ϕ1 ds1) "[[% %] [HSPϕ1 [_ [[] | Hϕ1v]]]] /=".
    move:H H0=>[<-] Hγ1; rewrite Hγ in Hγ1. move :Hγ1 =>[<-].
    iAssert (▷ (ϕ v ≡ ϕ1 v))%I as "#Hag".
    { by iApply saved_pred_agree. }
    iNext; by iRewrite "Hag".
  Qed.

End Sec.
