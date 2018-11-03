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
  Proof. simpl; iIntros "!> **"; by iNext. Qed.

  Lemma ivstp_ande1 T1 T2: ivstp Γ (TAnd T1 T2) T1.
  Proof. simpl; by iIntros "!> * ? [? ?]". Qed.
  Lemma ivstp_ande2 T1 T2: ivstp Γ (TAnd T1 T2) T2.
  Proof. simpl; by iIntros "!> * ? [? ?]". Qed.

  Lemma stp_andi T1 T2 ρ v:
    interp T1 ρ v -∗
    interp T2 ρ v -∗
    interp (TAnd T1 T2) ρ v.
  Proof. iIntros; by iSplit. Qed.

  Lemma vstp_andi S T1 T2:
    vstp Γ S T1 ->
    vstp Γ S T2 ->
    vstp Γ S (TAnd T1 T2).
  Proof.
    simpl; intros * H1 H2 **.
    by iSplit; [iApply H1 | iApply H2].
  Qed.

  Lemma ivstp_andi S T1 T2:
    ivstp Γ S T1 -∗
    ivstp Γ S T2 -∗
    ivstp Γ S (TAnd T1 T2).
  Proof.
    iIntros "/= #H1 #H2 !> * #Hg #HS".
    iApply stp_andi; [iApply "H1" | iApply "H2"]; done.
  Qed.

  Lemma stp_ori1 T1 T2 ρ v: interp T1 ρ v -∗ interp (TOr T1 T2) ρ v.
  Proof. simpl; iIntros; by iLeft. Qed.
  Lemma stp_ori2 T1 T2 ρ v: interp T2 ρ v -∗ interp (TOr T1 T2) ρ v.
  Proof. simpl; iIntros; by iRight. Qed.

  Lemma ivstp_ore S T1 T2:
    ivstp Γ T1 S -∗
    ivstp Γ T2 S -∗
    ivstp Γ (TOr T1 T2) S.
  Proof.
    iIntros "/= #H1 #H2 !> * #Hg #HT".
    iDestruct "HT" as "[HT1 | HT2]"; [iApply "H1" | iApply "H2"]; done.
  Qed.

  Lemma ivstp_ori1 T1 T2: ivstp Γ T1 (TOr T1 T2).
  Proof. iIntros "!> ** /="; by iLeft. Qed.
  Lemma ivstp_ori2 T1 T2: ivstp Γ T2 (TOr T1 T2).
  Proof. iIntros "!> ** /="; by iRight. Qed.
End Sec.
