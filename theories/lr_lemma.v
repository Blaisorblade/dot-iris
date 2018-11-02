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

  Lemma stp_later T ρ v : interp T ρ v -> interp (TLater T) ρ v.
  Proof. intro h. simpl; iNext. iApply h. Qed.

  Lemma stp_and1 T1 T2 ρ v: interp (TAnd T1 T2) ρ v -> interp T1 ρ v.
  Proof.
    simpl in *. intros Hv.
    iDestruct Hv as "[H1 H2]".
    iAssumption.
  Qed.

  Lemma stp_and2 T1 T2 ρ v: interp (TAnd T1 T2) ρ v -> interp T2 ρ v.
  Proof.
    simpl in *. intros Hv.
    iDestruct Hv as "[H1 H2]".
    iAssumption.
  Qed.

  Lemma stp_and1_fails T1 T2 ρ v: interp (TAnd T1 T2) ρ v -∗ interp T2 ρ v.
  Proof.
    simpl in *. iIntros "Hv".
    (* This would turn P ∧ Q into P, Q in the Iris context (that is, P * Q), but
    this is illegal unless P and Q are persistent. *)
    Fail iDestruct "Hv" as "[H1 H2]".
    Fail iAssumption.
   Abort.

  Lemma stp_and T1 T2 ρ v:
    interp T1 ρ v ->
    interp T2 ρ v ->
    interp (TAnd T1 T2) ρ v.
  Proof.
    simpl; intros H1 H2; iSplit.
    iApply H1
    iApply H2.
  Qed.

  Lemma stp_and_wand T1 T2 ρ v:
    interp T1 ρ v -∗
    interp T2 ρ v -∗
    interp (TAnd T1 T2) ρ v.
  Proof. iIntros; by iSplit. Qed.

End Sec.