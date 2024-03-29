(** * Adequacy of expression weakest preconditions, part of gDOT adequacy. *)
From stdpp Require Import relations.
From iris.proofmode Require Import proofmode.
From D.pure_program_logic Require Export weakestpre.
Import uPred.
Import relations.

(* Program logic adequacy *)
Record adequate `{LangDet Λ} (e1 : expr Λ) (φ : val Λ → Prop) := {
  adequate_result v2 :
    rtc pure_step e1 (of_val v2) → φ v2;
  adequate_not_stuck e2 :
    rtc pure_step e1 e2 → not_stuck e2
}.

Section adequacy.
Context `{Hiris : irisGS Λ Σ}.

Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

#[local] Notation σ := dummyState.

Lemma wp_step e1 e2 Φ :
  pure_step e1 e2 →
  WP e1 {{ Φ }} -∗ ▷ WP e2 {{ Φ }}.
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (Hpure) "H".
  rewrite (val_stuck e1 σ [] e2 σ []); last exact: pure_to_prim.
  iDestruct "H" as (e2' Hstep') "H".
  suff ->: e2' = e2 by [].
  edestruct Hpure as [_ []]; [done|naive_solver].
Qed.

Lemma wptp_steps {n e1 e2 Φ} :
  nsteps pure_step n e1 e2 →
  WP e1 {{ Φ }}
  -∗ ▷^n WP e2 {{ Φ }}.
Proof.
  elim: n e1 => [|n IH] e1 /=; inversion_clear 1; first iIntros "$".
  iIntros "He". by iApply IH; last iApply (wp_step with "He").
Qed.

Lemma wptp_result e1 v2 φ n :
  nsteps pure_step n e1 (of_val v2) →
  WP e1 {{ v, ⌜φ v⌝ }} -∗
  ▷^n ⌜φ v2⌝.
Proof. iIntros (Hs) "He /=". by rewrite (wptp_steps Hs) wp_value_inv'. Qed.

Lemma wp_safe e Φ :
  WP e {{ Φ }} -∗ ⌜not_stuck e⌝.
Proof.
  rewrite wp_unfold /wp_pre /L.not_stuck. iIntros "H".
  destruct (to_val e); first by eauto.
  iDestruct "H" as (e2 ?) "_". iIntros "!%".
  rewrite /reducible; naive_solver.
Qed.

Lemma wptp_safe n e1 e2 Φ :
  nsteps pure_step n e1 e2 →
  WP e1 {{ Φ }} -∗ ▷^n ⌜not_stuck e2⌝.
Proof.
  iIntros (He2) "He".
  iDestruct (wptp_steps with "He") as "H"; first done.
  iNext.
  iApply (wp_safe with "H").
Qed.

Lemma wptp_safe_n n e1 Φ :
  WP e1 {{ Φ }} -∗ ▷^n ⌜safe_n n e1⌝.
Proof. iIntros "Hwp" (e2 Hsteps); by iApply wptp_safe. Qed.
End adequacy.

Theorem wp_adequacy {Σ Λ} e φ `{LangDet Λ} :
  (⊢@{iPropI Σ} let _ := IrisG Λ Σ in |==> WP e {{ v, ⌜φ v⌝ }}) →
  adequate e (λ v, φ v).
Proof.
  intros Hwp; split; intros ? [n Hsteps]%rtc_nsteps_1; eapply (soundness _ n);
    iMod Hwp as "Hwp".
  by iApply (wptp_result e with "Hwp").
  by iApply (wptp_safe with "Hwp").
Qed.
