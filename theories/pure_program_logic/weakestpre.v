(** * Expression weakest preconditions.

The following development is that of a *pure* weakest
precondition: it uses no (basic/fancy) updates, does not supports Iris invariants,
and is specialized to deterministic languages.
*)
From iris.base_logic Require Export iprop.
From iris.program_logic Require Export language.
From iris.bi Require Export weakestpre.
From iris.proofmode Require Import base tactics classes.

From D.iris_extra Require Export det_reduction.
Set Default Proof Using "Type".
Import uPred.

Class irisG (Λ : language) (Σ : gFunctors) `{InhabitedState Λ} := IrisG {
  irisG_langdet :> LangDet Λ
}.
Arguments IrisG _ _ {_ _}.
Local Notation σ := dummyState.

Definition wp_pre `{irisG Λ Σ}
    (wp : expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ e1 Φ,
  match to_val e1 with
  | Some v => Φ v
  | None => ∃ e2, ⌜prim_step e1 σ [] e2 σ []⌝ ∧ ▷ wp e2 Φ
  end%I.

Local Instance wp_pre_contractive `{irisG Λ Σ} : Contractive wp_pre.
Proof.
  rewrite /wp_pre => n wp wp' Hwp e1 Φ.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wp_def `{irisG Λ Σ} : stuckness → coPset →
   expr Λ → (val Λ → iProp Σ) → iProp Σ := λ _ _, fixpoint wp_pre.
Definition wp_aux `{irisG Λ Σ} : seal (wp_def (Λ := Λ) (Σ := Σ)). Proof. by eexists. Qed.
Instance wp' `{irisG Λ Σ} : Wp Λ (iProp Σ) stuckness := wp_aux.(unseal).
Definition wp_eq `{irisG Λ Σ} : wp = wp_def (Λ := Λ) (Σ := Σ) := wp_aux.(seal_eq).

Section wp.
Context `{irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre (wp (PROP:=iProp Σ) s E) e Φ.
Proof. rewrite wp_eq. apply (fixpoint_unfold wp_pre). Qed.

#[global] Instance wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  elim: (lt_wf n) e => {}n _ IH e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre.
  repeat first [apply IH; first lia | f_contractive | f_equiv].
  eapply dist_le; eauto with lia.
Qed.
#[global] Instance wp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.
#[global] Instance wp_contractive s E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He.
  by repeat (f_contractive || f_equiv).
Qed.
#[global] Instance wp_plain s E e Φ (HΦ: ∀ v, Plain (Φ v)):
  Plain (wp (PROP:=iProp Σ) s E e Φ).
Proof.
  rewrite /Plain; iLöb as "IH" forall (e).
  iEval rewrite !wp_unfold /wp_pre.
  case_match; first by iApply plain.
  iDestruct 1 as (e2 ?) "H2"; iExists e2; iSplit; first done.
  rewrite -later_plainly; by iApply ("IH" $! e2 with "H2").
Qed.

Lemma wp_value' s E Φ v : Φ v ⊢ WP of_val v @ s; E {{ Φ }}.
Proof. iIntros "HΦ". rewrite wp_unfold /wp_pre to_of_val. auto. Qed.
Lemma wp_value_inv' s E Φ v : WP of_val v @ s; E {{ Φ }} ⊢ Φ v.
Proof. by rewrite wp_unfold /wp_pre to_of_val. Qed.

Lemma wp_strong_mono e Φ Ψ :
  WP e {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e {{ Ψ }}.
Proof.
  iIntros "H HΦ". iLöb as "IH" forall (e Φ Ψ).
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|]; first by iApply ("HΦ" with "[-]").
  iDestruct "H" as (e2 ?) "H".
  iExists e2; iSplit; first done; iIntros "!>".
  iApply ("IH" with "H HΦ").
Qed.

Lemma wp_step e P Φ :
  to_val e = None →
  (▷ P) -∗ WP e {{ v, P -∗ Φ v }} -∗ WP e {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre; iIntros (->) "HR".
  iDestruct 1 as (e2) "[% H]".
  iExists e2; iSplit; first done. iIntros "!>".
  iApply (wp_strong_mono with "H").
  iIntros (v) "H". by iApply "H".
Qed.

Lemma wp_bind K `{!LanguageCtx K} e Φ :
  WP e {{ v, WP K (of_val v) {{ Φ }} }} ⊢ WP K e {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He; first by apply of_to_val in He as <-.
  rewrite wp_unfold /wp_pre fill_not_val //.
  iDestruct "H" as (e2 ?) "H"; iExists (K e2); iSplit; last by iApply "IH".
  iPureIntro. exact: fill_step.
Qed.

Lemma wp_bind_inv K `{!LanguageCtx K} e Φ :
  WP K e {{ Φ }} ⊢ WP e {{ v, WP K (of_val v) {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (e Φ). rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. }
  rewrite fill_not_val //.
  iDestruct "H" as (eK2 Hkstep) "H".
  edestruct (fill_step_inv e) with (e2 := eK2) as (e2 & -> & ?) => //.
  iExists e2; iSplit; first done. by iApply "IH".
Qed.

(** ** Derived rules *)
Lemma wp_mono e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e {{ Φ }} ⊢ WP e {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
#[global] Instance wp_mono' e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) NotStuck ⊤ e).
Proof. intros Φ Φ' ?. by apply wp_mono. Qed.

Lemma wp_value Φ e v : IntoVal e v → Φ v ⊢ WP e {{ Φ }}.
Proof. intros <-. by apply wp_value'. Qed.
Lemma wp_value_inv Φ e v : IntoVal e v → WP e {{ Φ }} ⊢ Φ v.
Proof. intros <-. by apply wp_value_inv'. Qed.

Lemma wp_frame_l e Φ R : R ∗ WP e {{ Φ }} ⊢ WP e {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r e Φ R : WP e {{ Φ }} ∗ R ⊢ WP e {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma wp_frame_step_l e Φ R :
  to_val e = None →
  (▷R) ∗ WP e {{ Φ }} ⊢ WP e {{ v, R ∗ Φ v }}.
Proof.
  iIntros (?) "[Hu Hwp]". iApply (wp_step with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r e Φ R :
  to_val e = None →
  WP e {{ Φ }} ∗ (▷R) ⊢ WP e {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' e Φ R :
  to_val e = None → ▷ R ∗ WP e {{ Φ }} ⊢ WP e {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply wp_frame_step_l; try iFrame; eauto. Qed.
Lemma wp_frame_step_r' e Φ R :
  to_val e = None → WP e {{ Φ }} ∗ ▷ R ⊢ WP e {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply wp_frame_step_r; try iFrame; eauto. Qed.

Lemma wp_wand e Φ Ψ :
  WP e {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
Qed.
Lemma wp_wand_l e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e {{ Φ }} ⊢ WP e {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r e Φ Ψ :
  WP e {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{irisG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  #[global] Instance frame_wp p e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e {{ Φ }}) (WP e {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.
End proofmode_classes.
