From iris.proofmode Require Import tactics.
Import bi.

Module Tests1.
  Section Succeed.
    Context {PROP : sbi}.
    Implicit Types P Q R : PROP.

    Lemma strip_timeless_later_wand P Q :
      Timeless P →
      (P -∗ ▷ Q) ⊢ (▷ P -∗ ▷ Q).
    Proof.
      iIntros (?) "Hw >HP". by iApply "Hw".
    Qed.

    Lemma strip_timeless_later_impl `{!BiAffine PROP} P Q:
      Timeless P → Persistent P →
      (P → ▷ Q) ⊢ (▷ P → ▷ Q).
    Proof.
      iIntros (??) "Hi >HP". by iApply "Hi".
    Qed.

    Lemma strip_pure_later_wand φ Q :
      (⌜ φ ⌝ -∗ ▷ Q) -∗ (▷ ⌜ φ ⌝ -∗ ▷ Q).
    Proof. apply strip_timeless_later_wand; apply _. Qed.

    Lemma strip_pure_later_impl `{!BiAffine PROP} φ Q:
      (⌜ φ ⌝ → ▷ Q) ⊢ (▷ ⌜ φ ⌝ → ▷ Q).
    Proof. apply strip_timeless_later_impl; apply _. Qed.
  End Succeed.
End Tests1.

Section proofmode_extra.
  Context {PROP : sbi}.
  Implicit Types P Q R : PROP.

  Lemma swap_later {n} P: ▷^n ▷ P ⊣⊢ ▷ ▷^n P.
  Proof. by rewrite -bi.later_laterN bi.laterN_later. Qed.

  Lemma swap_laterN i j {P}: ▷^i ▷^j P ⊣⊢ ▷^j ▷^i P.
  Proof. by rewrite -bi.laterN_plus Nat.add_comm bi.laterN_plus. Qed.

  Lemma timeless_timelessN i P :
    Timeless P →
    ▷^i P ⊢ ▷^i False ∨ P.
  Proof.
    iIntros (?) "H". iInduction i as [|i] "IH"; cbn; first by auto.
    iDestruct ("IH" with "H") as "[H|H]"; first by auto.
    iDestruct (timeless with "H") as "H".
    rewrite /sbi_except_0. iDestruct "H" as "[H|H]"; auto.
  Qed.

  Lemma strip_timeless_laterN_wand i P Q :
    Timeless P →
    (P -∗ ▷^i Q) -∗ (▷^i P -∗ ▷^i Q).
  Proof.
    iIntros (?) "Hw HP".
    iDestruct (timeless_timelessN with "HP") as "[H|H]"; first by iNext.
    by iApply "Hw".
  Qed.

  Lemma strip_timeless_laterN_impl `{!BiAffine PROP} i P Q:
    Timeless P → Persistent P →
    (P → ▷^i Q) ⊢ (▷^i P → ▷^i Q).
  Proof.
    iIntros (??) "Hi HP".
    iDestruct (timeless_timelessN with "HP") as "[H|H]"; first by iNext.
    by iApply "Hi".
  Qed.

  Lemma strip_pure_laterN_wand i φ Q :
    (⌜ φ ⌝ -∗ ▷^i Q) -∗ (▷^i ⌜ φ ⌝ -∗ ▷^i Q).
  Proof. exact: strip_timeless_laterN_wand. Qed.

  Lemma strip_pure_laterN_impl `{!BiAffine PROP} i φ Q :
    (⌜ φ ⌝ → ▷^i Q) ⊢ ▷^i ⌜ φ ⌝ → ▷^i Q.
  Proof. exact: strip_timeless_laterN_impl. Qed.

  Lemma strip_pure_laterN_wand' i j φ Q:
    (⌜ φ ⌝ -∗ ▷^(i + j) Q) -∗ (▷^i ⌜ φ ⌝ -∗ ▷^(i + j) Q).
  Proof.
    rewrite Nat.add_comm (laterN_intro j (▷^i ⌜ φ ⌝))%I -laterN_plus.
    exact: strip_pure_laterN_wand.
  Qed.
End proofmode_extra.

From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

Section wp_extra.
  Context `{irisG Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Lemma wp_strong_mono_wf s1 s2 E1 E2 e Φ {Ψ} (wf: expr Λ → Prop):
    s1 ⊑ s2 →
    wf e →
    (∀ t1 t2 σ σ' ts κ, prim_step t1 σ κ t2 σ' ts → wf t1 → wf t2 ∧ Forall wf ts) →
    WP e @ s1; E1 {{ Φ }} -∗
    (∀ v, ⌜wf (of_val v)⌝ -∗ Φ v -∗ Ψ v) -∗
    WP e @ s2; E2 {{ Ψ }}.
  Proof.
    iIntros (? HwfE Hpres) "H HΦ". iLöb as "IH" forall (e HwfE E1 E2 Φ Ψ).
    rewrite !wp_unfold /wp_pre.
    destruct (to_val e) as [v|] eqn:?.
    { iApply ("HΦ" with "[%] [-//]"). apply of_to_val in Heqo. by subst. }
    iIntros (σ1 κ κs n) "Hσ".
    iDestruct ("H" with "[$]") as "[% H]".
    iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep).
    iDestruct ("H" with "[//]") as "H". iIntros "!>".
    have HPefs: Forall wf efs. by eapply Hpres.
    iDestruct "H" as "(Hσ & H & Hefs)".
    iFrame "Hσ". iSplitR "Hefs".
    - iApply ("IH" with "[%] H HΦ"). by eapply Hpres.
    - iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef Heq).
      iIntros "H". iApply ("IH" with "[%] H"); auto.
      edestruct (Hpres e e2) => //. by eapply Forall_lookup_1.
  Qed.

  Lemma wp_wand_wf s E e Φ {Ψ} (wf: expr Λ → Prop):
    wf e →
    (∀ t1 t2 σ σ' ts κ, prim_step t1 σ κ t2 σ' ts → wf t1 → wf t2 ∧ Forall wf ts) →
    WP e @ s; E {{ v, Φ v }} -∗
    (∀ v, ⌜wf (of_val v)⌝ -∗ Φ v -∗ Ψ v) -∗
    WP e @ s; E {{ v, Ψ v }}.
  Proof.
    iIntros (HwfE Hpres) "Hwp HΦ". iApply (wp_strong_mono_wf with "Hwp"); eauto.
  Qed.

  Lemma wp_and_val P1 P2 v:
    WP of_val v {{ P1 }} -∗ WP of_val v {{ P2 }} -∗
      WP of_val v {{ v, P1 v ∧ P2 v }}.
  Proof.
    iIntros "H1 H2".
    iDestruct (wp_value_inv' with "H1") as "H1'".
    iDestruct (wp_value_inv' with "H2") as "H2'".
    iApply wp_value'; by iSplit.
  Qed.

  (*
    Overly strong, and doesn't generalize, as state_interp
    is basically never persistent. Still here for now.
  *)
  Lemma wp_and `{∀ σ κ n, Persistent (state_interp σ κ n)} (P1 P2: val Λ → iProp Σ) e:
    WP e {{ P1 }} -∗ WP e {{ P2 }} -∗ WP e {{ v, P1 v ∧ P2 v }}.
  Proof.
    iLöb as "IH" forall (e).
    iIntros "H1 H2".
    iEval (rewrite !wp_unfold /wp_pre) in "H1 H2".
    iEval (rewrite !wp_unfold /wp_pre).
    case_match; first by auto.
    iIntros (σ1 k ks n) "#Ha".
    iDestruct ("H1" $! σ1 k ks n with "Ha") as "[$ H1]".
    iDestruct ("H2" $! σ1 k ks n with "Ha") as "[% H2]".
    iIntros (e2 σ2 efs Hstep).
    iSpecialize ("H1" $! e2 σ2 efs Hstep);
    iSpecialize ("H2" $! e2 σ2 efs Hstep).
    iNext.
    iDestruct "H1" as "[$ [H1 $]]".
    iDestruct "H2" as "[_ [H2 _]]".
    by iApply ("IH" with "H1 H2").
  Qed.
End wp_extra.
