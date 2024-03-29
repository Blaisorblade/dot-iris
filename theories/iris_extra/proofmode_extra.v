From iris.proofmode Require Import proofmode.
From D Require Import prelude.
Import bi.

(* Avoid auto-dropping box (and unfolding) when introducing judgments persistently. *)
#[global] Notation IntoPersistent' P := (IntoPersistent false P P).

Tactic Notation "iSplitWith" constr(H) "as" constr(H') :=
  iApply (bi.and_parallel with H); iSplit; iIntros H'.

Lemma and_pure_equiv {PROP : bi} P Q1 Q2 :
  ⌜ P ⌝ ∧ Q1 ⊣⊢@{PROP} ⌜ P ⌝ ∧ Q2 ↔ (P → Q1 ≡ Q2).
Proof.
  split => Heq; first move=> Hp.
  - iDestruct Heq as "Heq";
    iSplitWith "Heq" as "Hwand"; iIntros "H";
    iDestruct ("Hwand" with "[$H //]") as "[_ $]".
  - by iSplit; iDestruct 1 as (HP) "H"; iFrame (HP); rewrite (Heq HP).
Qed.

Lemma forall_swap_impl `{BiAffine PROP} {A} (P : PROP) `{!Persistent P} (Ψ : A → PROP) :
  (P → ∀ a, Ψ a) ⊣⊢ ∀ a, P → Ψ a.
Proof.
  iSplit; [iIntros "H" (a) "P"|iIntros "H P" (a)]; iApply ("H" with "P").
Qed.

Lemma forall_swap_wand {PROP : bi} {A} (P : PROP) `{!Persistent P} (Ψ : A → PROP) :
  (P -∗ ∀ a, Ψ a) ⊣⊢ ∀ a, P -∗ Ψ a.
Proof.
  iSplit; [iIntros "H" (a) "P"|iIntros "H P" (a)]; iApply ("H" with "P").
Qed.

Lemma bi_emp_valid_True `{BiAffine PROP} {P : PROP} (Hvalid : ⊢ P) : P ⊣⊢ True.
Proof. by iSplit; [iIntros "_"|rewrite -Hvalid]. Qed.

Lemma bi_exist_swap (PROP : bi) `(P : A → B → PROP) : (∃ a b, P a b) ⊣⊢ ∃ b a, P a b.
Proof. by iSplit; iDestruct 1 as (x1 x2) "?"; iExists x2, x1. Qed.

Lemma bi_exist_nested_swap {PROP : bi} `{P : A → PROP} `{Q : A → B → PROP} :
  (∃ a, P a ∧ ∃ b, Q a b) ⊣⊢ ∃ b a, P a ∧ Q a b.
Proof. setoid_rewrite and_exist_l; apply bi_exist_swap. Qed.

Lemma and2_exist_r {PROP : bi} {A} P Q R :
  (∃ a : A, P a ∧ Q a ∧ R) ⊣⊢@{PROP} (∃ a : A, P a ∧ Q a) ∧ R.
Proof. rewrite (and_exist_r R); apply bi.exist_proper => d; exact: assoc. Qed.

Lemma forall_intuitionistically {A} `{BiAffine PROP, BiPersistentlyForall PROP} (Φ : A → PROP) :
  (∀ x, □ Φ x) ⊣⊢ □ ∀ x, Φ x.
Proof.
  iSplit; last iApply intuitionistically_forall.
  iIntros "#H !> %". by iApply "H".
Qed.

Section proofmode_extra.
  Context {PROP : bi}.
  Implicit Types P Q R : PROP.

  Lemma swap_later {n} P : ▷^n ▷ P ⊣⊢ ▷ ▷^n P.
  Proof. by rewrite -bi.later_laterN bi.laterN_later. Qed.

  Lemma swap_laterN i j {P} : ▷^i ▷^j P ⊣⊢ ▷^j ▷^i P.
  Proof. by rewrite -bi.laterN_add Nat.add_comm bi.laterN_add. Qed.

  Lemma timeless_timelessN i P :
    Timeless P →
    ▷^i P ⊢ ▷^i False ∨ P.
  Proof.
    iIntros (?) "H". iInduction i as [|i] "IH"; cbn; first by auto.
    iDestruct ("IH" with "H") as "[H|H]"; first by auto.
    iDestruct (timeless with "H") as "H".
    rewrite /bi_except_0. iDestruct "H" as "[H|H]"; auto.
  Qed.

  Lemma strip_timeless_laterN_wand i P Q :
    Timeless P →
    (P -∗ ▷^i Q) -∗ (▷^i P -∗ ▷^i Q).
  Proof.
    iIntros (?) "Hw HP".
    iDestruct (timeless_timelessN with "HP") as "[H|H]"; first by iNext.
    by iApply "Hw".
  Qed.

  Lemma strip_timeless_laterN_impl `{!BiAffine PROP} i P Q :
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

  Lemma strip_pure_laterN_wand' i j φ Q :
    (⌜ φ ⌝ -∗ ▷^(i + j) Q) -∗ (▷^i ⌜ φ ⌝ -∗ ▷^(i + j) Q).
  Proof.
    rewrite Nat.add_comm (laterN_intro j (▷^i ⌜ φ ⌝))%I -laterN_add.
    exact: strip_pure_laterN_wand.
  Qed.
End proofmode_extra.

From iris.base_logic Require Import bi.
Section derived_swap_lemmas.
  Context `{M : ucmra}.
  Lemma mlater_pers (P: uPred M) : □ ▷ P ⊣⊢ ▷ □ P.
  Proof. iSplit; by iIntros "#? !>!>". Qed.
  Lemma mlaterN_pers (P: uPred M) i : □ ▷^i P ⊣⊢ ▷^i □ P.
  Proof. iSplit; by iIntros "#? !>!>". Qed.
End derived_swap_lemmas.

From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.
From D.iris_extra Require Import det_reduction.

Section wp_extra.
  Context `{irisGS Λ Σ}.
  Implicit Types (P : val Λ → iProp Σ) (v : val Λ) (e : expr Λ).

  Lemma wp_and_val P1 P2 v :
    WP of_val v {{ P1 }} -∗ WP of_val v {{ P2 }} -∗
      WP of_val v {{ v, P1 v ∧ P2 v }}.
  Proof. rewrite 2!wp_value_inv' -wp_value'; iIntros "$$". Qed.

  (* Doesn't generalize to standard WP, but needed for DOT. *)
  Lemma wp_and `{!LangDet Λ} (P1 P2 : val Λ → iProp Σ) e :
    WP e {{ P1 }} -∗ WP e {{ P2 }} -∗ WP e {{ v, P1 v ∧ P2 v }}.
  Proof.
    iLöb as "IH" forall (e); iIntros "H1 H2".
    iEval (rewrite !wp_unfold /wp_pre) in "H1 H2";
      iEval (rewrite !wp_unfold /wp_pre);
      case_match; [by auto|].
    iDestruct "H1" as (e1 Hs1) "H1"; iDestruct "H2" as (e2 Hs2) "H2".
    rewrite !(prim_step_det Hs1 Hs2).
    by iExists (e2); iSplit; [|iApply ("IH" with "H1 H2")].
  Qed.
End wp_extra.
