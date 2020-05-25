From iris.proofmode Require Import tactics.
Import bi.
From D.iris_extra Require Import proofmode_extra.

Section Succeed.
  Context {PROP : bi}.
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
