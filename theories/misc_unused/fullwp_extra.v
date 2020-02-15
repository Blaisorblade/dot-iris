From iris.proofmode Require Import tactics.

From iris.program_logic Require Import language lifting.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Section wp_extra.
  Context `{!irisG Λ Σ}.
  Implicit Types P : val Λ → iProp Σ.
  Implicit Types v : val Λ.

  Lemma wp_and_val P1 P2 v:
    WP of_val v {{ P1 }} -∗ WP of_val v {{ P2 }} -∗
                            WP of_val v {{ v, P1 v ∧ P2 v }}.
  Proof.
    iIntros "H1 H2".
    iEval (rewrite wp_value_inv') in "H1 H2".
    iMod "H1"; iMod "H2".
    rewrite -wp_value'. by iSplit.
  Qed.
End wp_extra.
