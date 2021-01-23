(** * Lift operational semantics to expression weakest preconditions. *)
From D.pure_program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section lifting.
Context `{irisG Λ Σ}.

Implicit Types s : stuckness.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

#[local] Notation σ := dummyState.

Lemma wp_lift_step s E Φ e1 :
  to_val e1 = None →
  (∃ e2 , ⌜prim_step e1 σ [] e2 σ []⌝ ∧ ▷ WP e2 @ s; E {{ Φ }})
  ⊢ WP e1 @ s; E {{ Φ }}.
Proof. rewrite wp_unfold /wp_pre. iIntros (->) "$". Qed.

(** Derived lifting lemmas. *)
Lemma wp_pure_step_later s E e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  (▷^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 Hpstep] "IH"; simpl; first done.
  have ?: to_val e1 = None.
  by apply reducible_not_val with (σ := σ), reducible_no_obs_reducible, Hpstep.
  iApply wp_lift_step; first done.
  iExists (e2); iSplit; first eauto using pure_to_prim.
  by iApply "IH".
Qed.
End lifting.
