From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
Require Import D.iris_prelude.

(** saved interpretations *)

Notation savedInterpG Σ A B := (savedAnythingG Σ (A -c> B -c> ▶ ∙)).
Notation savedInterpΣ A B := (savedAnythingΣ (A -c> B -c> ▶ ∙)).

Section saved_interp.
  Context {A B : Type}.
  Context `{!savedInterpG Σ A B}.
  Implicit Type (Φ : A -c> B -c> iProp Σ).

  Definition saved_interp_own (γ : gname) Φ :=
    saved_anything_own
      (F := A -c> B -c> ▶ ∙) γ (λ a b, Next (Φ a b)).

  Instance saved_interp_own_contractive γ : Contractive (saved_interp_own γ).
  Proof. rewrite /saved_interp_own /saved_anything_own. solve_contractive_ho. Qed.

  Global Instance persistent_saved_interp_own: Persistent (saved_interp_own γ Φ) := _.

  Lemma saved_interp_alloc Φ : (|==> ∃ γ, saved_interp_own γ Φ)%I.
  Proof. apply saved_anything_alloc. Qed.

  Lemma saved_interp_agree γ Φ Ψ a b :
    saved_interp_own γ Φ -∗ saved_interp_own γ Ψ -∗
    ▷ (Φ a b ≡ Ψ a b).
  Proof.
    iIntros "HΦ HΨ /=".
    iDestruct (saved_anything_agree with "HΦ HΨ") as "Heq".
    repeat setoid_rewrite bi.ofe_fun_equivI.
    iApply bi.later_equivI; iApply "Heq".
  Qed.
End saved_interp.

Global Opaque saved_interp_own.

Notation "γ ⤇ φ" := (saved_interp_own γ φ) (at level 20).
