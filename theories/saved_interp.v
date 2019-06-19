From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
Require Import D.iris_prelude.

(** saved interpretations *)

Notation savedInterpG Σ A B := (savedPredG Σ (A * B)).
Notation savedInterpΣ A B := (savedPredΣ (A * B)).

Section saved_interp.
  Context {A B : Type}.
  Context `{!savedInterpG Σ A B}.
  Implicit Type (Φ : A -c> B -c> iProp Σ).

  Definition curryC Φ : A * B -c> iProp Σ := (λ '(a, b), Φ a b).

  Definition saved_interp_own (γ : gname) Φ :=
    saved_pred_own γ (curryC Φ).

  Instance saved_interp_own_contractive γ : Contractive (saved_interp_own γ).
  Proof.
    rewrite /saved_interp_own => n f g Hfg.
    apply saved_pred_own_contractive. case: n Hfg => [//|n Hfg [] //].
  Qed.

  Global Instance persistent_saved_interp_own: Persistent (saved_interp_own γ Φ) := _.

  Lemma saved_interp_alloc Φ : (|==> ∃ γ, saved_interp_own γ Φ)%I.
  Proof. apply saved_anything_alloc. Qed.

  Lemma saved_interp_agree γ Φ Ψ a b :
    saved_interp_own γ Φ -∗ saved_interp_own γ Ψ -∗
    ▷ (Φ a b ≡ Ψ a b).
  Proof. apply (saved_pred_agree γ (curryC Φ) (curryC Ψ) (a, b)). Qed.
End saved_interp.

Global Opaque saved_interp_own.

Notation "γ ⤇ φ" := (saved_interp_own γ φ) (at level 20).
