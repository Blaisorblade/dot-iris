From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.

(** saved interpretations *)

Notation savedPred3G Σ A B C := (savedPredG Σ (A * B * C)).
Notation savedPred3Σ A B C := (savedPredΣ (A * B * C)).

Section saved_pred3.
  Context {A B C : Type}.
  Context `{!savedPred3G Σ A B C}.
  Implicit Type (Φ : A -d> B -d> C -d> iProp Σ).

  Definition curryC Φ : A * B * C -d> iProp Σ := (λ '(a, b, c), Φ a b c).

  Definition saved_pred3_own (γ : gname) Φ :=
    saved_pred_own γ (curryC Φ).

  Instance saved_pred3_own_contractive γ : Contractive (saved_pred3_own γ).
  Proof.
    rewrite /saved_pred3_own => n f g Hfg.
    apply saved_pred_own_contractive. case: n Hfg => [//|n Hfg [[]] //].
  Qed.

  Global Instance persistent_saved_pred3_own: Persistent (saved_pred3_own γ Φ) := _.

  Lemma saved_pred3_alloc Φ : (|==> ∃ γ, saved_pred3_own γ Φ)%I.
  Proof. apply saved_pred_alloc. Qed.

  Lemma saved_pred3_agree γ Φ Ψ a b c :
    saved_pred3_own γ Φ -∗ saved_pred3_own γ Ψ -∗
    ▷ (Φ a b c ≡ Ψ a b c).
  Proof. apply (saved_pred_agree γ (curryC Φ) (curryC Ψ) (a, b, c)). Qed.
End saved_pred3.

Global Opaque saved_pred3_own.

(* XXX solve notation overlap. *)
Notation "γ ⤇ φ" := (saved_pred3_own γ φ) (at level 20).
