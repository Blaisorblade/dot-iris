From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.saved_prop.
Require Import D.iris_prelude.

(** saved interpretations *)

Notation savedPred3G Σ A B C := (savedAnythingG Σ (A -d> B -d> C -d> ▶ ∙)).
Notation savedPred3Σ A B C := (savedAnythingΣ (A -d> B -d> C -d> ▶ ∙)).

Section saved_pred3.
  Context {A B C : Type}.
  Context `{!savedPred3G Σ A B C}.
  Implicit Type (Φ : A -d> B -d> C -d> iProp Σ).

  Definition saved_pred3_own (γ : gname) Φ :=
    saved_anything_own
      (F := A -d> B -d> C -d> ▶ ∙) γ (λ a b c, Next (Φ a b c)).

  Instance saved_pred3_own_contractive γ : Contractive (saved_pred3_own γ).
  Proof.
    rewrite /saved_pred3_own /saved_anything_own => n x y Hxy.
    (do 3 f_equiv) => ???. f_contractive. exact: Hxy.
  Qed.

  Global Instance persistent_saved_pred3_own: Persistent (saved_pred3_own γ Φ) := _.

  Lemma saved_pred3_alloc Φ : (|==> ∃ γ, saved_pred3_own γ Φ)%I.
  Proof. apply saved_anything_alloc. Qed.

  Lemma saved_pred3_agree γ Φ Ψ a b c :
    saved_pred3_own γ Φ -∗ saved_pred3_own γ Ψ -∗
    ▷ (Φ a b c ≡ Ψ a b c).
  Proof.
    iIntros "HΦ HΨ /=".
    iDestruct (saved_anything_agree with "HΦ HΨ") as "Heq".
    repeat setoid_rewrite bi.discrete_fun_equivI.
    iApply bi.later_equivI; iApply "Heq".
  Qed.
End saved_pred3.

Global Opaque saved_pred3_own.

(* XXX solve notation overlap. *)
Notation "γ ⤇ φ" := (saved_pred3_own γ φ) (at level 20).
