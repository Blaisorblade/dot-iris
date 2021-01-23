From iris.base_logic Require Import lib.saved_prop.
From D Require Import prelude iris_prelude asubst_intf.

(** saved interpretations *)
Module Type SavedInterpN (Import V : VlSortsSig).

Notation envPred s Σ := (env -d> s -d> iPropO Σ).
Notation envD Σ := (envPred vl Σ).

Definition hoEnvPred s Σ := list vl -d> envPred s Σ.
Notation hoEnvD := (hoEnvPred vl).

Definition hoD Σ := (* HO args *) list vl -d> vl -d> iPropO Σ.
(* Definition packedHoEnvD Σ := packedHoEnvPred vl Σ. *)
(* TODO name*)
Local Notation argType s := (list vl * env * s)%type.

Notation savedHoEnvPredG s Σ := (savedPredG Σ (argType s)).
Notation savedHoEnvPredΣ s := (savedPredΣ (argType s)).

Section saved_pred3.
  Context {s : Type}.
  Context `{!savedHoEnvPredG s Σ}.
  Implicit Type (Φ : list vl -d> env -d> s -d> iPropO Σ).

  Definition curryC Φ : argType s -d> iPropO Σ := (λ '(a, b, c), Φ a b c).

  Definition saved_pred3_own (γ : gname) Φ :=
    saved_pred_own γ (curryC Φ).

  #[global] Instance saved_pred3_own_contractive γ : Contractive (saved_pred3_own γ).
  Proof.
    rewrite /saved_pred3_own => n f g Hfg.
    apply saved_pred_own_contractive. case: n Hfg => [//|n Hfg [[]] //].
  Qed.

  #[global] Instance persistent_saved_pred3_own γ Φ : Persistent (saved_pred3_own γ Φ) := _.

  Lemma saved_pred3_alloc Φ : ⊢ |==> ∃ γ, saved_pred3_own γ Φ.
  Proof. apply saved_pred_alloc. Qed.

  Lemma saved_pred3_agree γ Φ Ψ a b c :
    saved_pred3_own γ Φ -∗ saved_pred3_own γ Ψ -∗
    ▷ (Φ a b c ≡ Ψ a b c).
  Proof. apply (saved_pred_agree γ (curryC Φ) (curryC Ψ) (a, b, c)). Qed.
End saved_pred3.

Typeclasses Opaque saved_pred3_own.
#[global] Opaque saved_pred3_own.

Notation "γ ⤇ φ" := (saved_pred3_own γ φ) (at level 20).

Definition vcurry {A} (Φ : list vl -d> A) : vl -d> list vl -d> A :=
  λ v args, Φ (cons v args).
Instance vcurry_ne A n :
  Proper (dist n ==> (=) ==> dist n) (@vcurry A).
Proof. solve_proper_ho. Qed.

Definition vopen {A : ofeT} (Φ : A) : list vl -d> A := λ args, Φ.
#[global] Arguments vopen /.

End SavedInterpN.
