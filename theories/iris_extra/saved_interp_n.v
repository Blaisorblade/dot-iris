From iris.base_logic Require Import lib.saved_prop.
From D Require Import prelude iris_prelude asubst_intf.

(** saved interpretations *)
Module Type SavedHoInterp (Import V : VlSortsSig).

(** Argument stream. *)
Definition astream := nat -> vl.
Implicit Types (args : astream) (a arg v : vl).

Definition anil : astream := ids.
Definition acons a args := a .: args.
Definition ahead : astream -> vl := shead.
Definition atail : astream -> astream := stail.

Definition auncurry {A} (Φ : vl -d> astream -d> A) : astream -d> A :=
  λ args, Φ (ahead args) (atail args).
Definition acurry {A} (Φ : astream -d> A) : vl -d> astream -d> A :=
  λ v args, Φ (acons v args).
#[global] Instance acurry_ne A n :
  Proper (dist n ==> (=) ==> dist n) (@acurry A).
Proof. solve_proper_ho. Qed.

Definition aopen {A : ofeT} (Φ : A) : astream -d> A := λ args, Φ.
#[global] Arguments aopen /.
Notation aclose Φ := (Φ anil).

Module TEST.
  Definition __aclose {A : ofeT} (Φ : astream -d> A) : A. refine (aclose Φ). Abort.
End TEST.

Notation envPred s Σ := (env -d> s -d> iPropO Σ).
Notation envD Σ := (envPred vl Σ).

Definition hoEnvPred s Σ := astream -d> envPred s Σ.
Notation hoEnvD := (hoEnvPred vl).

Definition hoD Σ := astream -d> vl -d> iPropO Σ.
#[local] Notation argType s := (astream * env * s)%type.

Notation savedHoEnvPredG s Σ := (savedPredG Σ (argType s)).
Notation savedHoEnvPredΣ s := (savedPredΣ (argType s)).

Section saved_ho_sem_type.
  Context {s : Type}.
  Context `{!savedHoEnvPredG s Σ}.
  Implicit Type (Φ : astream -d> env -d> s -d> iPropO Σ).

  Definition curryC Φ : argType s -d> iPropO Σ := (λ '(args, ρ, c), Φ args ρ c).

  Definition saved_ho_sem_type_own (γ : gname) Φ :=
    saved_pred_own γ (curryC Φ).

  #[global] Instance saved_ho_sem_type_own_contractive γ : Contractive (saved_ho_sem_type_own γ).
  Proof.
    rewrite /saved_ho_sem_type_own => n f g Hfg.
    apply saved_pred_own_contractive. case: n Hfg => [//|n Hfg [[]] //].
  Qed.

  #[global] Instance persistent_saved_ho_sem_type_own γ Φ : Persistent (saved_ho_sem_type_own γ Φ) := _.

  Lemma saved_ho_sem_type_alloc Φ : ⊢ |==> ∃ γ, saved_ho_sem_type_own γ Φ.
  Proof. apply saved_pred_alloc. Qed.

  Lemma saved_ho_sem_type_agree {γ Φ Ψ} args ρ c :
    saved_ho_sem_type_own γ Φ -∗ saved_ho_sem_type_own γ Ψ -∗
    ▷ (Φ args ρ c ≡ Ψ args ρ c).
  Proof. apply (saved_pred_agree γ (curryC Φ) (curryC Ψ) (_, _, _)). Qed.
End saved_ho_sem_type.

Typeclasses Opaque saved_ho_sem_type_own.
#[global] Opaque saved_ho_sem_type_own.

Notation "γ ⤇ φ" := (saved_ho_sem_type_own γ φ) (at level 20).

End SavedHoInterp.
