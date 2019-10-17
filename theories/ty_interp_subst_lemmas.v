From D Require Import prelude asubst_base dlang.
From iris.proofmode Require Import tactics.

Module Type TyInterpLemmas (Import VS : VlSortsFullSig) (Import LWP : LiftWp VS).

Class TyInterpLemmas ty Σ `{sort_ty : Sort ty} `{!TyInterp ty Σ} := {
  interp_subst_compose_ind T ρ1 ρ2 v:
    ⟦ T.|[ρ1] ⟧ ρ2 v ⊣⊢ ⟦ T ⟧ (ρ1 >> ρ2) v;
}.

(** * Lemmas about the logical relation itself. *)
Section logrel_binding_lemmas.
  Context `{Htil : TyInterpLemmas ty Σ}.

  Implicit Types
          (L T U: ty) (v: vl) (e: tm) (ρ : env).

  Lemma interp_subst_compose T ρ1 ρ2 ρ3:
    ρ1 >> ρ2 = ρ3 → ⟦ T.|[ρ1] ⟧ ρ2 ≡ ⟦ T ⟧ ρ3.
  Proof. move=> <- v. exact: interp_subst_compose_ind. Qed.

  Lemma interp_weaken_one τ ρ:
     ⟦ τ.|[ren (+1)] ⟧ ρ ≡ ⟦ τ ⟧ (stail ρ).
  Proof. apply interp_subst_compose. autosubst. Qed.

  Lemma interp_subst_one T v w ρ:
    ⟦ T.|[v/] ⟧ ρ w ≡ ⟦ T ⟧ (v.[ρ] .: ρ) w.
  Proof. apply interp_subst_compose. autosubst. Qed.

  Lemma interp_subst_ids T ρ : ⟦ T ⟧ ρ ≡ ⟦ T.|[ρ] ⟧ ids.
  Proof. symmetry. apply interp_subst_compose. autosubst. Qed.

  (**
    We have, unconditionally, that
    ⟦ T.|[to_subst σ] ⟧ ρ = ⟦ T ⟧ (to_subst σ >> ρ).

    But [to_subst σ >> ρ] and [to_subst σ.|[ρ]] are only equal for
    [length σ] entries.
  *)
  Lemma interp_subst_commute T σ ρ v:
    nclosed T (length σ) →
    ⟦ T.|[∞ σ] ⟧ ρ v ≡ ⟦ T ⟧ (∞ σ.|[ρ]) v.
  Proof.
    move => HclT. rewrite interp_subst_compose_ind.
    rewrite (interp_subst_ids T (∞ _) v) (interp_subst_ids T (_ >> _) v).
    rewrite (subst_compose _ _ HclT) //. f_equiv; autosubst.
  Qed.
End logrel_binding_lemmas.
End TyInterpLemmas.
