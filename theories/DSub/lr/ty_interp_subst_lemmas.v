(** * Binding lemmas about DSub* logical relations. *)
From D Require Import prelude iris_prelude asubst_base saved_interp_dep.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

Module Type TyInterpLemmas (Import VS : VlSortsFullSig)
  (Import LWP : SavedInterpDep VS).
(* XXX SavedInterpDep is used because it defines identifiers like [envD]. *)

Class TyInterp ty Σ :=
  ty_interp : ty → envD Σ.
Notation "⟦ T ⟧" := (ty_interp T).

(* Also appears in Autosubst. *)
Global Arguments ty_interp {_ _ _} !_ /.

Module ty_interp_lemmas.
Class TyInterpLemmas ty Σ `{sort_ty : Sort ty} `{!TyInterp ty Σ} := {
  interp_subst_compose_ind T ρ1 ρ2 v:
    ⟦ T.|[ρ1] ⟧ ρ2 v ⊣⊢ ⟦ T ⟧ (ρ1 >> ρ2) v;
}.

Section logrel_binding_lemmas.
  Context `{Htil : TyInterpLemmas ty Σ}.

  Implicit Types
          (L T U: ty) (v: vl) (e: tm) (ρ : env).

  Lemma interp_subst_compose T ρ1 ρ2 ρ3:
    ρ1 >> ρ2 = ρ3 → ⟦ T.|[ρ1] ⟧ ρ2 ≡ ⟦ T ⟧ ρ3.
  Proof. move=> <- v. exact: interp_subst_compose_ind. Qed.

  Lemma interp_weaken_one τ ρ:
     ⟦ shift τ ⟧ ρ ≡ ⟦ τ ⟧ (stail ρ).
  Proof. apply interp_subst_compose. autosubst. Qed.

  Lemma interp_subst_one T v w ρ:
    ⟦ T.|[v/] ⟧ ρ w ≡ ⟦ T ⟧ (v.[ρ] .: ρ) w.
  Proof. apply interp_subst_compose. autosubst. Qed.

  Lemma interp_subst_ids T ρ : ⟦ T ⟧ ρ ≡ ⟦ T.|[ρ] ⟧ ids.
  Proof. symmetry. apply interp_subst_compose. autosubst. Qed.

  (**
    We have, unconditionally, that
    ⟦ T.|[∞ σ] ⟧ ρ = ⟦ T ⟧ (∞ σ >> ρ).

    But [∞ σ >> ρ] and [∞ σ.|[ρ]] are only equal for
    [length σ] entries.
  *)
  Lemma interp_finsubst_commute_cl T σ ρ v (HclT : nclosed T (length σ)) :
    ⟦ T.|[∞ σ] ⟧ ρ v ≡ ⟦ T ⟧ (∞ σ.|[ρ]) v.
  Proof.
    rewrite interp_subst_compose_ind !(interp_subst_ids T) -hsubst_comp.
    (* *The* step requiring [HclT]. *)
    by rewrite (subst_compose HclT).
  Qed.
End logrel_binding_lemmas.
End ty_interp_lemmas.
End TyInterpLemmas.
