From D Require Import prelude asubst_base dlang.
From iris.proofmode Require Import tactics.

From D Require Import lty.
Module Type PTyInterpLemmas (Import VS : VlSortsFullSig) (Import LWP : LiftWp VS)
  (Import LJ : LtyJudgements VS LWP).

Class PTyInterp ty Σ :=
  pty_interpO : ty -> oltyO Σ 0.
Notation "V⟦ T ⟧" := (pty_interpO T).

(* Also appears in Autosubst. *)
Global Arguments pty_interpO {_ _ _} !_ /.

Definition pty_interp `{PTyInterp ty Σ} : ty -> hoEnvD Σ 0 := pty_interpO.
Notation "Vs⟦ g ⟧" := (fmap (M := gmap stamp) pty_interp g).
Global Arguments pty_interp /.

Module persistent_ty_interp_lemmas.

Class PTyInterpLemmas ty Σ `{sort_ty : Sort ty} `{!PTyInterp ty Σ} := {
  interp_subst_compose_ind T {args} ρ1 ρ2 v:
    V⟦ T.|[ρ1] ⟧ args ρ2 v ⊣⊢ V⟦ T ⟧ args (ρ1 >> ρ2) v;
}.

(** * Lemmas about the logical relation itself. *)
Section logrel_binding_lemmas.
  Context `{Htil : PTyInterpLemmas ty Σ}.

  Implicit Types
          (L T U: ty) (v: vl) (e: tm) (ρ : env).

  Lemma interp_subst_compose T {args} ρ1 ρ2 ρ3:
    ρ1 >> ρ2 = ρ3 → V⟦ T.|[ρ1] ⟧ args ρ2 ≡ V⟦ T ⟧ args ρ3.
  Proof. move=> <- v. exact: interp_subst_compose_ind. Qed.

  Lemma interp_weaken_one τ ρ {args} :
     V⟦ shift τ ⟧ args ρ ≡ V⟦ τ ⟧ args (stail ρ).
  Proof. apply interp_subst_compose. autosubst. Qed.

  Lemma interp_subst_one T v w ρ {args} :
    V⟦ T.|[v/] ⟧ args ρ w ≡ V⟦ T ⟧ args (v.[ρ] .: ρ) w.
  Proof. apply interp_subst_compose. autosubst. Qed.

  Lemma interp_subst_ids T ρ {args} : V⟦ T ⟧ args ρ ≡ V⟦ T.|[ρ] ⟧ args ids.
  Proof. symmetry. apply interp_subst_compose. autosubst. Qed.

  (**
    We have, unconditionally, that
    V⟦ T.|[∞ σ] ⟧ args ρ = V⟦ T ⟧ args (∞ σ >> ρ).

    But [∞ σ >> ρ] and [∞ σ.|[ρ]] are only equal for
    [length σ] entries.
  *)
  Lemma interp_subst_commute T σ ρ v (HclT : nclosed T (length σ)) args :
    V⟦ T.|[∞ σ] ⟧ args ρ v ≡ V⟦ T ⟧ args (∞ σ.|[ρ]) v.
  Proof.
    rewrite interp_subst_compose_ind !(interp_subst_ids T _ _) -hsubst_comp.
    (* *The* step requiring [HclT]. *)
    by rewrite (subst_compose _ _ HclT).
  Qed.
End logrel_binding_lemmas.
End persistent_ty_interp_lemmas.
End PTyInterpLemmas.
