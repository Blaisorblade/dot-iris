From D Require Import prelude asubst_base dlang.
From iris.proofmode Require Import tactics.

From D Require Import lty.
Module Type PTyInterpLemmas (Import VS : VlSortsFullSig) (Import LWP : LiftWp VS)
  (Import LJ : LtyJudgements VS LWP).

Module persistent_ty_interp_lemmas.

Class PTyInterp ty Σ :=
  pty_interp : ty -> olty Σ 0.
Notation "p⟦ T ⟧" := (pty_interp T).
Notation "p⟦ g ⟧g" := (fmap (M := gmap stamp) pty_interp g).

(* Also appears in Autosubst. *)
Global Arguments pty_interp {_ _ _} !_ /.

Class PTyInterpLemmas ty Σ `{sort_ty : Sort ty} `{!PTyInterp ty Σ} := {
  interp_subst_compose_ind T {args} ρ1 ρ2 v:
    p⟦ T.|[ρ1] ⟧ args ρ2 v ⊣⊢ p⟦ T ⟧ args (ρ1 >> ρ2) v;
}.

(** * Lemmas about the logical relation itself. *)
Section logrel_binding_lemmas.
  Context `{Htil : PTyInterpLemmas ty Σ}.

  Implicit Types
          (L T U: ty) (v: vl) (e: tm) (ρ : env).

  Lemma interp_subst_compose T {args} ρ1 ρ2 ρ3:
    ρ1 >> ρ2 = ρ3 → p⟦ T.|[ρ1] ⟧ args ρ2 ≡ p⟦ T ⟧ args ρ3.
  Proof. move=> <- v. exact: interp_subst_compose_ind. Qed.

  Lemma interp_weaken_one τ ρ {args} :
     p⟦ shift τ ⟧ args ρ ≡ p⟦ τ ⟧ args (stail ρ).
  Proof. apply interp_subst_compose. autosubst. Qed.

  Lemma interp_subst_one T v w ρ {args} :
    p⟦ T.|[v/] ⟧ args ρ w ≡ p⟦ T ⟧ args (v.[ρ] .: ρ) w.
  Proof. apply interp_subst_compose. autosubst. Qed.

  Lemma interp_subst_ids T ρ {args} : p⟦ T ⟧ args ρ ≡ p⟦ T.|[ρ] ⟧ args ids.
  Proof. symmetry. apply interp_subst_compose. autosubst. Qed.

  (**
    We have, unconditionally, that
    p⟦ T.|[∞ σ] ⟧ args ρ = p⟦ T ⟧ args (∞ σ >> ρ).

    But [∞ σ >> ρ] and [∞ σ.|[ρ]] are only equal for
    [length σ] entries.
  *)
  Lemma interp_subst_commute T σ ρ v (HclT : nclosed T (length σ)) args :
    p⟦ T.|[∞ σ] ⟧ args ρ v ≡ p⟦ T ⟧ args (∞ σ.|[ρ]) v.
  Proof.
    rewrite interp_subst_compose_ind !(interp_subst_ids T _ _) -hsubst_comp.
    (* *The* step requiring [HclT]. *)
    by rewrite (subst_compose _ _ HclT).
  Qed.
End logrel_binding_lemmas.
End persistent_ty_interp_lemmas.
End PTyInterpLemmas.
