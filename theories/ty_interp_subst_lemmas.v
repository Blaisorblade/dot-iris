From D Require Import prelude asubst_base dlang.
From iris.proofmode Require Import tactics.

Module Type TyInterpLemmas (Import VS : VlSortsFullSig) (Import LWP : LiftWp VS).

Class TyInterpLemmas ty Σ `{sort_ty : Sort ty} `{!TyInterp ty Σ} := {
  interp_subst_compose_ind T sb1 sb2 v:
    ⟦ T.|[sb1] ⟧ sb2 v ⊣⊢ ⟦ T ⟧ (sb1 >> sb2) v;
}.

(** * Lemmas about the logical relation itself. *)
Section logrel_binding_lemmas.
  Context `{Htil : TyInterpLemmas ty Σ}.

  Implicit Types
          (L T U: ty) (v: vl) (e: tm)
          (ρ : vls).

  Lemma interp_subst_compose T sb1 sb2 sb3:
    sb1 >> sb2 = sb3 → ⟦ T.|[sb1] ⟧ sb2 ≡ ⟦ T ⟧ sb3.
  Proof. move=> <- v. exact: interp_subst_compose_ind. Qed.

  Lemma interp_weaken_one v τ ρ:
     ⟦ τ.|[ren (+1)] ⟧ (v .: to_subst ρ) ≡ ⟦ τ ⟧ (to_subst ρ).
  Proof. apply interp_subst_compose, (to_subst_weaken [] [v]). Qed.

  Lemma interp_subst ρ τ v1 v2 :
    ⟦ τ.|[v1.[ren (+length ρ)]/] ⟧ (to_subst ρ) v2 ≡
    ⟦ τ ⟧ (v1 .: to_subst ρ) v2.
  Proof. apply interp_subst_compose, (to_subst_up []). Qed.

  Lemma interp_subst_ids T sb1 : ⟦ T ⟧ sb1 ≡ ⟦ T.|[sb1] ⟧ ids.
  Proof. symmetry. apply interp_subst_compose. autosubst. Qed.

  Lemma interp_nclosed_proper {T n sb1 sb2}:
    nclosed T n → eq_n_s sb1 sb2 n → ⟦ T.|[sb1] ⟧ ≡ ⟦ T.|[sb2] ⟧.
  Proof. intros HclT Heqs. f_equiv. apply HclT, Heqs. Qed.

  Lemma interp_closed {T n sb1 sb2}:
    nclosed T n → eq_n_s sb1 sb2 n → ⟦ T ⟧ sb1 ≡ ⟦ T ⟧ sb2.
  Proof.
    move => Hcl Heqs.
    rewrite (interp_subst_ids T sb1) (interp_subst_ids T sb2).
    exact: interp_nclosed_proper.
  Qed.

  Lemma interp_subst_commute_gen T {σ sb v}:
    ⟦ T.|[to_subst σ] ⟧ sb v ≡ ⟦ T ⟧ (to_subst σ >> sb) v.
  Proof. exact: interp_subst_compose. Qed.

  (*
    We have, unconditionally, that
    ⟦ T.|[to_subst σ] ⟧ sb = ⟦ T ⟧ (to_subst σ >> sb).

    But [to_subst σ >> sb] and [to_subst σ.|[sb]] are only equal for
    [length σ] entries.
  *)
  Lemma interp_subst_commute T σ sb v:
    nclosed T (length σ) →
    ⟦ T.|[to_subst σ] ⟧ sb v ≡ ⟦ T ⟧ (to_subst σ.|[sb]) v.
  Proof.
    rewrite interp_subst_commute_gen => HclT.
    apply (interp_closed HclT).
    apply eq_n_s_symm, to_subst_compose.
  Qed.

  Lemma interp_subst_closed T v w ρ:
    ⟦ T.|[v/] ⟧ (to_subst ρ) w ≡ ⟦ T ⟧ (v.[to_subst ρ] .: to_subst ρ) w.
  Proof. apply interp_subst_compose. autosubst. Qed.
End logrel_binding_lemmas.
End TyInterpLemmas.
