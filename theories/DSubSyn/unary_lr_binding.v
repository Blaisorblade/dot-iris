From iris.proofmode Require Import tactics.
From D.DSub Require Export synLemmas.
From D.DSubSyn Require Export unary_lr.

Implicit Types
         (L T U: ty) (v: vl) (e: tm)
         (Γ : ctx) (ρ : vls).

(** * Binding Lemmas about the logical relation itself. *)
Section logrel_binding_lemmas.
  Context `{!dsubSynG Σ} Γ.

  Lemma interp_env_lookup ρ T x:
    Γ !! x = Some T →
    ⟦ Γ ⟧* ρ -∗ ⟦ T.|[ren (+x)] ⟧ (to_subst ρ) (to_subst ρ x).
  Proof.
    elim: Γ ρ x => [//|τ' Γ' IHΓ] [|v ρ] x Hx /=. by iIntros "[]".
    iDestruct 1 as "[Hg Hv]". move: x Hx => [ [->] | x Hx] /=.
    - rewrite hsubst_id. by [].
    - rewrite hrenS.
      iApply (interp_weaken_one v (T.|[ren (+x)]) ρ).
      iApply (IHΓ ρ x Hx with "Hg").
  Qed.
End logrel_binding_lemmas.
