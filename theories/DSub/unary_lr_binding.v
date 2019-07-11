From iris.proofmode Require Import tactics.
From D.DSub Require Export unary_lr synLemmas.

Implicit Types
         (L T U: ty) (v: vl) (e: tm)
         (Γ : ctx) (ρ : vls).

(** * Binding Lemmas about the logical relation itself. *)
Section logrel_binding_lemmas.
  Context `{!dlangG Σ} Γ.

  Lemma interp_env_ρ_fv ρ: ⟦ Γ ⟧* ρ -∗ ⌜ nclosed ρ 0 ⌝.
  Proof.
    rewrite interp_env_ρ_closed. iIntros "!%". exact: cl_ρ_fv.
  Qed.

  Lemma interp_env_to_subst_closed ρ x: x < length ρ → ⟦ Γ ⟧* ρ -∗ ⌜ nclosed_vl (to_subst ρ x) 0 ⌝%I.
  Proof.
    rewrite interp_env_ρ_closed. iIntros "!%" (??). exact: closed_to_subst.
  Qed.

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

  Lemma ietp_closed_vl T v: Γ ⊨ tv v : T -∗ ⌜ nclosed_vl v (length Γ) ⌝.
  Proof. rewrite ietp_closed; iPureIntro; exact: fv_tv_inv. Qed.
End logrel_binding_lemmas.
