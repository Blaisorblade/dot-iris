From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language ectx_language.
From iris.proofmode Require Import tactics.
From D Require Import tactics.
From D.Dot Require Import unary_lr unary_lr_binding synLemmas rules.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms)
         (Γ : ctx) (ρ : vls).

Section Sec.
  Context `{HdotG: dotG Σ}.

  (** Core definitions for singleton types. ⟦ w.type ⟧ ρ v *)
  Definition sem_singleton w ρ v : iProp Σ := (⌜ w.[to_subst ρ] = v ∧ nclosed_vl v 0 ⌝)%I.
  Arguments sem_singleton /.

  (* Core typing lemmas, sketches. TODO: make the above into a type, and add all
     the plumbing. *)
  Lemma self_sem_singleton ρ v: cl_ρ ρ → nclosed_vl v 0 → sem_singleton v ρ v.
  Proof.
    iIntros (Hclρ Hclv) "/= !%"; split => //. by apply closed_subst_vl_id.
  Qed.

  Lemma other_sem_singleton ρ w v v':
    (sem_singleton w ρ v →
    sem_singleton w ρ v' ↔ sem_singleton v ρ v')%I.
  Proof.
    iIntros ((Hv & Hclv)) "/="; iSplit; iIntros ((Hv1 & Hclv')) "!%"; split => //;
    by [> rewrite closed_subst_vl_id // -Hv -Hv1 | rewrite Hv -Hv1 closed_subst_vl_id ].
  Qed.

  Lemma tskip_self_sem_singleton ρ v: cl_ρ ρ → nclosed_vl v 0 →
    WP (tskip (tv v)) {{ v, sem_singleton v ρ v }}%I.
  Proof.
    iIntros (Hclρ Hclv) "/=".
    iApply wp_pure_step_later => //; iApply wp_value.
    iIntros "!%"; split => //. by apply closed_subst_vl_id.
  Qed.

  Lemma tskip_other_sem_singleton ρ w v v':
    sem_singleton w ρ v -∗
    WP (tskip (tv v)) {{ v', sem_singleton w ρ v' }}%I.
  Proof.
    iIntros (H); iApply wp_pure_step_later => //; iApply wp_value. by iIntros "!%".
  Qed.

  Lemma ietp_later_works Γ W T v:
    W :: Γ ⊨ tv v : T -∗
    TLater W :: Γ ⊨ tv v: TLater T.
  Proof.
    iIntros "/= #[% #Hv]". move: H => Hclv. iFrame (Hclv). iIntros "!> *".
    destruct ρ as [|w ρ]; first by iIntros.
    iIntros "[#Hg [% #Hw]]". move: H => Hclw.
    iApply wp_value.
    iPoseProof (interp_env_ρ_closed with "Hg") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in *.
    have Hclvs: nclosed_vl v.[to_subst (w :: ρ)] 0.
      by apply fv_to_subst_vl; naive_solver eauto using fv_tv_inv.
    iFrame (Hclvs).
    iApply wp_value_inv'. iApply "Hv". by iSplit.
  Qed.

  Import uPred.
  Lemma internal_iff_eq_try1 (P Q: iProp Σ) `(!Affine P) `(!Affine Q): (P ↔ Q ⊢ P ≡ Q)%I.
  Proof.
    rewrite /bi_iff; unseal.
    constructor=> n x Hv [Hf1 Hf2].
    constructor=> n' x' Hle Hv'.
    have Hxl: x ≼ x' by admit. (* False, but needed below. *)
    split.
    - apply Hf1; first apply Hxl; done.
    - apply Hf2; first apply Hxl; done.
    all: fail.
  Abort.

  Context (Γ: list ty).

  Lemma inclusion_equiv_wp_upd {P Q}:
    ((□∀ e, WP e {{P}} → WP e {{Q}})%I ≡ (□∀ v, P v → Q v)%I).
  Proof.
    iSplit; iIntros "#Himpl !> * HP".
    - setoid_rewrite wp_unfold.
        by iApply ("Himpl" $! (of_val v)).
    - iApply (wp_wand with " [-]"); first iApply "HP".
      iIntros "* HP". by iApply "Himpl".
  Qed.
End Sec.
