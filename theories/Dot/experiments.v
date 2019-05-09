From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language ectx_language.
From iris.proofmode Require Import tactics.
From D Require Import tactics.
From D.Dot Require Import unary_lr unary_lr_binding synLemmas rules
  lr_lemma_nobinding.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms)
         (Γ : ctx) (ρ : vls).

Section Sec.
  Context `{HdotG: dotG Σ}.

  (** Rename. *)
  Lemma iterate_Sub_Mono Γ T i j:
    Γ ⊨ [ T, i ] <: [T, j + i].
  Proof.
    iInduction j as [] "IHj".
    - iApply Sub_Refl.
    - iApply (Sub_Trans with "IHj").
      iApply Sub_Mono.
  Qed.

  Lemma iterate_Sub_Later Γ T i j:
    Γ ⊨ [T, j + i] <: [iterate TLater j T, i].
  Proof.
      iInduction j as [] "IHj" forall (T).
    - iApply Sub_Refl.
    - iApply Sub_Trans; rewrite ?iterate_Sr /=.
      + iApply Sub_Later.
      + iApply ("IHj" $! (TLater T)).
  Qed.

  Lemma Distr_TLater_And T1 T2 ρ v:
    ⟦ TLater (TAnd T1 T2) ⟧ ρ v ⊣⊢
    ⟦ TAnd (TLater T1) (TLater T2) ⟧ ρ v.
  Proof.
    iSplit.
    iIntros "/= [$ [??]]"; eauto.
    iIntros "/= [[$?] [_?]]"; eauto.
  Qed.

  Lemma selfIntersect Γ T U i j:
    Γ ⊨ [ T, i ] <: [ U, j + i ] -∗
    Γ ⊨ [ T, i ] <: [ TAnd U T, j + i ].
  Proof.
    iIntros "H"; iApply (Sub_And with "[H//] []").
    iApply iterate_Sub_Mono.
  Qed.

  Lemma selfIntersectLater Γ T U i:
    Γ ⊨ [ T, i ] <: [ TLater U, i ] -∗
    Γ ⊨ [ T, i ] <: [ TLater (TAnd T U), i ].
  Proof.
    iIntros "H"; iSimpl; setoid_rewrite Distr_TLater_And.
    iApply (Sub_And with "[] H").
    iApply (Sub_Trans _ _ T _ _ (S i)).
    - by iApply Sub_Mono.
    - by iApply Sub_Later.
  Qed.

  Lemma Distr_TLaterN_And T1 T2 j ρ v:
    nclosed_vl v 0 →
    ⟦ iterate TLater j (TAnd T1 T2) ⟧ ρ v ⊣⊢
    ⟦ TAnd (iterate TLater j T1) (iterate TLater j T2) ⟧ ρ v.
  Proof.
    intro Hclv.
    rewrite /= !iterate_TLater_later //=.
    iSplit; iIntros "/= [??]"; iSplit; by [].
  Qed.

  Lemma sub_rewrite_2 Γ T U1 U2 i:
    (∀ ρ v, nclosed_vl v 0 → ⟦ U1 ⟧ ρ v ⊣⊢ ⟦ U2 ⟧ ρ v) →
    Γ ⊨ [ T, i ] <: [ U1, i ] ⊣⊢
    Γ ⊨ [ T, i ] <: [ U2, i ].
  Proof.
    iIntros (Heq); iSplit; iIntros "/= #H !>" (ρ v Hcl) "#Hg #HT";
      [rewrite -Heq //|rewrite Heq //]; by iApply "H".
  Qed.

  Lemma sub_rewrite_1 Γ T1 T2 U i:
    (∀ ρ v, nclosed_vl v 0 → ⟦ T1 ⟧ ρ v ⊣⊢ ⟦ T2 ⟧ ρ v) →
    Γ ⊨ [ T1, i ] <: [ U, i ] ⊣⊢
    Γ ⊨ [ T2, i ] <: [ U, i ].
  Proof.
    iIntros (Heq); iSplit; iIntros "/= #H !>" (ρ v Hcl) "#Hg #HT";
      [rewrite -Heq //|rewrite Heq //]; by iApply "H".
  Qed.

  Lemma eq_to_bisub Γ T1 T2 i:
    (∀ ρ v, nclosed_vl v 0 → ⟦ T1 ⟧ ρ v ⊣⊢ ⟦ T2 ⟧ ρ v) → True ⊢
    Γ ⊨ [ T1, i ] <: [ T2, i ] ∗
    Γ ⊨ [ T2, i ] <: [ T1, i ].
  Proof.
    iIntros (Heq) "_"; iSplit; iIntros "/= !>" (ρ v Hcl) "#Hg #HT";
      [rewrite -Heq //|rewrite Heq //]; by iApply "H".
  Qed.

  Lemma selfIntersectLaterN Γ T U i j:
    Γ ⊨ [ T, i ] <: [ iterate TLater j U, i ] -∗
    Γ ⊨ [ T, i ] <: [ iterate TLater j (TAnd T U), i ].
  Proof.
    iIntros "H".
    setoid_rewrite (sub_rewrite_2 Γ T _ _ i (Distr_TLaterN_And T U j)).
    iApply (Sub_And with "[] H").
    iApply (Sub_Trans _ _ T _ _ (j + i)).
    - by iApply iterate_Sub_Mono.
    - by iApply iterate_Sub_Later.
  Qed.
  From D.Dot Require Import lr_lemma.
  Lemma iterate_Later_Sub Γ T i j:
    Γ ⊨ [iterate TLater j T, i] <: [T, i + j].
  Proof.
      iInduction j as [] "IHj" forall (T); rewrite ?plusnO ?iterate_Sr ?plusnS.
    - iApply Sub_Refl.
    - iApply Sub_Trans.
      iApply ("IHj" $! (TLater T)).
      iApply Later_Sub.
  Qed.

  (* The point is, ensuring this works with T being a singleton type :-) *)
  Lemma dropLaters Γ e T U i:
    Γ ⊨ e : T -∗ Γ ⊨ [T, 0] <: [iterate TLater i U, 0] -∗
    Γ ⊨ iterate tskip i e : TAnd T U.
  Proof.
    iIntros "HeT Hsub".
    iApply (T_Sub with "HeT [Hsub]").
    iApply (Sub_Trans with "[-]").
    - by iApply selfIntersectLaterN.
    - iApply (iterate_Later_Sub _ _ 0 i).
  Qed.

  (* Exercise: do this with only *syntactic* typing rules. *)

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
