From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.
From Dot Require Import tactics unary_lr synLemmas.
(* Workflow: Use this file for new experiments, and move experiments here in appropriate files once they're done. *)

(* From iris.bi Require Export derived_laws_bi. *)
(* From iris.bi Require Import derived_laws_sbi. *)
(* From iris.algebra Require Import monoid. *)

(* Module bi. *)
(* Import interface.bi. *)
(* Import derived_laws_bi.bi. *)
(* Import derived_laws_sbi.bi. *)

(* Section sbi_derived. *)
(* Context {PROP : sbi}. *)
(* Implicit Types φ : Prop. *)
(* Implicit Types P Q R : PROP. *)
(* About bi.internal_eq_rewrite'. *)
(* Hint Resolve internal_eq_refl. *)
(* (* Hint Extern 100 (NonExpansive _) => solve_proper. *) *)

(* Lemma internal_eq_iff P Q (_: Affine P) (_: Affine Q): (P ↔ Q ⊢ P ≡ Q)%I. *)
(* Proof. *)
(*   iIntros "H". *)
(*   iApply pure_internal_eq. *)
(*   About iff_equiv. *)
(*   pose proof (iff_equiv P Q) as Hf. *)
(*   iPoseProof (Hf with "H") as "Hf2". *)
(*   iApply Hf in "H". *)
(*   with "H"). *)
(*   iApply (iff_equiv P Q with "H"). *)
(*   Set Printing All. *)
(*   pose proof (proj2 (bi.equiv_spec P Q)). *)
(*   admit. *)
(*   SearchAbout bi_iff. *)
(*   iPureIntro. *)
(*   apply H. *)
(*   iDestruct "H" as "[H1 H2]". *)
(*   iDestruct  *)
(*   Set Printing All. *)
(*   iApply bi.equiv_spec. *)
(*       pose proof (proj2 (bi.equiv_spec (⟦ T' ⟧ ρ v) (⟦ T'' ⟧ ρ v))) as Heq. *)
(*       pose proof (proj2 (bi.equiv_spec (⟦ T' ⟧ ρ v) (⟦ T'' ⟧ ρ v))) as Heq. *)
(*   iSplit. *)
(*   OCheck internal_eq_rewrite'. *)
(*   apply (internal_eq_rewrite' P Q (λ Q, P ≡ Q))%I; auto using iff_refl. solve_proper. Qed. *)

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms)
         (Γ : ctx) (ρ : listVlC).

Section Sec.
  Context `{HdotG: dotG Σ}.

  Lemma internal_iff_eq_try1 (P Q: iProp Σ) `(!Affine P) `(!Affine Q): (P ↔ Q ⊢ P ≡ Q)%I.
  Proof.
    constructor.
    remember (uPred_holds P) as P'. rewrite /uPred_holds in HeqP'.
    remember (uPred_holds Q) as Q'. rewrite /uPred_holds in HeqQ'.
    rewrite /uPredSI /sbi_internal_eq /= /bi_iff /= uPred_internal_eq_eq /uPred_internal_eq_def /uPred_holds /= /bi_and /= uPred_and_eq /uPred_and_def /= /bi_impl /= uPred_impl_eq /uPred_impl_def /= /uPred_holds.
    (* progress rewrite -HeqQ' -HeqP'. *)
    intros n x Hv [Hf1 Hf2]. constructor. intros n' x' Hle Hv'.
    assert (x ≼ x') as Hxl by admit. (* False, but needed below. *)
    split.
    - apply Hf1; first apply Hxl; done.
    - apply Hf2; first apply Hxl; done.
  Abort.
  Require Import Dot.synToSem.

  Lemma translations_types_equivalent_vals T T' T'' v ρ:
    (t_ty T T' → t_ty T T'' → ⟦ T' ⟧ ρ v ≡ ⟦ T'' ⟧ ρ v)%I.
  Proof.
    (* -  *)
    (*   iIntros. *)
(*       Check uPred_primitive.equiv_spec. *)
(* (* From iris.base_logic Require Import upred. *) *)
(* (*       Import uPred. *) *)
(* (*       Check uPred. *) *)
(* From iris.bi Require Import bi. *)
(* Import bi. *)
(*       Check bi.equiv_spec . *)
(*       pose proof (proj2 (bi.equiv_spec (⟦ T' ⟧ ρ v) (⟦ T'' ⟧ ρ v))) as Heq. *)
(* From iris.bi Require Import derived_laws_sbi. *)
(*       Set Printing All. *)
(*       About internal_eq_iff. *)
(*       pose proof ((bi.internal_eq_iff (⟦ T' ⟧ ρ v) (⟦ T'' ⟧ ρ v))) as Heq1. *)
(*       Unset Printing All. *)
(*       iApply Heq. *)
(*       Locate "↔". *)
(*       SearchAbout and. *)
(*       destruct H1. *)
(*       pose proof (bi.equiv_spec (⟦ T' ⟧ ρ v) (⟦ T'' ⟧ ρ v)) as H1. *)
(*       iRewrite (bi_mixin_equiv_spec (⟦ T' ⟧ ρ v) (⟦ T'' ⟧ ρ v)). *)
(*       Set Printing All. *)
(*       SearchAbout (sbi_internal_eq). *)
(*       Set Printing All. *)
(*       SearchAbout uPred_entails. *)
(*       Check @bi.internal_eq_iff. *)
(*       Search *)
(*         (@bi_entails (sbi_bi _) (@sbi_internal_eq _ (sbi_ofeC _) _ _) (@bi_iff (sbi_bi _) _ _)). *)
(*       Require Import ssrbool. *)
(*       SearchHead sbi_internal_eq. *)
(*       Search "~~". *)
(*       Search (bi_entails (sbi_internal_eq _ _) (bi_iff _ _))%I. *)
(*       SearchPattern uPred_internal_eq. *)
(*       set (t := (@sbi_internal_eq (uPredSI (iResUR Σ)) (uPredC (iResUR Σ)))). *)
(*       hnf in t. *)
(*       Set Printing All. *)
(*        red. *)
(*        hnf. *)
(*        (ofe_mor_car _ _ (ofe_mor_car _ _ (@interp Σ H T') ρ) v) *)
(*              (ofe_mor_car _ _ (ofe_mor_car _ _ (@interp Σ H T'') ρ) v))). *)

    iInduction T as [] "IHT" forall (T' T'' ρ v); iIntros "#H1 #H2";
      destruct T' => //=; destruct T'' => //; cbn.
                                    properness.
                                    try (iDestruct "H1" as "[H11 H12]"); try (iDestruct "H2" as "[H21 H22]").
    all: try iRewrite ("IHT" $! _ _ ρ v with "H11 H21"); try iRewrite ("IHT1" $! _ _ ρ v with "H12 H22"); try iRewrite ("IHT" $! _ _ ρ v with "H1 H2"); try done.
    -
      iAssert (∀ ρ v, ⟦ T'1 ⟧ ρ v ≡ ⟦ T''1 ⟧ ρ v)%I as "#H". by iIntros; iApply ("IHT").
      admit.
    - by iRewrite ("IHT" $! _ _ (v :: ρ) v with "H1 H2").
    - 
      iDestruct "H11" as "->".
      iDestruct "H21" as "->".
      iAssert (∀ v, ⟦ T' ⟧ ρ v ≡ ⟦ T'' ⟧ ρ v)%I as "#H". by iIntros; iApply ("IHT").
      Fail iRewrite ("H" $! _).
      admit.
  Abort.
    (*   iClear "H". *)
    (*   About (≡). *)
    (*   About sbi_internal_eq. *)
    (* Check (1 ≡ 2: iProp Σ)%I. *)
    (* Check bi_emp_valid. *)

    (*   red. *)
    (*   iEval (hnf). *)
    (*   iRewrite ("H" $! ρ). *)

    (* all: try iRewrite (IHT1 _ _ ρ v with "H11 H21"); try iRewrite (IHT2 _ _ ρ v with "H12 H22"); *)
    (* try iRewrite (IHT _ _ ρ v with "H1 H2"). *)
    (* all: try done. *)

    (* iPoseProof (IHT1 _ _ ρ v with "H11 H21") as "->". *)
    (* iPoseProof (IHT2 _ _ ρ v with "H11 H21") as "->". *)
    (* try iRewrite (IHT2 _ _ ρ v with "H12 H22"); *)
    (* admit. *)
    (* by iRewrite (IHT _ _ (v :: ρ) v with "H1 H2"). *)
    (* Check bi.sep_proper. *)
    (* - *)
    (*   About sbi_internal_eq. *)
    (*   Check sbi_internal_eq. *)
    (* Set Printing All. *)
    (* Check (1 ≡ 2)%I. *)
    (* Check bi_emp_valid. *)
    (* properness. *)
    (* iRewrite (IHT _ _ ρ with "H1 H2"). *)


  (* Can't find how to use it. *)
  Lemma later_persistently_1 (P: iProp Σ): (▷ □ P → ▷ P)%I.
  Proof. iIntros; naive_solver. Qed.

  (* (Expression) subtyping, strengthened to be equivalent to valye subtyping. *)
  Definition istp Γ T1 T2 : iProp Σ :=
    (ivstp Γ T1 T2 ∧ □∀ ρ e, ⟦Γ⟧* ρ → ⟦T1⟧ₑ ρ e → ⟦T2⟧ₑ ρ e)%I.
  Global Arguments istp /.

  Definition uvstp Γ T1 T2: iProp Σ :=
    (□∀ ρ v, ⟦Γ⟧*ρ -∗ ((*|={⊤}=>*) ⟦T1⟧ ρ v) → |={⊤}=> ⟦T2⟧ ρ v)%I.
  Global Arguments uvstp /.

  Notation "Γ ⊨e T1 <: T2" := (istp Γ T1 T2) (at level 74, T1, T2 at next level).
  Notation "Γ ⊨> T1 <: T2" := (uvstp Γ T1 T2) (at level 74, T1, T2 at next level).

  Definition uvstp2 Γ T1 T2: iProp Σ :=
    (□∀ ρ v, ⟦Γ⟧*ρ → |={⊤}=> (⟦T1⟧ ρ v) → ⟦T2⟧ ρ v)%I.
  Global Arguments uvstp2 /.
  (* Print uvstp2. *)

  (* To be able to use uvstp2, maybe we can use the following. Since it uses a single WP, it's clear
   * that we're talking about a single execution of e! That's weaker for non-deterministic
   * languages, but makes more sense: subtyping is about the same result after all.
   * However, this also asserts that all expressions are safe???
   *)
  Definition istp2 Γ T1 T2 : iProp Σ := (□∀ e ρ, ⟦Γ⟧* ρ →
                                                 WP e {{v, ⟦T1⟧ ρ v → ⟦T2⟧ ρ v}})%I.

  Lemma dropUpdateFromPremise {A B: iProp Σ}:
    (□ ((|={⊤}=> A) → |={⊤}=> B) ↔ □ (A → |={⊤}=> B))%I.
  Proof.
    iSplit; iIntros "#Himpl !>".
    - iIntros "HA". by iApply "Himpl".
    - iIntros ">HA". by iApply "Himpl".
  Qed.

  Context (Γ: list ty).

  (* Still wrong. The correct statement will arise from the translation. *)
  Lemma idtp_tmem_i T γ l ρ1:
    γ ⤇ dot_interp T -∗
    idtp Γ (TTMem l T T) l (dtysem ρ1 γ).
  Proof.
    unfold idtp.
    iIntros "/= #Hγ". iSplit. admit. iIntros " !> **".
    repeat iSplit => //.
    admit.
    iExists (interp T), _. iSplit; first auto.
    iModIntro; repeat iSplitL; iIntros "**" => //.
  Abort.

  (* Lemma iuvstp_later T: Γ ⊨> T <: TLater T. *)
  (* Proof. by iIntros "!> ** /=". Qed. *)

  Lemma istp2ivstp T1 T2: (Γ ⊨e T1 <: T2 → Γ ⊨ T1 <: T2)%I.
  Proof. by iIntros "/= [#? _]". Qed.

  Lemma ivstp2istp T1 T2: (Γ ⊨ T1 <: T2 → Γ ⊨e T1 <: T2)%I.
  Proof.
    iIntros "/= #Hstp". iFrame "Hstp".
    iIntros " !> * #Hg HeT1".
    iApply wp_fupd.
    iApply (wp_wand with " [-]"); try iApply "HeT1".
    iIntros "* HT1". by iApply "Hstp".
  Qed.


  (** We prove that vstp and stp are equivalent, so that we can use them
      interchangeably; and in my previous proofs, proving uvstp was easier. *)
  Lemma istpEqIvstp T1 T2: (Γ ⊨e T1 <: T2) ≡ (Γ ⊨ T1 <: T2).
  Proof. iSplit; iIntros; by [iApply istp2ivstp| iApply ivstp2istp]. Qed.

  Lemma iStpUvstp T1 T2: (Γ ⊨e T1 <: T2 → Γ ⊨> T1 <: T2)%I.
  Proof.
    (* Inspired by the proof of wp_value_inv'! *)

    (* More manual.*)
    (* iIntros "/= #Hsub !> * #Hg *". *)
    (* iSpecialize ("Hsub" $! (of_val v) with "Hg"). *)
    (* rewrite !wp_unfold /wp_pre /=. iIntros. by iApply "Hsub". *)
    (* Restart. *)
    iIntros "/= [#Hsub1 #Hsub2] !> * #Hg * #?".
    by iApply "Hsub1".
    (* Or *)
    (* setoid_rewrite wp_unfold. *)
    (* by iApply ("Hsub2" $! _ (of_val v)). *)
  Qed.



  (* Does the converse direction hold? Do we need it? *)
  (* Lemma iStpVstp Γ T1 T2: (istp Γ T1 T2 -∗ ivstp Γ T1 T2)%I. *)
  (* This direction is useful when we have istp as an hypothesis. *)
  (* What I can easily prove: *)

  Lemma vstpToUvstp T1 T2 : (Γ ⊨ T1 <: T2 → Γ ⊨> T1 <: T2)%I.
    iIntros "#Hstp !> * #Hg #HT1 !>".
    by iApply ("Hstp").
  Qed.

  Lemma iVstpStp T1 T2: (Γ ⊨ T1 <: T2 → Γ ⊨e T1 <: T2)%I.
  Proof. iApply ivstp2istp. Qed.
  (*   by iIntros "#Hsub"; iApply istpEqIvstp; iApply vstpToUvstp. *)
  (* Qed. *)
  (*   iIntros "#Hsub !> * #Hg HT1". *)
  (*   iApply (wp_wand with " [-]"). iApply "HT1". by iIntros; iApply "Hsub". *)
  (* Qed. *)

  (* Maybe the update is OK; after all, it's part of the definition of weakest
     preconditions, and it pairs with the later. But it confuses me honestly.

     In any case, once we add pointers typing will clearly depend on resources (such as the heap), so we can just as well deal with it now. *)
  (* Also, subtyping now implies subtyping after update: *)
  (* But not viceversa, because |==> P talks about the *existence* of a future resource world
   where P holds, even though P might be false now. *)
  Lemma uvstpToVstp T1 T2 : (Γ ⊨> T1 <: T2 → Γ ⊨ T1 <: T2)%I.
    iIntros "/= #Hstp !> * #Hg #Ht1".
    Fail iApply "Hstp".
  Abort.

  Lemma uvstp21 T1 T2: (uvstp2 Γ T1 T2 → uvstp Γ T1 T2)%I.
  Proof.
    iIntros "/= #Hstp !> * #Hg".
    iDestruct ("Hstp" $! ρ v with "Hg") as "H".
    iIntros "HT1". by iApply "H".
  Qed.

  (* False. *)
  Lemma uvstp12 T1 T2: (uvstp Γ T1 T2 -∗ uvstp2 Γ T1 T2)%I.
  Proof.
    iIntros "/= #Hstp !> * #Hg".
    iSpecialize ("Hstp" $! _ _ with "Hg").
    Fail iMod "Hstp".
    Fail iApply "Hstp".
    iIntros "!>".
  Abort.

  Lemma iStpUvstp2 T1 T2: (istp2 Γ T1 T2 -∗ uvstp2 Γ T1 T2)%I.
  Proof.
    iIntros "/= #Hsub !> * #Hg *".
    iSpecialize ("Hsub" $! (of_val v) with "Hg").
    rewrite !wp_unfold /wp_pre /=. by iApply "Hsub".
  Qed.

  Lemma inclusion_equiv_wp_upd {P Q}:
    ((□∀ e, WP e {{P}} → WP e {{Q}})%I ≡ (□∀ v, P v → |={⊤}=> Q v)%I).
  Proof.
    iSplit; iIntros "#Himpl !> * HP".
    - setoid_rewrite wp_unfold.
        by iApply ("Himpl" $! (of_val v)).
    - iApply wp_fupd.
      iApply (wp_wand with " [-]"); first iApply "HP".
      iIntros "* HP". by iApply "Himpl".
  Qed.

  Lemma alloc_sp T:
    (|==> ∃ γ, γ ⤇ (λ ρ v, interp T ρ v))%I.
  Proof. by apply saved_interp_alloc. Qed.

  (* [idsσ] was needed for the lemma below, but no more as [def_interp] now expects
   *closed* definitions. *)

  (* (** Create an identity environment vls. *) *)
  (* (*  * The definition gives the right results but is not ideal to reason about. It *) *)
  (* (*    is hard to prove it does what it should, and it's likely theorems using it *) *)
  (* (*    should be rephrased in terms of the translation. *) *)
  (* (*  *) *)
  (* Definition idsσ: vls -> vls := foldr (λ _, push_var) []. *)
  (* Lemma idsσ_is_id ρ: ρ = (idsσ ρ).|[to_subst ρ]. *)
  (* Admitted. *)

  Lemma alloc_dtp_tmem_i T ρ l:
    ⟦Γ⟧* ρ -∗
    (|==> ∃ γ, def_interp (TTMem l T T) l ρ (dtysem ρ γ))%I.
  Proof.
    iIntros "#Hg /=".
    iDestruct (alloc_sp T) as "HupdSp".
    iMod "HupdSp" as (γ) "#Hsp".
    iModIntro; iExists γ; iSplit; try done; iExists _, _; iSplit; first auto.
    repeat iSplitL; naive_solver.
  Qed.
End Sec.
