From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.
Require Import Dot.tactics.
Require Import Dot.unary_lr.
Require Import Dot.synLemmas.
(* Workflow: Use this file for new experiments, and move experiments here in appropriate files once they're done. *)

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms)
         (Γ : ctx) (ρ : listVlC).

Section Sec.
  Context `{HdotG: dotG Σ}.

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
