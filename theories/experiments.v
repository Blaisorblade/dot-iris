Require Import Dot.tactics.
Require Import Dot.unary_lr.
Require Import Dot.synLemmas.
(* Workflow: Use this file for new experiments, and move experiments here in appropriate files once they're done. *)

Section Sec.
  Context `{HdotG: dotG Σ}.

  (* Can't find how to use it. *)
  Lemma later_persistently_1 (P: iProp Σ): (▷ □ P → ▷ P)%I.
  Proof. iIntros; naive_solver. Qed.

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

  (* Does the converse direction hold? Do we need it? *)
  (* Lemma iStpVstp Γ T1 T2: (istp Γ T1 T2 -∗ ivstp Γ T1 T2)%I. *)
  (* This direction is useful when we have istp as an hypothesis. *)
  (* What I can easily prove: *)

  Lemma vstpToUvstp T1 T2 : (Γ ⊨v T1 <: T2 → Γ ⊨> T1 <: T2)%I.
    iIntros "#Hstp !> * #Hg #HT1 !>".
    by iApply ("Hstp").
  Qed.

  Lemma iVstpStp T1 T2: (Γ ⊨v T1 <: T2 → Γ ⊨ T1 <: T2)%I.
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
  Lemma uvstpToVstp T1 T2 : (Γ ⊨> T1 <: T2 → Γ ⊨v T1 <: T2)%I.
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




  Lemma alloc_dtp_tmem_i T ρ l:
    ⟦Γ⟧* ρ -∗
    (|==> ∃ γ, def_interp (TTMem l T T) l ρ (dtysem (idsσ ρ) γ))%I.
  Proof.
    iIntros "#Hg /=".
    iDestruct (alloc_sp T) as "HupdSp".
    iMod "HupdSp" as (γ) "#Hsp".
    iModIntro; iExists γ; iSplit; try done; iExists _, _; iSplit; first auto.
    rewrite <- idsσ_is_id.
    repeat iSplit; naive_solver.
  Qed.
End Sec.
