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
  Proof.
  (*   by iIntros "#Hsub"; iApply istpEqIvstp; iApply vstpToUvstp. *)
  (* Qed. *)
    iIntros "#Hsub !> * #Hg HT1".
    iApply (wp_wand with " [-]"). iApply "HT1". by iIntros; iApply "Hsub".
  Qed.

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



  (* Locate "|==>". *)
  (* Check @bupd. *)
  (* Print BUpd. *)
  (* SearchAbout BUpd. *)
  (* SearchAbout BiBUpd. *)

  (* Print SP. *)
  (* Check ⊤%I. *)

  (* Program Definition wtovdm (dw: dm): (|==> ∃(dv: gname), True)%I := *)

  Lemma alloc_sp T:
    (|==> ∃ γ, SP γ (uinterp T))%I.
  Proof. by apply saved_pred_alloc. Qed.

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

  (* (* Print saved_pred_own. *) *)
  (* (* Print Next. *) *)
  (* (* Print savedPredG. *) *)
  (* (* Eval cbn in (∀ A, savedAnythingG Σ (A -c> ▶ ∙)). *) *)
  (* (* Check savedAnythingG. *) *)
  (* (* From iris Require Import algebra.ofe. *) *)
  (* (* Check savedEnvD. *) *)
  (* (* Alternative to savedPredG *) *)
  (* Notation savedEnvDG := (savedAnythingG Σ (listVlC -c> vlC -c> ▶ ∙)%CF). *)
  (* Notation savedEnvDΣ := (savedAnythingΣ (listVlC -c> vlC -c> ▶ ∙)). *)

  (* (* (* Notation savedEnvDG := (savedAnythingG Σ (listVlC -c> vlC -c> ▶ ∙)). *) *) *)
  (* (* (* Notation savedEnvDΣ := (savedAnythingΣ (listVlC -c> vlC -c> ▶ ∙)). *) *) *)
  (* (* (* Print saved_anything_own. *) *) *)
  (* (* (* Print savedAnythingG. *) *) *)
  (* (* (* Print cFunctor. *) *) *)
  (* (* Print savedPredG. *) *)
  (* (* Print saved_pred_own. *) *)

  (* (* Print saved_anything_own. *) *)
  (* Context `{savedEnvDG}. *)
  (* Program Definition saved_envDG_own (γ : gname) (Φ : listVlC -n> vlC -n> iProp Σ): iProp Σ := *)
  (*   saved_anything_own (F := listVlC -c> vlC -c> ▶ ∙) γ (λ ρ, λne v, Next (Φ ρ v)). *)

  (* Instance saved_envDG_own_contractive γ: *)
  (*   Contractive *)
  (*               (saved_envDG_own γ: (listVlC -n> vlC -n> iProp Σ) → iProp Σ). *)
  (* Proof. *)
  (*   solve_proper_core ltac:(fun _ => *)
  (*                   first [ intros ? ?; progress simpl | by auto | f_contractive | f_equiv ]). *)

  (*   (* solve_proper_prepare. *) *)

  (*   (* repeat first [eassumption | first [ intros ? ?; progress simpl | by auto | f_contractive | f_equiv ]]. *) *)
  (*   (* cbn in H0. *) *)
  (*   (* solve [apply H0]. *) *)
  (*   (* Restart. *) *)
  (*   (* (* Summarizes to: *) *) *)
  (*   (* solve_proper_core ltac:(fun _ => *) *)
  (*   (*                 first [ intros ? ?; progress simpl | by auto | f_contractive | f_equiv | apply H0 ]). *) *)
  (*   (* (* But that is really fragile.*) *) *)
  (* Qed. *)

  (* Lemma saved_envDG_alloc_strong (G : gset gname) (Φ : listVlC -n> vlC -n> iProp Σ) : *)
  (*   (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ saved_envDG_own γ Φ)%I. *)
  (* Proof. iApply saved_anything_alloc_strong. Qed. *)

  (* Lemma saved_envDG_alloc (Φ : listVlC -n> vlC -n> iProp Σ) : *)
  (*   (|==> ∃ γ, saved_envDG_own γ Φ)%I. *)
  (* Proof. iApply saved_anything_alloc. Qed. *)

  (* (* We put the `x` on the outside to make this lemma easier to apply. *) *)
  (* Lemma saved_envDG_agree1 `{savedPredG Σ A} γ Φ Ψ x : *)
  (*   saved_envDG_own γ Φ -∗ saved_envDG_own γ Ψ -∗ ▷ (Φ x ≡ Ψ x). *)
  (*   unfold saved_envDG_own. iIntros "#HΦ #HΨ". *)
  (*   Import uPred. *)
  (*   iApply later_equivI. *)
  (*   (* Check @saved_anything_agree. *) *)
  (*   (* Eval hnf in (listVlC -c> vlC -c> ▶ iProp Σ)%CF. *) *)
  (*   iDestruct (saved_anything_agree (F := listVlC -c> vlC -c> ▶ ∙) with "HΦ HΨ") as "Heq". *)
  (*   simpl. *)

  (*   (* Check @ofe_fun_equivI. *) *)
  (*   iDestruct (@ofe_fun_equivI _ (listVlC) (λ _, vlC -n> laterC (iProp Σ)) (λ ρ, λne v, Next (Φ ρ v)) (λ ρ, λne v, Next (Ψ ρ v))) as "[Heq1 _]". *)
  (*   Fail iSpecialize ("Heq1" with "Heq"). *)
  (*   Abort. *)
  (* (* (*   by iDestruct ("Heq1" with "Heq") as "?". *) *) *)

  (* (* (*   simpl. *) *) *)
  (* (* (*   Unset Printing Notations. *) *) *)
  (* (* (*   Set Printing Implicit. *) *) *)
  (* (* (*   simpl in *. *) *) *)
  (* (* (*   iDestruct ("Heq1" with "Heq") as "?". *) *) *)
  (* (* (*   iApply "Heq1". *) *) *)

  (* (* (*  "Heq" : (λ (ρ : listVlC) (v : vlC), Next (Φ ρ v)) *) *) *)
  (* (* (*         ≡ (λ (ρ : listVlC) (v : vlC), Next (Ψ ρ v)) *) *) *)
  (* (* (*   iDestruct (ofe_fun_equivI with "Heq"). as "?". *) *) *)
  (* (* (*   by iDestruct (ofe_fun_equivI with "Heq") as "?". *) *) *)
  (* (* (* Qed. *) *) *)

  (* (* Lemma saved_envDG_agree `{savedPredG Σ A} γ Φ Ψ x y : *) *)
  (* (*   saved_envDG_own γ Φ -∗ saved_envDG_own γ Ψ -∗ ▷ (Φ x y ≡ Ψ x y). *) *)
  (* (* Proof. *) *)
  (* (*   unfold saved_envDG_own. iIntros "#HΦ #HΨ /=". *) *)
  (* (*   Import uPred. *) *)
  (* (*   iApply later_equivI. *) *)
  (* (*   Check @saved_anything_agree. *) *)
  (* (*   Eval hnf in (listVlC -c> vlC -c> ▶ iProp Σ)%CF. *) *)
  (* (*   iDestruct (saved_anything_agree (F := listVlC -c> vlC -c> ▶ ∙) with "HΦ HΨ") as "Heq". *) *)
  (* (*   Check @ofe_fun_equivI. *) *)
  (* (*   epose proof (@ofe_fun_equivI _ (listVlC) (λ _, vlC -n> laterC (iProp Σ)) (λne ρ, λne v, CofeMor Next (Φ ρ v)) (λ ρ, λne v, Next (Ψ ρ v))). *) *)
  (* (*   iDestruct (H0 with "Heq") as "?". *) *)

  (* (*  "Heq" : (λ (ρ : listVlC) (v : vlC), Next (Φ ρ v)) *) *)
  (* (*         ≡ (λ (ρ : listVlC) (v : vlC), Next (Ψ ρ v)) *) *)
  (* (*   iDestruct (ofe_fun_equivI with "Heq"). as "?". *) *)
  (* (*   by iDestruct (ofe_fun_equivI with "Heq") as "?". *) *)
  (* (* Qed. *) *)
End Sec.
