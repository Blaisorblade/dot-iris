Require Import Dot.tactics.
Require Import Dot.unary_lr.
Require Import Dot.synLemmas.
(* Workflow: Use this file for new experiments, and move experiments here in appropriate files once they're done. *)

Section Sec.
  Context `{HdotG: dotG Σ}.

  Context (Γ: list ty).
  Implicit Types T: ty.

  (* Locate "|==>". *)
  (* Check @bupd. *)
  (* Print BUpd. *)
  (* SearchAbout BUpd. *)
  (* SearchAbout BiBUpd. *)

  (* Print SP. *)
  (* Check ⊤%I. *)

  (* Program Definition wtovdm (dw: dm): (|==> ∃(dv: gname), True)%I := *)

  Lemma alloc_sp T ρ:
    (|==> ∃ γ, SP γ (⟦T⟧ ρ))%I.
  Proof. by apply saved_pred_alloc. Qed.

  Program Fixpoint wtovdm (dw: dm):
    (|==> ∃(dv: dm), (True%I: iProp Σ))%I :=
    (* (|==> )%I := *)
    match dw with
      | dtysyn T => _
      | dvl w =>
        _
        (* dvl w (* XXX *) *)
      | dtysem γ σ =>
        _
        (* dtysem γ *)
    end.
  Next Obligation.
    iIntros "** !>".
    iDestruct (alloc_sp T []) as ">Hγ".
    iDestruct "Hγ" as (γ) "Hsp".
    by iExists (dtysem _ γ).
    Grab Existential Variables.
    constructor.
  Defined.
  Next Obligation.
    iIntros "** !>".
    by iExists dw.
  Defined.
  Next Obligation.
    iIntros "** !>".
    by iExists dw.
  Defined.

  (* Program Definition wtov (w: val): val := *)
  (*   match w with *)
  (*     |  *)

  Lemma alloc_dtp_tmem_i T ρ σ:
    ⟦Γ⟧* ρ -∗
    (|==> ∃ γ, defs_interp (TTMem 0 T T) ρ [@ dtysem σ γ])%I.
  Proof.
    iIntros "#Hg /=".
    iDestruct (alloc_sp T ρ) as "HupdSp".
    iMod "HupdSp" as (γ) "#Hsp".
    iModIntro; iExists γ, (⟦T⟧ρ), σ; iSplit.
    - iExists γ; by iSplit.
    - repeat iSplit; repeat iModIntro; by iIntros "**".
  Qed.
  (* Print saved_pred_own. *)
  (* Print Next. *)
  (* Print savedPredG. *)
  (* Eval cbn in (∀ A, savedAnythingG Σ (A -c> ▶ ∙)). *)
  (* Check savedAnythingG. *)
  (* From iris Require Import algebra.ofe. *)
  (* Check savedEnvD. *)
  (* Alternative to savedPredG *)
  Notation savedEnvDG := (savedAnythingG Σ (listVlC -c> vlC -c> ▶ ∙)%CF).
  Notation savedEnvDΣ := (savedAnythingΣ (listVlC -c> vlC -c> ▶ ∙)).

  (* Notation savedEnvDG := (savedAnythingG Σ (listVlC -c> vlC -c> ▶ ∙)). *)
  (* Notation savedEnvDΣ := (savedAnythingΣ (listVlC -c> vlC -c> ▶ ∙)). *)
  (* Print saved_anything_own. *)
  (* Print savedAnythingG. *)
  (* Print cFunctor. *)
  Print savedPredG.
  Print saved_pred_own.

  Print saved_anything_own.
  Context `{savedEnvDG}.
  Program Definition saved_envDG_own (γ : gname) (Φ : listVlC -n> vlC -n> iProp Σ): iProp Σ :=
    saved_anything_own (F := listVlC -c> vlC -c> ▶ ∙) γ (λ ρ, λne v, Next (Φ ρ v)).

  Instance saved_envDG_own_contractive γ:
    Contractive
                (saved_envDG_own γ: (listVlC -n> vlC -n> iProp Σ) → iProp Σ).
  Proof.
    solve_proper_core ltac:(fun _ =>
                    first [ intros ? ?; progress simpl | by auto | f_contractive | f_equiv ]).

    (* solve_proper_prepare. *)

    (* repeat first [eassumption | first [ intros ? ?; progress simpl | by auto | f_contractive | f_equiv ]]. *)
    (* cbn in H0. *)
    (* solve [apply H0]. *)
    (* Restart. *)
    (* (* Summarizes to: *) *)
    (* solve_proper_core ltac:(fun _ => *)
    (*                 first [ intros ? ?; progress simpl | by auto | f_contractive | f_equiv | apply H0 ]). *)
    (* (* But that is really fragile.*) *)
  Qed.

  Lemma saved_envDG_alloc_strong (G : gset gname) (Φ : listVlC -n> vlC -n> iProp Σ) :
    (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ saved_envDG_own γ Φ)%I.
  Proof. iApply saved_anything_alloc_strong. Qed.

  Lemma saved_envDG_alloc (Φ : listVlC -n> vlC -n> iProp Σ) :
    (|==> ∃ γ, saved_envDG_own γ Φ)%I.
  Proof. iApply saved_anything_alloc. Qed.

  (* We put the `x` on the outside to make this lemma easier to apply. *)
  Lemma saved_envDG_agree1 `{savedPredG Σ A} γ Φ Ψ x :
    saved_envDG_own γ Φ -∗ saved_envDG_own γ Ψ -∗ ▷ (Φ x ≡ Ψ x).
    unfold saved_envDG_own. iIntros "#HΦ #HΨ".
    Import uPred.
    iApply later_equivI.
    Check @saved_anything_agree.
    Eval hnf in (listVlC -c> vlC -c> ▶ iProp Σ)%CF.
    iDestruct (saved_anything_agree (F := listVlC -c> vlC -c> ▶ ∙) with "HΦ HΨ") as "Heq".
    simpl.

    Check @ofe_fun_equivI.
    iDestruct (@ofe_fun_equivI _ (listVlC) (λ _, vlC -n> laterC (iProp Σ)) (λ ρ, λne v, Next (Φ ρ v)) (λ ρ, λne v, Next (Ψ ρ v))) as "[Heq1 _]".
    Fail iSpecialize ("Heq1" with "Heq").
    Abort.
  (* (*   by iDestruct ("Heq1" with "Heq") as "?". *) *)

  (* (*   simpl. *) *)
  (* (*   Unset Printing Notations. *) *)
  (* (*   Set Printing Implicit. *) *)
  (* (*   simpl in *. *) *)
  (* (*   iDestruct ("Heq1" with "Heq") as "?". *) *)
  (* (*   iApply "Heq1". *) *)

  (* (*  "Heq" : (λ (ρ : listVlC) (v : vlC), Next (Φ ρ v)) *) *)
  (* (*         ≡ (λ (ρ : listVlC) (v : vlC), Next (Ψ ρ v)) *) *)
  (* (*   iDestruct (ofe_fun_equivI with "Heq"). as "?". *) *)
  (* (*   by iDestruct (ofe_fun_equivI with "Heq") as "?". *) *)
  (* (* Qed. *) *)

  (* Lemma saved_envDG_agree `{savedPredG Σ A} γ Φ Ψ x y : *)
  (*   saved_envDG_own γ Φ -∗ saved_envDG_own γ Ψ -∗ ▷ (Φ x y ≡ Ψ x y). *)
  (* Proof. *)
  (*   unfold saved_envDG_own. iIntros "#HΦ #HΨ /=". *)
  (*   Import uPred. *)
  (*   iApply later_equivI. *)
  (*   Check @saved_anything_agree. *)
  (*   Eval hnf in (listVlC -c> vlC -c> ▶ iProp Σ)%CF. *)
  (*   iDestruct (saved_anything_agree (F := listVlC -c> vlC -c> ▶ ∙) with "HΦ HΨ") as "Heq". *)
  (*   Check @ofe_fun_equivI. *)
  (*   epose proof (@ofe_fun_equivI _ (listVlC) (λ _, vlC -n> laterC (iProp Σ)) (λne ρ, λne v, CofeMor Next (Φ ρ v)) (λ ρ, λne v, Next (Ψ ρ v))). *)
  (*   iDestruct (H0 with "Heq") as "?". *)

  (*  "Heq" : (λ (ρ : listVlC) (v : vlC), Next (Φ ρ v)) *)
  (*         ≡ (λ (ρ : listVlC) (v : vlC), Next (Ψ ρ v)) *)
  (*   iDestruct (ofe_fun_equivI with "Heq"). as "?". *)
  (*   by iDestruct (ofe_fun_equivI with "Heq") as "?". *)
  (* Qed. *)
End Sec.
