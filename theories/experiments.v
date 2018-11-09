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
      | dtysem γ =>
        _
        (* dtysem γ *)
    end.
  Next Obligation.
    iIntros "** !>".
    iDestruct (alloc_sp T []) as ">Hγ".
    iDestruct "Hγ" as(γ) "Hsp".
    by iExists (dtysem γ).
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

  Lemma alloc_dtp_tmem_i T ρ:
    ⟦Γ⟧* ρ -∗
    (|==> ∃ γ, defs_interp (TTMem 0 T T) ρ [@ dtysem γ])%I.
  Proof.
    iIntros "#Hg /=".
    iDestruct (alloc_sp T ρ) as "HupdSp".
    iMod "HupdSp" as (γ) "#Hsp".
    iModIntro; iExists γ, (⟦T⟧ρ); iSplit.
    - iExists γ; by iSplit.
    - iSplit; by iIntros "!> **".
  Qed.
  (* Print saved_pred_own. *)
  (* Print Next. *)
  (* Print savedPredG. *)
  (* Eval cbn in (∀ A, savedAnythingG Σ (A -c> ▶ ∙)). *)
  (* Check savedAnythingG. *)
  (* From iris Require Import algebra.ofe. *)
  (* Check savedEnvD. *)
  (* Alternative to savedPredG *)
  Canonical Structure listVlC := leibnizC (list vl).
  Definition savedEnvDG := (savedAnythingG Σ (listVlC -n> vlC -c> ▶ ∙)%CF).
End Sec.
