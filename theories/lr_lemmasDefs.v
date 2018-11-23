Require Import Dot.tactics.
Require Import Dot.unary_lr.
Require Import Dot.synLemmas.

Section Sec.
  Context `{HdotG: dotG Σ}.

  Context (Γ: list ty).
  Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

  (**
     Lemmas about definition typing.
     TODO: generalize them for definitions at arbitrary positions.

     This should be easier now, since we made labels index
     definitions from the end, as done by existing formalizations.
     This way, [dcons d ds] keeps the existing labels for [ds] and uses a new
     one ([length ds]) for [d]. That's a bit like de Bruijn levels.
   *)
  Lemma idtp_vmem_i T v l:
    ▷ ivtp Γ T v -∗
      idtp Γ (TVMem l T) l (dvl v).
  Proof.
    iIntros "#Hv !> * #Hg /=".
    iSplit; try done.
    iExists v; iSplit; try done. by iApply "Hv".
  Qed.

  (*
    What I'd want, if we store envD instead, is closer to:

    Lemma idtp_tmem_i T γ:
      SP γ ⟦T⟧ -∗
      idtp Γ (TTMem 0 T T) [@ dtysem γ].
    Tho we need something about syntactic definitions as well (or not??)

    TODO: prove what I actually want, now that we store envD.
  *)
  Lemma dtp_tmem_i T γ ρ l :
    γ ⤇ uinterp T -∗ ⟦Γ⟧* ρ -∗
    def_interp (TTMem l T T) l ρ (dtysem (idsσ ρ) γ).
  Proof.
    iIntros "#Hv * #Hg /=".
    (* iExists _, _. iSplit. _auto. *)
    iSplit; try done.
    iExists (uinterp T), _. iSplit; first naive_solver.
    rewrite <- idsσ_is_id.
    auto 8.
  Qed.

  (* We can't write idtp_tmem_i as above, but for now we can write: *)
  (* Lemma idtp_tmem_i T γ ρ: *)
  (*   SP γ (⟦T⟧ ρ) -∗ *)
  (*      idtp Γ (TTMem 0 T T) [@ dtysem γ]. *)
  (* Proof. *)
  (*   iIntros "#Hv !> * #Hg /=". *)
  (*   iExists (⟦T⟧ ρ); iSplit. *)
  (*   iExists γ; by iSplit. *)
  (*   iSplit; iIntros "!> **". *)
  (* Aborted. *)


  Lemma dtp_tmem_abs_i T L U γ ρ l :
    SP γ (uinterp T) -∗ ⟦Γ⟧* ρ -∗
    Γ ⊨> L <: U -∗
    (* We want the next two hypotheses to hold in a later world, but for this Γ,
       both because that's what we need to introduce, and because it allows
       using Γ *now* to establish the assumption.

       How do we represent subtyping in a later world? We have two distinct
       choices, because in Iris ▷(P ⇒ Q) ⊢ ▷ P ⇒ ▷ Q but not viceversa
       (unlike with raw step-indexing).
       In turn, that's because to show ▷ P ⇒ ▷ Q we can assume resources are
       valid one step earlier, unlike for ▷(P ⇒ Q).

       It seems easier, in subtyping judgment, to just delay individual types
       via (Γ ⊨ TLater T <: TLater U), that is

       (□∀ v ρ, ⟦Γ⟧* ρ → ▷ ⟦T1⟧ ρ v → ▷ ⟦T2⟧ ρ v),

       instead of instead of introducing some notation to write

       (□∀ v ρ, ⟦Γ⟧* ρ → ▷ (⟦T1⟧ ρ v → ⟦T2⟧ ρ v)).

       And that forces using the same implication in the logical relation
       (unlike I did originally). *)
    (Γ ⊨> TLater T <: TLater U) -∗
    (Γ ⊨> TLater L <: TLater T) →
    def_interp (TTMem l L U) l ρ (dtysem (idsσ ρ) γ).
  Proof.
    iIntros "#Hv * #Hg #HLU #HTU #HLT /=".
    iSplit; try done.
    iExists (uinterp T), _. iSplit; first auto.
    rewrite <- idsσ_is_id.

    repeat iSplit; iIntros "!> *".
    - iIntros "#HL".
      iSpecialize ("HLT" with "Hg").
      iDestruct ("HLT" with "HL") as ">#HLT1". by repeat iModIntro.
    - iIntros "#HT". by iApply "HTU"; last naive_solver.
    - iIntros "#HL". by iApply "HLU"; last naive_solver.
  Qed.

  (*     iSpecialize ("HTU" with "Hg"). *)
  (*     iApply "HTU". *)
  (*     iNext. *)
  (*     info_eauto using later_persistently_1. *)
      
  (*     iDestruct (later_persistently_1 with "HT") as "#HT'". *)
  (*     (* Require Import iris.base_logic.upred. *) *)
  (*     (* (* Import uPred_primitive. *) *) *)
  (*     (* rewrite bi.later_persistently. in "HT". *) *)
  (*     (* iRewrite bi.later_persistently. in "HT". *) *)
  (*     (* iPoseProof (bi.later_persistently with "HT") as "?". *) *)
  (*     (* Search (▷ (□ _) ⊢ □ (▷ _))%I. *) *)
  (*     (* iMod "HT". *) *)

  (*     done. *)
  (*     iDestruct ("HTU" with "HT'") as "HTU1". by repeat iModIntro. *)
  (*   iApply "HLT". *)
  (*   Check persistent. *)
  (*   Check (persistent (interp_persistent _ _ _)). *)
  (*   iApply "HLT". *)
  (*   naive_solver. [iApply "HLT" | iApply "HTU" | iApply "HLU"]; done. *)
  (* Qed. *)

  Lemma dtp_tand_i T U ρ d ds:
    defs_interp T ρ ds -∗
    def_interp U (dms_length ds) ρ d -∗
    defs_interp (TAnd T U) ρ (dcons d ds).
  Proof. naive_solver. Qed.

  (* Check that Löb induction works as expected for proving introduction of
   * objects. That part is trivial, but the scoping in the statement is all wrong.
   * What I should prove instead is the following, and the correct statement involves closing substitutions!
   *
   * Γ, x: ▷ T ⊨ ds : T
   * ---------------------
   * Γ ⊨ nu x. ds : μ x. T
   *
   * It also seems this would be easier to prove if TMu *weakened* the value;
   * the current definition is OK for closed v, but we never make that explicit
   * and Autosubst doesn't seem to happy to talk about closed terms.
   *
    Program Definition interp_mu (interp : envD) : envD := uncurryD (λne ρ, λne v,
      (curryD interp (v::ρ) v.[up (ren var_vl)])) % I.
   *)
  (* XXX Seems needed for idtp_new_i as stated, but the scoping seems all wrong.
   * Instead, we need to use closing substitutions in both sides of the lemma;
   * Still missing: use of closing substitutions in the term. TODO: follow examples.
   *)
  Lemma wip_hard T ds ρ:
    defs_uinterp T (vobj ds :: ρ, ds) ⊢
    uinterp T (vobj ds :: ρ, vobj ds).
  Admitted.
  Lemma dtp_new_i T ds ρ:
    defs_interp T (vobj ds :: ρ) ds
    ⊢
    interp (TMu T) ρ (vobj ds).
  Proof. by iApply wip_hard. Qed.

  Lemma idstp_new_i T ds:
    idstp (TLater T :: Γ) T ds ⊢
    ivtp Γ (TMu T) (vobj ds).
  Proof.
    iIntros "/= #Hds !> * #Hρ".
    iLöb as "IH".
    iApply wip_hard. by iApply "Hds"; auto.
  Qed.

    (*
  "Hds" : ⟦ Γ ⟧* ρ ∗ ▷ (uinterp T) (vobj ds :: ρ, vobj ds) -∗ (defs_uinterp T) (vobj ds :: ρ, ds)
  "Hρ" : ⟦ Γ ⟧* ρ
  --------------------------------------□
  (uinterp T) (vobj ds :: ρ, vobj ds)

    *)

  (* Still wrong. The correct statement will arise from the translation. *)
  Lemma idtp_tmem_i T γ l ρ1:
    γ ⤇ uinterp T -∗
    idtp Γ (TTMem l T T) l (dtysem (idsσ ρ1) γ).
  Proof.
    unfold idtp.
    iIntros "/= #Hγ !> **".
    iSplit; try done.
    iExists (uinterp T), _. iSplit; first naive_solver.
  Abort.

End Sec.
