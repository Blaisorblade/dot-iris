Require Import Dot.tactics.
Require Import Dot.unary_lr.
Require Import Dot.synLemmas.

Section Sec.
  Context `{HdotG: dotG Σ}.

  Context (Γ: list ty).
  Implicit Types T: ty.

  (**
     Lemmas about definition typing.
     TODO: generalize them for definitions at arbitrary positions.

     This should be easier now, since we made labels index
     definitions from the end, as done by existing formalizations.
     This way, [dcons d ds] keeps the existing labels for [ds] and uses a new
     one ([length ds]) for [d]. That's a bit like de Bruijn levels.
   *)
  Lemma idtp_vmem_i T v ds:
    ▷ ivtp Γ T v -∗
      idtp Γ (TVMem (dms_length ds) T) (dcons (dvl v) ds).
  Proof.
    iIntros "#Hv !> * #Hg /=".
    iExists v; iSplit.
    - by [].
    - by iApply "Hv".
  Qed.

  (*
    What I'd want, if we store envD instead, is closer to:

    Lemma idtp_tmem_i T γ:
      SP γ ⟦T⟧ -∗
      idtp Γ (TTMem 0 T T) [@ dtysem γ].
    Tho we need something about syntactic definitions as well (or not??)

    TODO: prove what I actually want, now that we store envD.
  *)
  Lemma dtp_tmem_i T γ ρ ds:
    γ ⤇  uinterp T -∗ ⟦Γ⟧* ρ -∗
    defs_interp (TTMem (dms_length ds) T T) ρ (dcons (dtysem (idsσ ρ) γ) ds).
  Proof.
    iIntros "#Hv * #Hg /=".
    (* iExists _, _. iSplit. _auto. *)
    iExists (uinterp T), _. iSplit; first auto.
    rewrite <- idsσ_is_id.
    repeat iSplit; repeat iModIntro; by iIntros "**".
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


  Lemma dtp_tmem_abs_i T L U γ ρ ds:
    SP γ (uinterp T) -∗ ⟦Γ⟧* ρ -∗
    Γ ⊨ L <: U -∗
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
    (Γ ⊨ TLater T <: TLater U) -∗
    (Γ ⊨ TLater L <: TLater T) →
    defs_interp (TTMem (dms_length ds) L U) ρ (dcons (dtysem (idsσ ρ) γ) ds).
  Proof.
    iIntros "#Hv * #Hg #HLU #HTU #HLT /=".
    iExists (uinterp T), _. iSplit; first auto.
    rewrite <- idsσ_is_id.
    repeat iSplit;
      iIntros "!> **"; [iApply "HLT" | iApply "HTU" | iApply "HLU"]; done.
  Qed.

  Lemma dtp_add_defs T ρ d ds:
    defs_interp T ρ ds -∗
    defs_interp T ρ (dcons d ds).
  Proof.
    iInduction T as [] "IH".
    all: iIntros "#HT /="; try done.
    - iDestruct "HT" as "[? ?]". iSplit.
      + by iApply "IH".
      + by iApply "IH1".
    - iDestruct "HT" as (vmem) "[% ?]".
      iExists vmem; iSplit; try done.
      by erewrite index_dms_extend.
    - iDestruct "HT" as (φ σ) "[Hγ ?]".
      iDestruct "Hγ" as (γ) "[% HSP]".
      erewrite index_dms_extend; eauto 6.
  Qed.

  Lemma dtp_tand_i T U ρ d ds:
    defs_interp T ρ ds -∗
    defs_interp U ρ (dcons d ds) -∗
    defs_interp (TAnd T U) ρ (dcons d ds).
  Proof.
    iIntros "#HT #HU /=".
    iSplit; last done.
    by iApply dtp_add_defs.
  Qed.

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

  Lemma idtp_new_i T ds:
    idtp (TLater T :: Γ) T ds ⊢
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

  Lemma idtp_tmem_i T γ ds ρ1:
    γ ⤇ (uinterp T) -∗
    idtp Γ (TTMem (dms_length ds) T T) (dcons (dtysem (idsσ ρ1) γ) ds).
  Proof.
    unfold idtp.
    iIntros "/= #Hγ !> **".
  Abort.

End Sec.
