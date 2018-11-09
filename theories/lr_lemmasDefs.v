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
    Tho we need something about syntactic definitions as well.
  *)
  Lemma dtp_tmem_i T γ ρ ds σ:
    SP γ (⟦T⟧ ρ) -∗ ⟦Γ⟧* ρ -∗
    defs_interp (TTMem (dms_length ds) T T) ρ (dcons (dtysem σ γ) ds).
  Proof.
    iIntros "#Hv * #Hg /=".
    iExists (⟦T⟧ ρ), σ. iSplit.
    iExists γ; by iSplit.
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


  Lemma dtp_tmem_abs_i T L U γ ρ ds σ:
    SP γ (⟦T⟧ ρ) -∗ ⟦Γ⟧* ρ -∗
    (* I'd want to require these two hypotheses to hold later. *)
    Γ ⊨ L <: U -∗
    ▷ (Γ ⊨ T <: U) -∗
    ▷ (Γ ⊨ L <: T) -∗
    defs_interp (TTMem (dms_length ds) L U) ρ (dcons (dtysem σ γ) ds).
  Proof.
    iIntros "#Hv * #Hg #HLU #HTU #HLT /=".
    iExists (⟦T⟧ ρ), σ; iSplit.
    iExists γ; by iSplit.
    repeat iSplit; repeat iModIntro; iIntros "**";
      [iApply "HLT" | iApply "HTU" | iApply "HLU"]; done.
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
    - iDestruct "HT" as (φ  σ) "[Hγ ?]".
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

End Sec.
