Require Import Dot.tactics.
Require Import Dot.unary_lr.

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
  Lemma idtp_vmem_i T v:
    ▷ ivtp Γ T v -∗
      idtp Γ (TVMem 0 T) [@ dvl v].
  Proof.
    iIntros "#Hv !> * #Hg /=".
    iExists v; iSplit.
    - repeat iPureIntro; done.
    - by iApply "Hv".
  Qed.

  (*
    What I'd want, if we store envD instead, is closer to:

    Lemma idtp_tmem_i T γ:
      SP γ ⟦T⟧ -∗
      idtp Γ (TTMem 0 T T) [@ dtysem γ].
    Tho we need something about syntactic definitions as well.
  *)
  Lemma dtp_tmem_i T γ ρ:
    SP γ (⟦T⟧ ρ) -∗ ⟦Γ⟧* ρ -∗
    defs_interp (TTMem 0 T T) ρ [@ dtysem γ].
  Proof.
    iIntros "#Hv * #Hg /=".
    iExists (⟦T⟧ ρ); iSplit.
    iExists γ; by iSplit.
    iSplit; by iIntros "!> **".
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


  Lemma dtp_tmem_abs_i T L U γ ρ:
    SP γ (⟦T⟧ ρ) -∗ ⟦Γ⟧* ρ -∗
    (* I'd want to require these two hypotheses to hold later. *)
    Γ ⊨ T <: U -∗
    Γ ⊨ L <: T -∗
    defs_interp (TTMem 0 L U) ρ [@ dtysem γ].
  Proof.
    iIntros "#Hv * #Hg #HTU #HLT /=".
    iExists (⟦T⟧ ρ); iSplit.
    iExists γ; by iSplit.
    iSplit; iIntros "!> **"; [iApply "HLT" | iApply "HTU"]; done.
  Qed.

End Sec.
