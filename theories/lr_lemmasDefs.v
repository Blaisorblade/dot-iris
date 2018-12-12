From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.
From Dot Require Import tactics unary_lr synLemmas rules.

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
    iExists _; iSplit; try done. by iApply "Hv".
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
    γ ⤇ dot_interp T -∗ ⟦Γ⟧* ρ -∗
    def_interp (TTMem l T T) l ρ (dtysem ρ γ).
  Proof.
    iIntros "#Hv * #Hg /=".
    (* iExists _, _. iSplit. _auto. *)
    iSplit; try done.
    iExists (interp T), _. iSplit; first naive_solver.
    iModIntro; repeat iSplitL; auto.
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
    γ ⤇ dot_interp T -∗ ⟦Γ⟧* ρ -∗
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
    def_interp (TTMem l L U) l ρ (dtysem ρ γ).
  Proof.
    iIntros "#Hv * #Hg #HLU #HTU #HLT /=".
    iSplit; try done.
    iExists (interp T), _. iSplit; first auto.

    iModIntro; repeat iSplitL; iIntros "*";
      try (iIntros "**"; by [iApply "HTU" | iApply "HLU"]).
    (* iIntros "**". iApply ("HLT" with "Hg").  | iApply "HTU" | iApply "HLU"]. *)
    - iIntros "#HL".
      iSpecialize ("HLT" with "Hg").
      iDestruct ("HLT" with "HL") as "#HLT1"; auto.
  Qed.

  Lemma dtp_tand_i T U ρ d ds:
    defs_interp T ρ ds -∗
    def_interp U (length ds) ρ d -∗
    defs_interp (TAnd T U) ρ (cons d ds).
  Proof. naive_solver. Qed.

  (* Check that Löb induction works as expected for proving introduction of
   * objects. Using Löb induction works easily, but the scoping in the statement should be
   * checked (but might be okay now).
   * What I should prove is the following, and the correct statement
   * involves closing substitutions!
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
  Lemma wip_hard T ds ρ:
    let v0 := (vobj ds).[to_subst ρ] in
    defs_interp T (v0 :: ρ) (ds.|[to_subst (v0 :: ρ)]) ⊢
    interp T (v0 :: ρ) v0.
  Admitted.

  (* XXX Seems needed for idtp_new_i as stated, but the scoping seems all wrong.
   * Instead, we need to use closing substitutions in both sides of the lemma;
   * Still missing: use of closing substitutions in the term. TODO: follow examples.
   *)
  Lemma idstp_new_i T ds:
    idstp (TLater T :: Γ) T ds ⊢
    ietp Γ (TMu T) (tv (vobj ds)).
  Proof.
    iIntros "/= #Hds !> * #Hρ".
    change ((tv (vobj ds)).|[to_subst ρ]) with (tv (vobj ds).[to_subst ρ]).
    iApply wp_value.
    iLöb as "IH".
    (* set (v0 := (vobj ds).[to_subst ρ]). *)
    iApply wip_hard.
    iApply "Hds".
    auto.
  Qed.

  (* Lemma dtp_new_i T ds ρ: *)
  (*   defs_interp T (vobj ds :: ρ) ds *)
  (*   ⊢ *)
  (*   interp (TMu T) ρ (vobj ds). *)
  (* Proof. iIntros. simpl. iApply wip_hard. Qed. *)


    (*
  "Hds" : ⟦ Γ ⟧* ρ ∗ ▷ (uinterp T) (vobj ds :: ρ, vobj ds) -∗ (defs_uinterp T) (vobj ds :: ρ, ds)
  "Hρ" : ⟦ Γ ⟧* ρ
  --------------------------------------□
  (uinterp T) (vobj ds :: ρ, vobj ds)

    *)

  (* Still wrong. The correct statement will arise from the translation. *)
  Lemma idtp_tmem_i T γ l ρ1:
    γ ⤇ dot_interp T -∗
    idtp Γ (TTMem l T T) l (dtysem ρ1 γ).
  Proof.
    unfold idtp.
    iIntros "/= #Hγ !> **".
    iSplit; try done.
    iExists (interp T), _. iSplit; first auto.
    iModIntro; repeat iSplitL; iIntros "**".
  Abort.

End Sec.
