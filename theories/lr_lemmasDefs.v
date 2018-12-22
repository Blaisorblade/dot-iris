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

  Lemma def_interp_to_interp T d ds ρ s:
    let v0 := (vobj (d :: ds)).[s] in
    def_interp T (length ds) ρ (d.|[v0 .: s]) ⊢
    interp T ρ v0.
  Proof.
    induction T; simpl; iIntros "H"; trivial;
      asimpl; set (d' := d.|[up s]); set (ds' := ds.|[up s]);
      iDestruct "H" as "[% #H]";
      move: H => Hlen; rewrite <- Hlen.

    - iDestruct "H" as (vmem) "[#H1 #H2]".
      iExists (d'.|[vobj (d' :: ds')/]). iSplit.
      + iPureIntro.
        assert (length ds = length ds') as ->. by rewrite /ds' /hsubst map_length.
          by apply obj_lookup_cons.
      + iExists _; iSplit; trivial.
        subst d'. by asimpl.
    -
      iDestruct "H" as (φ σ) "[#Hl [#? [#? #?]]]".
      iDestruct "Hl" as (γ) "[% #Hγ]". move: H => Hl.
      iExists (d'.|[vobj (d' :: ds')/]); iSplit.
      + iPureIntro.
        assert (length ds = length ds') as ->. by rewrite /ds' /hsubst map_length.
        apply obj_lookup_cons.
      + iExists φ, σ; iSplit; trivial.
        * iExists γ.
          subst d'. asimpl.
          auto.
        * iModIntro. repeat iSplitL; naive_solver.
  Qed.

  (* Check that Löb induction works as expected for proving introduction of
   * objects. Using Löb induction works easily.
   *
   * Γ, x: ▷ T ⊨ ds : T
   * ---------------------
   * Γ ⊨ nu x. ds : μ x. T
   *)
  (* Formerly wip_hard. *)
  Lemma defs_interp_to_interp T ds ρ s:
    let v0 := (vobj ds).[s] in
    defs_interp T ρ (ds.|[v0 .: s]) ⊢
    interp T ρ v0.
  Proof.
    induction ds; asimpl; iIntros "H".
    - destruct T; simpl; trivial.
    - simpl in IHds.
      destruct T; trivial.
      Fail iApply dtp_tand_i.
      Fail iApply IHds.
      Restart.
    
    revert ds.
    induction T; simpl; iIntros (ds) "H"; trivial.
    destruct ds; simpl; first done. rewrite map_length.
    iDestruct "H" as "[#H1 #H2]".
    iSplit.
    2: {
      iApply (def_interp_to_interp T2 d ds ρ s).
      iApply "H2".
    }
    - asimpl.
      iApply (IHT1 (d :: ds)).
      iAssert (⟦ T1 ⟧ ρ (vobj (ds.|[up s]))) as "H3".

      (* iApply (IHT1 (d :: ds)). *)
      (* set (d' := d.|[up (to_subst ρ)]). *)
      (* set (ds' := ds.|[up (to_subst ρ)]). *)
      (* change (ds.|[up (to_subst ρ)]) with ds'. *)

    (* simpl. *)
    (* induction T; rewrite /defs_interp => //=; fold defs_interp; *)
    (* try solve [iIntros; try done]. *)
  Admitted.

  Lemma T_New_I T ds:
     (TLater T :: Γ ⊨ds ds : T →
     Γ ⊨ tv (vobj ds) : TMu T)%I.
  Proof.
    iIntros "/= #Hds !> * #Hρ".
    iApply wp_value.
    iLöb as "IH".
    iApply defs_interp_to_interp.
    iPoseProof ("Hds" $! (vobj ds.|[up (to_subst ρ)] :: ρ)) as "H".
    asimpl.
    iApply "H"; by iSplit.
  Qed.

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
