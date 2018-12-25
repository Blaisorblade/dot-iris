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
  (* TODO: switch to ietp. Might involve challenges with fancy updates;
     worst-case, we can add a fancy update to definition typing. *)
  Lemma idtp_vmem_i T v l:
    ivtp Γ (TLater T) v -∗
    Γ ⊨d { l = dvl v } : TVMem l T.
  Proof.
    iIntros "#[% #Hv]". move: H => Hclv. iSplit; auto using fv_dvl. iIntros "!> * #Hg".
    iPoseProof (interp_env_ρ_closed with "Hg") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in *.
    repeat iSplit => //. { iPureIntro. apply fv_to_subst, Hclρ. apply fv_dvl, Hclv. }
    iExists _; iSplit; try done.
    simpl. iDestruct ("Hv" with "Hg") as "[% Hv▷T]". iExact "Hv▷T".
  Qed.

  Lemma interp_env_ρ_fv ρ: ⟦ Γ ⟧* ρ -∗ ⌜ nclosed ρ 0 ⌝.
  Proof.
    iIntros "Hg".
    iPoseProof (interp_env_ρ_closed with "Hg") as "%".
    iPureIntro. by apply cl_ρ_fv.
  Qed.

  (* Lemma dtp_tmem_i T γ ρ l : *)
  (*   γ ⤇ dot_interp T -∗ ⟦Γ⟧* ρ -∗ *)
  (*   def_interp (TTMem l T T) l ρ (dtysem ρ γ). *)
  (* Proof. *)
  (*   iIntros "#Hv * #Hg /=". *)
  (*   (* iExists _, _. iSplit. _auto. *) *)
  (*   iPoseProof (interp_env_ρ_fv with "Hg") as "%". move: H => Hclρ. *)
  (*   repeat iSplit => //. eauto using fv_dtysem. *)
  (*   iExists (interp T), _. iSplit; first naive_solver. *)
  (*   iModIntro; repeat iSplitL; auto. *)
  (* Qed. *)

  (* XXX: the PDF indexes definition typing. *)
  Lemma idtp_tmem_abs_i T L U γ l :
    Γ ⊨ [L, 0] <: [U, 0] -∗
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
    Γ ⊨ [T, 1] <: [U, 1] -∗
    Γ ⊨ [L, 1] <: [T, 1] -∗
    γ ⤇ dot_interp T -∗
    Γ ⊨d { l = dtysem (idsσ (length Γ)) γ } : TTMem l L U.
  Proof.
    iIntros " #HLU #HTU #HLT #Hγ /=".
    iSplit. by auto using fv_dtysem, fv_idsσ.
    iIntros "!>" (ρ) "#Hg".
    iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in *.
    setoid_rewrite (subst_sigma_idsσ ρ (length ρ) eq_refl).
    iPoseProof (interp_env_ρ_fv with "Hg") as "%". move: H => Hfvρ.
    repeat iSplit => //. by eauto using fv_dtysem.
    iExists (interp T), _.
    iSplit; first auto.
    iModIntro; repeat iSplitL; iIntros "*".
    - iIntros (Hclv) "#HL".
      iSpecialize ("HLT" $! ρ v Hclv with "Hg").
      iDestruct ("HLT" with "HL") as "#HLT1". by iNext.
    - iIntros; iApply "HTU" => //; iNext => //.
    - iIntros; iApply "HLU" => //; iApply interp_v_closed => //.
  Qed.

  (* Lemma idtp_tmem_i T γ l: *)
  (*   γ ⤇ dot_interp T -∗ *)
  (*   Γ ⊨d { l = dtysem (idsσ (length Γ)) γ } : TTMem l T T. *)
  (* Proof. *)
  (*   iIntros " #Hγ /=". *)
  (*   iSplit. by auto using fv_dtysem, fv_idsσ. *)
  (*   iIntros "!>" (ρ) "#Hg". *)

  (*   iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in *. *)
  (*   setoid_rewrite (subst_sigma_idsσ ρ (length ρ) eq_refl). *)
  (*   iPoseProof (interp_env_ρ_fv with "Hg") as "%". move: H => Hfvρ. *)
  (*   repeat iSplit => //. by eauto using fv_dtysem. *)
  (*   iExists (interp T), _. iSplit; first auto. *)
  (*   iModIntro; repeat iSplitL; auto. *)
  (* Qed. *)

  Lemma idtp_tmem_i T γ l:
    γ ⤇ dot_interp T -∗
    Γ ⊨d { l = dtysem (idsσ (length Γ)) γ } : TTMem l T T.
  Proof.
    iIntros " #Hγ".
    iApply (idtp_tmem_abs_i T T T) => //=;
      (* XXX Inline copy of Sub_Refl: *)
      by iIntros "!> **".
  Qed.

  Lemma dtp_tand_i T U ρ d ds:
    defs_interp T ρ ds -∗
    def_interp U (length ds) ρ d -∗
    defs_interp (TAnd T U) ρ (cons d ds).
  Proof. naive_solver. Qed.

  Lemma def_interp_to_interp T d ds ρ s:
    let v0 := (vobj (d :: ds)).[s] in
    nclosed_vl v0 0 →
    def_interp T (length ds) ρ (d.|[v0 .: s]) ⊢
    interp T ρ v0.
  Proof.
    intros * Hfvv0. asimpl.
    set (d' := d.|[up s]); set (ds' := ds.|[up s]).
    assert (nclosed_vl (vobj (d' :: ds')) 0) as Hfv'. {
      revert v0 Hfvv0.
      asimpl.
      by subst d' ds'.
    }
    assert (length ds = length ds') as Hlen'. by rewrite /ds' /hsubst map_length.
    assert (vobj (d' :: ds') @ length ds ↘ d'.|[vobj (d' :: ds')/]) as Hlookup.
      by rewrite Hlen'; apply obj_lookup_cons.
    induction T => //=; try (by iIntros "**").
    all: iIntros "[% [% #H]]"; move: H H0 => Hlen Hfvd; rewrite <- Hlen.
    - iDestruct "H" as (vmem) "[#H1 #H2]".
      iSplit => //.
      iExists (d'.|[vobj (d' :: ds')/]). iSplit => //.
      subst d'. asimpl.
      iSplit => //. iExists _. iSplit => //.
    - iDestruct "H" as (φ σ) "[#Hl [#? [#? #?]]]".
      iDestruct "Hl" as (γ) "[% #Hγ]". move: H => Hl.
      iSplit => //.
      iExists (d'.|[vobj (d' :: ds')/]). iSplit => //.
      subst d'; asimpl.
      iSplit => //. iExists φ, σ; iSplit => //.
      * iExists γ; iSplit => //.
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
    nclosed_vl v0 0 →
    defs_interp T ρ (ds.|[v0 .: s]) ⊢
    interp T ρ v0.
  Proof.
    induction ds; asimpl; iIntros (Hcl) "H".
    - destruct T => //=.
    - simpl in IHds.
      destruct T => //=.
      Fail iApply dtp_tand_i.
      Fail iApply IHds.
      Restart.

    simpl; iIntros (Hcl) "#H".
    iPoseProof (defs_interp_v_closed with "H") as "%". move: H => Hclds.
    iInduction T as [] "IHT" forall (ds Hcl Hclds) => //.
    destruct ds => //=. rewrite map_length.
    iDestruct "H" as "[#H1 #H2]".
    iSplit.
    2: { by iApply (def_interp_to_interp T2 d ds ρ s). }
    - asimpl.
      iAssert (⟦ T1 ⟧ ρ (vobj (ds.|[up s]))) as "#H3". {
        iApply ("IHT" $! ds) => //.
        admit.
        admit.
        asimpl.
        Fail iApply "H1".
        admit.
      }
      (* We could probably go from H3 to the thesis... *)
      iApply ("IHT" $! (d :: ds)) => //.
      admit.

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
    iIntros "/= #[% Hds]". move: H => Hclds. iSplit; auto using fv_tv, fv_vobj. iIntros " !> * #Hρ /=".
    iApply wp_value.
    iPoseProof (interp_env_ρ_closed with "Hρ") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "Hρ") as "%". move: H => Hlen. rewrite <- Hlen in *.
    assert (nclosed_vl (vobj ds).[to_subst ρ] 0) as Hclvds. {
      eapply (fv_to_subst_vl' (vobj ds)) => //. by apply fv_vobj.
    }

    iLöb as "IH".
    iApply defs_interp_to_interp. exact Hclvds.
    iPoseProof ("Hds" $! (vobj ds.|[up (to_subst ρ)] :: ρ)) as "#H".
    asimpl. iApply "H". repeat iSplit => //.
  Qed.

End Sec.
