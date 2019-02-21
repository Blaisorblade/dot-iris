From iris.proofmode Require Import tactics.
From D Require Import tactics.
From D.Dot Require Import unary_lr_binding rules.

Section Sec.
  Context `{HdotG: dotG Σ}.

  Context (Γ: list ty).
  Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

  (** Lemmas about definition typing. *)
  (* TODO: replace [TLater V :: Γ ⊨d dvl v : TVMem l T] by
    [Γ | V ⊨d dvl v : TVMem l T]. *)
  Lemma idtp_vmem_i V T v l:
    V :: Γ ⊨ tv v : T -∗
    TLater V :: Γ ⊨d dvl v : TVMem l T.
  Proof.
    iIntros "/= #[% #Hv]". move: H => Hclv. apply fv_tv_inv in Hclv.
    iSplit. by auto using fv_dvl.
    iIntros "!> *". destruct ρ as [|w ρ]; first by iIntros.
    iIntros "[#Hg [% #Hw]]". move: H => Hclw.
    iPoseProof (interp_env_ρ_closed with "Hg") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in *.
    repeat iSplit => //. { iPureIntro; apply fv_dvl, fv_to_subst_vl => //=; auto. }
    iExists _; iSplit => //.
    iNext. iApply wp_value_inv'; iApply "Hv"; by iSplit.
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
    Γ ⊨d dtysem (idsσ (length Γ)) γ : TTMem l L U.
  Proof.
    iIntros " #HLU #HTU #HLT #Hγ /=".
    iSplit. by auto using fv_dtysem, fv_idsσ.
    iIntros "!>" (ρ) "#Hg".
    iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in *.
    setoid_rewrite (subst_sigma_idsσ ρ (length ρ) eq_refl).
    iPoseProof (interp_env_ρ_fv with "Hg") as "%". move: H => Hfvρ.
    repeat iSplit => //. by eauto using fv_dtysem.
    iExists (interp T ρ).
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
    Γ ⊨d dtysem (idsσ (length Γ)) γ : TTMem l T T.
  Proof.
    iIntros " #Hγ".
    iApply (idtp_tmem_abs_i T T T) => //=;
      by iIntros "!> **".
  Qed.

  (* Lemma dtp_tand_i T U ρ d ds l: *)
  (*   defs_interp T ρ ds -∗ *)
  (*   def_interp U ρ d -∗ *)
  (*   defs_interp (TAnd T U) ρ (cons (l, d) ds). *)
  (* Proof. naive_solver. Qed. *)

  Lemma def_interp_to_interp T d ds ρ s l:
    let v0 := (vobj ((l, d) :: ds)).[s] in
    nclosed_vl v0 0 →
    label_of_ty T = Some l →
    def_interp T ρ (d.|[v0 .: s]) ⊢
    interp T ρ v0.
  Proof.
    intros * Hfvv0 HTlabel. asimpl.
    set (d' := d.|[up s]); set (ds' := ds.|[up s]).
    assert (nclosed_vl (vobj ((l, d') :: ds')) 0) as Hfv'. {
      revert v0 Hfvv0.
      asimpl.
      by subst d' ds'.
    }
    assert (length ds = length ds') as Hlen'. by rewrite /ds' /hsubst map_length.
    assert (vobj ((l, d') :: ds') @ l ↘ d'.|[vobj ((l, d') :: ds')/]) as Hlookup.
      by eexists _; split => //=; case_match.
      (* XXX we need to rewrite this lemma for the new lookup relation, after fixing typing.
        by rewrite Hlen'; apply obj_lookup_cons. *)
    induction T => //=; try (by iIntros "**").
    all: cbn in HTlabel; injectHyps; iIntros "[% #H]"; move: H => Hvd.
    - iDestruct "H" as (vmem) "[#H1 #H2]".
      iSplit => //.
      iExists (d'.|[vobj ((l, d') :: ds')/]).
      subst d' ds'; iSplit => //.
      asimpl; trivial.
      (* subst d' ds'. asimpl. apply Hlookup. *)
      (* subst; eauto. *)
      (* subst d'. asimpl. *)
      iSplit => //. iExists _. iSplit => //.
    - iDestruct "H" as (φ) "[#Hl [#? [#? #?]]]".
      iSplit => //.
      iExists (d'.|[vobj ((l, d') :: ds')/]). iSplit => //.
      subst d'; asimpl.
      iSplit => //. iExists φ; iSplit => //.
      iModIntro. repeat iSplitL; naive_solver.
  Qed.

  (* Formerly wip_hard. *)
  Lemma defs_interp_to_interp T ds ρ s:
    let v0 := (vobj ds).[s] in
    nclosed_vl v0 0 →
    defs_interp T ρ (ds.|[v0 .: s]) ⊢
    interp T ρ v0.
  Proof.
    (* induction ds; asimpl; iIntros (Hcl) "H". *)
    (* - destruct T => //=. *)
    (* - simpl in IHds. *)
    (*   destruct T => //=. *)
    (*   Fail iApply dtp_tand_i. *)
    (*   Fail iApply IHds. *)
    (*   Restart. *)

    simpl; iIntros (Hcl) "#H".
    iPoseProof (defs_interp_v_closed with "H") as "%". move: H => Hclds.
    iInduction T as [] "IHT" forall (ds Hcl Hclds) => //=; try iDestruct "H" as (l1 d) "[% H']"; trivial.

    (* destruct ds => //=. rewrite map_length. *)
    (* iDestruct "H" as "[#H1 #H2]". *)
    (* iSplit. *)
    (* 2: { by iApply (def_interp_to_interp T2 d ds ρ s). } *)
    (* - asimpl. *)
    (*   iAssert (⟦ T1 ⟧ ρ (vobj (ds.|[up s]))) as "#H3". { *)
    (*     iApply ("IHT" $! ds) => //. *)
    (*     admit. *)
    (*     admit. *)
    (*     asimpl. *)
    (*     Fail iApply "H1". *)
    (*     admit. *)
    (*   } *)
    (*   (* We could probably go from H3 to the thesis... *) *)
    (*   iApply ("IHT" $! (d :: ds)) => //. *)
    (*   admit. *)

    (*   (* iApply (IHT1 (d :: ds)). *) *)
    (*   (* set (d' := d.|[up (to_subst ρ)]). *) *)
    (*   (* set (ds' := ds.|[up (to_subst ρ)]). *) *)
    (*   (* change (ds.|[up (to_subst ρ)]) with ds'. *) *)

    (* (* simpl. *) *)
    (* (* induction T; rewrite /defs_interp => //=; fold defs_interp; *) *)
    (* (* try solve [iIntros; try done]. *) *)
  Admitted.

  (* Check that Löb induction works as expected for proving introduction of
   * objects. Using Löb induction works easily.
   *
   * Γ, x: ▷ T ⊨ ds : T
   * ---------------------
   * Γ ⊨ nu x. ds : μ x. T
   *)
  Lemma T_New_I T ds:
     (TLater T :: Γ ⊨ds ds : T →
     Γ ⊨ tv (vobj ds) : TMu T)%I.
  Proof.
    iIntros "/= #[% Hds]". move: H => Hclds. iSplit; auto using fv_tv, fv_vobj. iIntros " !> * #Hρ /=".
    iApply wp_value.
    iPoseProof (interp_env_ρ_closed with "Hρ") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "Hρ") as "%". move: H => Hlen. rewrite <- Hlen in *.
    assert (nclosed_vl (vobj ds).[to_subst ρ] 0) as Hclvds. {
      eapply (fv_to_subst_vl (vobj ds)) => //. by apply fv_vobj.
    }

    iLöb as "IH".
    iApply defs_interp_to_interp. exact Hclvds.
    iPoseProof ("Hds" $! (vobj ds.|[up (to_subst ρ)] :: ρ)) as "#H".
    asimpl. iApply "H". repeat iSplit => //.
  Qed.

End Sec.
