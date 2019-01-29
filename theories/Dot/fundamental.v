From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.
From D Require Import tactics.
From D.Dot Require Import unary_lr typing synToSem lr_lemma.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

(* Should use fresh names. *)
Ltac iDestrConjs :=
  iMatchHyp (fun H P => match P with
                        | (_ ∧ _)%I =>
                          iDestruct H as "[#HA #HB]"
                        end).

Section fundamental.
  Context `{!dotG Σ}.

  (** Show fundamental lemma. *)
  (** That depends on existence of translations. To use it, we must start from syntactic terms.
      So, we should show that syntactic typing only applies to syntactic terms/types/contexts
      (and probably add hypotheses to that effect). *)
  (* XXX lift translation and is_syn to contexts. Show that syntactic typing
     implies is_syn and closure. Stop talking about free variables inside is_syn? *)
  Lemma typed_tm_is_syn Γ e T:
    Γ ⊢ₜ e : T →
    is_syn_tm e.
  Admitted.

  Lemma typed_ty_is_syn Γ e T:
    Γ ⊢ₜ e : T →
    is_syn_ty T.
  Admitted.

  (* Check all types are syntactic. *)
  Definition is_syn_ctx Γ := Forall is_syn_ty Γ.

  Lemma typed_ctx_is_syn Γ e T:
    Γ ⊢ₜ e : T →
    is_syn_ctx Γ.
  Admitted.

  Lemma transl_len ds ds': (t_vl (vobj ds) (vobj ds') → ⌜ length ds = length ds' ⌝)%I.
  Proof.
    iIntros "#H".
    cbn; fold t_dm t_dms.
    (* remember t_dms as t_ds eqn:Heqt. unfold t_dms in Heqt. rewrite -Heqt. fold t_dms in Heqt. rewrite Heqt. *)
    iInduction ds as [] "IHds" forall (ds'); destruct ds' => //.
                                      cbn; fold t_dms.
                                      iDestruct "H" as "[Hd Hds]".
                                        by iPoseProof ("IHds" with "Hds") as "<-".
  Qed.

  Lemma subst_len ds s: length ds.|[s] = length ds.
  Proof. induction ds => //=. f_equal. by asimpl. Qed.

  Lemma selfSubst_len ds: length (selfSubst ds) = length ds.
  Proof. apply subst_len. Qed.

  Lemma transl_lookup_commute' {l v1 v2 d1 d2}: v1 @ l ↘ d1 → v2 @ l ↘ d2 → (t_vl v1 v2 → t_dm d1 d2)%I.
  Proof.
    iIntros (Hlook1 Hlook2) "#HTr".
    inversion Hlook1 as (ds1 & -> & Hl1).
    inversion Hlook2 as (ds2 & -> & Hl2).
    rewrite lookup_reverse_indexr in Hl1.
    rewrite lookup_reverse_indexr in Hl2.
    iInduction ds1 as [| dh1 ds1] "IHds" forall (ds2 Hlook2 Hl2); destruct ds2 as [|dh2 ds2]=>//.
    iPoseProof (transl_len with "HTr") as "%". move: H => Hlen.
    injection Hlen; clear Hlen; intro Hlen.
    cbn in *; fold t_dm t_dms.
    asimpl in Hl1. asimpl in Hl2.
    case_decide.
    simpl in *.
    simplify_eq.
    fold t_dms.
  Admitted.

  Lemma transl_lookup_commute v v1 v2 l d1 d2:
    v1 @ l ↘ d1 → v2 @ l ↘ d2 →
    (t_vl v v1 → t_vl v v2 → ∃ d, ⌜ v @ l ↘ d ⌝ ∧ t_dm d d1 ∧ t_dm d d2)%I.
  Proof.
    iIntros (Hlook1 Hlook2) "#HTr1 #HTr2".
    inversion Hlook1 as (ds1 & -> & Hl1).
    inversion Hlook2 as (ds2 & -> & Hl2).
    destruct v => //.
    iPoseProof (transl_len with "HTr1") as "%". move: H => Hlen1.
    iPoseProof (transl_len with "HTr2") as "%". move: H => Hlen2.
    assert (∃ d, reverse (selfSubst l0) !! l = Some d) as [d Hl]. {
      apply lookup_lt_is_Some_2.
      rewrite reverse_length selfSubst_len Hlen1 -selfSubst_len -reverse_length.
      eapply lookup_lt_is_Some_1. rewrite Hl1; eauto.
    }
    assert (vobj l0 @ l ↘ d). by exists l0.
    iExists d. repeat iSplit => //; by iApply transl_lookup_commute'.
  Qed.

  Lemma lookups_agree v0 v1 v2 ρ σ1 σ2 γ1 γ2 φ1  l:
    v1.[to_subst ρ] @ l ↘ dtysem σ1 γ1 → v2.[to_subst ρ] @ l ↘ dtysem σ2 γ2 →
    (t_vl v0 v1 → t_vl v0 v2 →
     γ1 ⤇ φ1 →
     ∃ (φ2: listVlC -n> vlC -n> iProp Σ),
       γ2 ⤇ (λ vs, φ2 vs) ∧
       ∀ ρ v,
         ⌜ length ρ = length σ1 ⌝ →
         ▷ (φ1 (subst_sigma σ1 ρ) v ≡ φ2 (subst_sigma σ2 ρ) v))%I.
  Proof.

    iIntros (Hlook1 Hlook2) "#HTr1 #HTr2 #Hγφ".
    inversion Hlook1 as (ds1 & Hobj1 & Hl1).
    inversion Hlook2 as (ds2 & Hobj2 & Hl2).

    destruct v0; destruct v1; cbn in Hobj1; try (iAssumption || discriminate).
    all: destruct v2 =>//.
    (**
       We have two cases: either v, v1 and v2 are the same variable, and then
       the two definitions are the same, or they're translated objects, and then
       translation commutes with lookup.
     *)
    -
      iDestruct "HTr1" as "->".
      iDestruct "HTr2" as "->".
      cbn in Hobj1, Hobj2 |- *.
      repeat optFuncs_det.
      iExists (λne vs v, φ1 vs v); by iSplit.
    -
      cbn in Hobj1, Hobj2 |-.
      cinject Hobj1.
      cinject Hobj2.

      (** Now we need to apply transl_lookup_commute, but beware!
          we can't prove that [t_vl (vobj l0).[to_subst ρ] (vobj l1).[to_subst
          ρ]], because [ρ] is translated!
          Instead, show lookup works before substitution. *)

      assert (∃ d1, (vobj l1) @ l ↘ d1) as [d1 HlookupUntransl1] by admit.
      assert (∃ d2, (vobj l2) @ l ↘ d2) as [d2 HlookupUntransl2] by admit.

      iPoseProof (transl_lookup_commute _ _ _ _ _ _ HlookupUntransl1 HlookupUntransl2 with "HTr1 HTr2")
        as (d) "[% [HtrdUns1 HtrdUns2]]".
      (* cbn; fold t_dm t_dms. *)
      (* XXX Now, we again struggle: we'd want substitution to preserve
         translation and lookup, but ρ is translated. So either we should that
         d1 and d2 must already be dtysems (a whole definition can't be a
         variable), so that ρ only affects σ, or we require that ρ has an
         untranslated counterpart (which is not obvious, as there are more
         semantic types than syntactic ones, though the restriction should be
         OK. *)
      assert ((vobj l0).[to_subst ρ] @ l ↘ d.|[to_subst ρ]) as Hlookv0. admit.
      (* hnf in Hlookv0. *)
      iAssert (t_dm d.|[to_subst ρ] (dtysem σ1 γ1))%I as "#Htrd1". admit.
      iAssert (t_dm d.|[to_subst ρ] (dtysem σ2 γ2))%I as "#Htrd2". admit.
      iPoseProof (t_dm_agree _ _ _ _ _ _ eq_refl with "Htrd1 Htrd2 Hγφ") as (σ γ φ) "[% [Hγ2 Hfoo]]".
      injectHyps.
      iExists φ. by repeat iSplit.
  Admitted.

  (* The proof of the lemma below is tedious. Maybe this would be easier using
     ≡, but I now believe that would be false, because the lemma only holds in
     certain worlds, while ≡ require two propositions to coincide in all worlds.
   *)

  Lemma translations_types_equivalent_vals T T' T'' v ρ:
    (t_ty T T' → t_ty T T'' → ⟦ T' ⟧ ρ v ↔ ⟦ T'' ⟧ ρ v)%I.
  Proof.
    revert T' T'' ρ v.
    induction T => /=; iIntros (T' T'' ρ v) "#H1 #H2"; destruct T' => //=; destruct T'' => //=; cbn;
    try (iDestruct "H1" as "[H11 H12]");
    try (iDestruct "H2" as "[H21 H22]").
    (* Check (@bi.and_proper (iPropSI Σ)). *)
    (* - iApply bi.and_proper. *)

    all: iSplit; iIntros "#Hv"; try (iDestruct "Hv" as "[#Hv1 #Hv2]"); try iFrame "Hv1"; try by iApply (IHT with "H1 H2").
    all: fold t_path.

    (* To prove equivalence this way, I end up having to copy-paste proofs. *)
    - iSplit; by [iApply (IHT1 with "H11 H21") | iApply (IHT2 with "H12 H22")].
    - iSplit; by [iApply (IHT1 with "H11 H21") | iApply (IHT2 with "H12 H22")].
    - iDestruct "Hv" as "[Hv1 | Hv2]"; by [iLeft ; iApply (IHT1 with "H11") | iRight; iApply (IHT2 with "H12")].
    - iDestruct "Hv" as "[Hv1 | Hv2]"; by [iLeft ; iApply (IHT1 with "H11") | iRight; iApply (IHT2 with "H12")].
    - iDestruct "Hv2" as (t ->) "#Hv2".
      iExists _; iSplitL; first done.
      iIntros "!> !> **".
      iApply wp_wand.
      + iApply "Hv2". by iApply (IHT1 with "H11 H21").
      + iIntros. by iApply (IHT2 with "H12 H22").
    - iDestruct "Hv2" as (t ->) "#Hv2".
      iExists _; iSplitL; first done.
      iIntros "!> !> **".
      iApply wp_wand.
      + iApply "Hv2". by iApply (IHT1 with "H11 H21").
      + iIntros. by iApply (IHT2 with "H12 H22").
    - iDestruct "H11" as "%". iDestruct "H21" as "%".
      iDestruct "Hv2" as (d) "[% [% H]]". iDestruct "H" as (vmem) "[% H]".
      subst.
      repeat (iExists _; repeat iSplit => //). by iApply (IHT with "H12 H22").
    - iDestruct "H11" as "%". iDestruct "H21" as "%".
      iDestruct "Hv2" as (d) "[% [% H]]". iDestruct "H" as (vmem) "[% H]".
      subst.
      repeat (iExists _; repeat iSplit => //). by iApply (IHT with "H12 H22").
    - iDestruct "H11" as "%". iDestruct "H21" as "%".
      iDestruct "H12" as "[H11 H12]".
      iDestruct "H22" as "[H21 H22]".
      iDestruct "Hv2" as (d) "[% [% H]]". iDestruct "H" as (φ σ) "[Hl #[H2 [H3 H4]]]".
      subst.
      repeat (iExists _; repeat iSplit => //).
      iDestruct "Hv1" as "%".
      iModIntro. repeat iSplitL; iIntros.
      + iApply "H2" => //. by iApply (IHT1 with "H11 H21").
      + iApply (IHT2 with "H12 H22"). by iApply "H3".
      + iApply (IHT2 with "H12 H22"). iApply "H4". by iApply (IHT1 with "H11 H21").
    (* Copy-paste *)
    - iDestruct "H11" as "%". iDestruct "H21" as "%".
      iDestruct "H12" as "[H11 H12]".
      iDestruct "H22" as "[H21 H22]".
      iDestruct "Hv2" as (d) "[% [% H]]". iDestruct "H" as (φ σ) "[Hl #[H2 [H3 H4]]]".
      subst.
      repeat (iExists _; repeat iSplit => //).
      iDestruct "Hv1" as "%".
      iModIntro. repeat iSplitL; iIntros.
      + iApply "H2" => //. by iApply (IHT1 with "H11 H21").
      + iApply (IHT2 with "H12 H22"). by iApply "H3".
      + iApply (IHT2 with "H12 H22"). iApply "H4". by iApply (IHT1 with "H11 H21").

    - iDestruct "H12" as "->". iDestruct "H22" as "->".
      iDestruct "Hv1" as "%". move: H => Hclv.
      iDestruct "Hv2" as "[[] | H]". iRight.
      iInduction p as [] "IHp" forall (p0 p1) "H"; destruct p0 => //; destruct p1 => //; cbn; fold t_vl.
      + iDestruct "H" as (σ1 φ1 d1) "[% [H Hφ]]". move: H => Hlook1.
        iDestruct "H" as (γ1) "[-> Hγ1]".
        (* These admits are (hopefully )syntactic lemmas provable on the translation. *)
        assert (∃ σ2 γ2, v2.[to_subst ρ] @ l1 ↘ dtysem σ2 γ2) as (σ2 & γ2 & Hlook2) by admit.
        iPoseProof (lookups_agree with "H11 H21 Hγ1") as "H" => //.
        iDestruct "H" as (φ2) "[Hγ2 Hφequiv]".
        iExists σ2, φ2, (dtysem σ2 γ2). repeat iSplit => //.
        * iExists _; iSplit =>//.
        * (* Since σ and σ1 come from
             [v1.[to_subst ρ] @ l1 ↘ dtysem σ1 γ1] and
             [v2.[to_subst ρ] @ l1 ↘ dtysem σ γ], they are closed, and arise
             from substituting [ρ] into the open σs in [v1] and [v2]. *)
          (* XXX We must restrict the hypotheses: this lemma only holds for ρ that are closed and of the right size.*)
          iAssert (⌜ length ρ = length σ1 ⌝)%I as "#Hlen". admit.
          iSpecialize ("Hφequiv" $! ρ v with "Hlen").
          (* XXX I'm not sure exactly how we should prove those. We need extra hypotheses.
             IMHO, we should ensure that [v1.[to_subst ρ]] and [v2.[to_subst ρ]]
             are closed, then reason that [σ1] and [σ2] are closed, hence
             [subst_sigma σ1 ρ = σ1] and [subst_sigma σ2 ρ = σ2] by [closed_subst_id].
             For that, IMHO, we must use [fv_to_subst_vl]. For that, finally, we
             must require [cl_ρ ρ] (which follows from [⟦Γ⟧*ρ] by
             [interp_env_ρ_closed]), so we should have it in the fundamental
             theorem), and [nclosed v1 (length ρ)] and [nclosed v2 (length ρ)],
             which should follow from [nclosed v0 (length ρ)].
           *)
          assert (subst_sigma σ2 ρ = σ2) as -> by admit.
          assert (subst_sigma σ1 ρ = σ1) as -> by admit.
          repeat iModIntro.
          iRewrite -"Hφequiv". done.
      +
        iDestruct "H11" as "[H11 ->]".
        iDestruct "H21" as "[H21 ->]".
        iSpecialize ("IHp" $! p0 p1 with "H11 H21").
        (* This induction doesn't seem to work - we must generalize by hand over
           the continuation I guess? *)
        admit.
    - admit.
    -
      iDestruct "H12" as "[-> [HTrT11 HTrT12]]".
      iDestruct "H22" as "[-> [HTrT21 HTrT22]]".
      iSplit. by iApply (IHT2 with "HTrT12 HTrT22").
      iDestruct "Hv2" as "[HT1|Hv2]".
      + iLeft. by iApply (IHT1 with "HTrT11 HTrT21").
      + iRight.
        (* Now we're back to the same proof as above. We might want to prove
           this for interp_sela and reuse it. *)
      admit.
    - admit.
  Admitted.

  Lemma translations_types_equivalent e T T' T'' Γ:
    (t_ty T T' → t_ty T T'' → Γ ⊨ e : T' → Γ ⊨ e : T'' )%I.
  Proof.
    iIntros "#A #B #[% #C] /="; iSplit => //. iIntros (ρ) "!> #D".
    rewrite /interp_expr /=.
    iApply wp_strong_mono => //. { by iApply "C". }
    iIntros (v) "HT' !>". by iApply (translations_types_equivalent_vals T T' T'').
  Qed.

  (* What we actually want is closer to:

  (* Check all types are translated. *)
  Definition t_ctx Γ Γ' := Forall2 t_ty Γ Γ'.
  Fixpoint fundamental Γ e T Γ' e' T' (HT: Γ ⊢ₜ e : T) {struct HT}:
  (* Lemma not_yet_fundamental Γ e T e' T' (HT: Γ ⊢ₜ e : T): *)
    t_ctx Γ Γ' → (t_tm e e' → t_ty T T' → |==> Γ' ⊨ e' : T')%I.

  Except we need an "Iris" Forall2. Gotta run but I know a few ways.
   *)
  (* Similarly, below we use: *)
  Lemma t_ty_subst_special: ∀ T T' v v', (t_ty T T' → t_vl v v' → t_ty (T.|[v/]) (T'.|[v'/]))%I.
  Admitted.
  (* But I guess we'll we actually need to say that two substitutions translate each other. *)

  Fixpoint not_yet_fundamental Γ e T e' T' (HT: Γ ⊢ₜ e : T) {struct HT}:
  (* Lemma not_yet_fundamental Γ e T e' T' (HT: Γ ⊢ₜ e : T): *)
    (t_tm e e' → t_ty T T' → |==> Γ ⊨ e' : T')%I.
  Proof.
    iIntros "#HtrE #HtrT".
    (* destruct HT. *)
     iInduction HT as [] "IHT" forall (e' T') "HtrE HtrT".
    -
      (* I'm careful with simplification to avoid unfolding too much. *)
      set (e2 := tv v2).
      cbn [t_tm] in * |- *; case_match; try done.
      iDestruct "HtrE" as "[Htr1 Htr2]".
      unfold e2.
      iEval (cbn [t_tm]) in "Htr2"; case_match; try done; fold (t_vl v2 v).
      iAssert (t_tm (tv v2) (tv v)) as "#Ht2"; first done.
      iMod (ex_t_ty (length Γ) T1) as (T1') "#HTT1r".
      (* nclosed: *) admit.
      { eauto using typed_ty_is_syn. }
      iMod (ex_t_ty (S (length Γ)) T2) as (T2') "#HTT2r".
      (* nclosed: *) admit.
      { assert (is_syn_ty (TAll T1 T2)) as Hsyn by eauto using typed_ty_is_syn. simpl in Hsyn. intuition. }

      iMod ("IHT" $! t1 (TAll T1' T2') with "Htr1 []") as "#toto".
      { iModIntro. unfold t_ty; simpl; fold t_ty. iSplit; try done. }
      iMod ("IHT1" $! (tv v) T1' with "Ht2 []") as "#tata". by [].

      iAssert (t_ty (T2.|[v2/]) (T2'.|[v/])) as "#HHH".
      { by iApply t_ty_subst_special. }
      iApply translations_types_equivalent; try done.

      by iApply (T_Forall_Ex  with "toto tata").
    -
      (* I'm careful with simplification to avoid unfolding too much. *)
      cbn [t_tm] in * |- *; case_match; try done.
      iDestruct "HtrE" as "[Htr1 Htr2]".
      iMod (ex_t_ty (length Γ) T1) as (T1') "#HTTr".
      (* nclosed: *) admit.
      eauto using typed_ty_is_syn.
      iAssert (t_ty T2.|[ren (+1)] T'.|[ren (+1)]) as "#HtrT2s". { admit. }
      iAssert (t_ty (TAll T1 T2.|[ren (+1)]) (TAll T1' T'.|[ren (+1)])) as "#HtrTAll".
      { cbn; by iSplit. }
      iMod ("IHT"with "Htr1 HtrTAll") as "#HsT1".
      iMod ("IHT1" with "Htr2 HTTr") as "#HsT2".
      by iApply (T_Forall_E with "HsT1 HsT2").
    (* pose proof (typed_tm_is_syn Γ e T HT) as HeSyn. *)
    (* pose proof (typed_ty_is_syn Γ e T HT) as HTSyn. *)
    (* pose proof (typed_ctx_is_syn Γ e T HT) as HΓSyn. *)

    (* (* XXX using the translation here means we end up using it again later, and *)
    (*    we'd even have to prove it's deterministic (which it isn't?) or smth. such! *)
    (*    Let's avoid that. *) *)
    (* iMod (ex_t_tm [] (length Γ) e) as (e') "#HeTr"; first done. *)
    (* iMod (ex_t_ty [] (length Γ) T) as (T') "#HTTr"; first done. *)
    (* iExists Γ, e', T'. repeat iSplitL; try done. *)
    (* Induction keeps the same expression e' in the conclusion of *all* induction hypotheses. *)
    (* iInduction HT as []  "IHT" forall "HeTr HTTr". *)
    (* So use destruct and a recursive proof; we'll need this anyway since the
       proof is by mutual induction on typing, subtyping etc.*)
    (* iDestruct HT as ([]) "". "IHT" forall "HeTr HTTr". *)
    (* - *)
    (*   (* Arguments t_tm _ _ _ /. *) *)
    (*   (* Arguments t_vl _ _ _ /. *) *)

    (*   (* destruct e'; cbn [t_tm]; try done. *) *)
    (*   (* fold (t_tm [] e1 e'1). *) *)
    (*   (* fold (t_tm [] (tv v2) e'2). *) *)
    (*   (* iDestruct "HeTr" as "[HeTr' HeTr'']". *) *)
    (*   cbn [t_tm] in * |- *; case_match; iStartProof. *)
    (*   iMod (ex_t_tm [] (length Γ) e1) as (e1') "#He1Tr"; first done. *)
    (*   iMod (ex_t_vl [] (length Γ) v2) as (v2') "#Hv2Tr"; first done. *)
    (*   assert (is_syn_ty (S (length Γ)) T2) by admit. *)
    (*   iMod (ex_t_ty [] (S (length Γ)) T2) as (T2') "#HTTr"; first done. *)
    (*   (* Here we seem to need a substitution lemma for the translation of types! *) *)
    (*   assert (t_ty [] T2.|[v2/] T2'.|[v2'/]) by admit. *)
    (*   iExists Γ. (tapp e1' (tv v2')), T2'.|[v2'/]. *)
    (*   repeat iSplitL; try done. *)
    (*   + iApply H3. *)
    (*   + *)
    (*     (* XXX: Here, recursive calls to the lemma still produce a fresh translation, *)
    (*        not the one we have; since translation isn't deterministic, that's bad. *)
    (*        We should take translations as hypotheses. *) *)
    (*   iMod (not_yet_fundamental Γ e1 _ HT1) as (Γ' e1'' T0') "#(H1 & H2 & H3)". *)
    (*   iMod (not_yet_fundamental Γ (tv v2) _ HT2) as (Γ'' e2'' T0'') "#(H4 & H5 & H6)". *)

    (*   (* iEval (cbn [t_tm]) in "HeTr". progress (case_match; try done); subst; *) *)
    (*   (* repeat iMatchHyp (fun H P => match P with *) *)
    (*   (*                       | (_ ∧ _)%I => *) *)
    (*   (*                         iDestruct H as "[#HA #HB]" *) *)
    (*   (*                       end). *) *)
    (*   (* fold (t_tm [] e1 t1). *) *)
    (*   (* fold (t_tm [] (tv v2) t2). *) *)
    (*   (* assert (e1'' = t2) as -> by admit. *) *)
    (*   (* (* iEval (cbn) in "HB". progress (case_match; try done); subst. *) *) *)
    (*   (* (* progress fold (t_vl [] v2 v). *) *) *)
    (*   (* iClear "H4". *) *)
    (*   (* iEval (cbn) in "H2". progress (case_match; try done); subst. *) *)
    (*   (* iDestruct "H2" as "[H7 H8]". *) *)
    (*   (* assert (e1' = t1) as -> by admit. *) *)
    (*   (* assert (T0'' = t3) as -> by admit. *) *)
    (*   (* assert (Γ'' = Γ') as -> by admit. *) *)
    (*   (* (* progress fold (t_vl [] v2 v0). *) *) *)
    (*   (* (* progress fold (t_tm [] e1 t1). *) *) *)
    (*   (* iModIntro. *) *)
    (*   (* (* iEval (simpl) in "HA". *) *) *)
    (*   (* (* iSimpl in "HA". *) *) *)
  Admitted.

End fundamental.
