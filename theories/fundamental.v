From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import tactics.
From Dot Require Import tactics unary_lr typing AAsynToSem lr_lemma.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

(* Should use fresh names. *)
Ltac iDestrConjs :=
  iMatchHyp (fun H P => match P with
                        | (_ ∧ _)%I =>
                          iDestruct H as "[#HA #HB]"
                        end).

Section fundamental.
  Context `{dotG Σ}.

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

  (* The proof of the lemma below is tedious.
     It'd be nicer to prove a variant using as relation either ⌜ _ = _ ⌝ or ⌜ _
     ≡ _ ⌝ or _ ≡ _ (those are all distinct!); however, proofs failed for each
     of those in a different way I did not know how to fix - a combination of
     - the [properness] tactic does not work here because it's for a different set of lemmas.
     - iRewrite doesn't work under binders
     - iRewrite works only with some but not others of those equivalence relations

     BTW, it'd be ideal to equate ⟦ T' ⟧ ≡ ⟦ T'' ⟧ since sometimes we pass other
     arguments, but that doesn't seem to work either for unclear reasons.
     Here are two attempts.
   *)
  Lemma translations_types_equivalent_vals_try1 T T' T'':
    (t_ty T T' → t_ty T T'' → ⟦ T' ⟧ ≡ ⟦ T'' ⟧)%I.
  Proof.
    revert T' T''.
    induction T => /=; iIntros (T' T'') "#H1 #H2"; destruct T' => //=; destruct T'' => //=; cbn;
    try (iDestruct "H1" as "[H11 H12]");
    try (iDestruct "H2" as "[H21 H22]").
    Fail iRewrite (IHT1 _ _ with "H11 H21").
  Abort.

  Lemma translations_types_equivalent_vals_try2 T T' T'' ρ:
    (t_ty T T' → t_ty T T'' → ⟦ T' ⟧ ρ ≡ ⟦ T'' ⟧ ρ)%I.
  Proof.
    revert T' T'' ρ.
    induction T => /=; iIntros (T' T'' ρ) "#H1 #H2"; destruct T' => //=; destruct T'' => //=; cbn;
    try (iDestruct "H1" as "[H11 H12]");
    try (iDestruct "H2" as "[H21 H22]").
    Fail iRewrite (IHT1 _ _ ρ with "H11 H21").
  Abort.

  (* Lemma translations_types_equivalent_vals T T' T'' v ρ: *)
  (*   (t_ty T T' → t_ty T T'' → ⌜ ⟦ T' ⟧ ρ v ≡ ⟦ T'' ⟧ ρ v ⌝)%I. *)
  (* Proof.  *)
  (*   revert T' T'' ρ v. *)
  (*   induction T => /=; iIntros (T' T'' ρ v) "#H1 #H2"; destruct T' => //=; destruct T'' => //=; cbn; *)
  (*   try (iDestruct "H1" as "[H11 H12]"); *)
  (*   try (iDestruct "H2" as "[H21 H22]"). *)
  (*   all: try iPoseProof (IHT1 _ _ ρ v with "H11 H21") as "->"; try iPoseProof (IHT2 _ _ ρ v with "H12 H22") as "->"; try iPoseProof (IHT _ _ ρ v with "H1 H2") as "->". *)
  (*   all: try done. *)
  (*   iAssert (∀ ρ v, ⌜ ⟦ T'1 ⟧ ρ v ≡ ⟦ T''1 ⟧ ρ v ⌝)%I as "#H". by iIntros; iApply IHT1. *)
  (*   iRewrite "H". *)

  (*   all: try iRewrite (IHT1 _ _ ρ v with "H11 H21"); try iRewrite (IHT2 _ _ ρ v with "H12 H22"); *)
  (*   try iRewrite (IHT _ _ ρ v with "H1 H2"). *)
  (*   all: try done. *)

  (*   iPoseProof (IHT1 _ _ ρ v with "H11 H21") as "->". *)
  (*   iPoseProof (IHT2 _ _ ρ v with "H11 H21") as "->". *)
  (*   try iRewrite (IHT2 _ _ ρ v with "H12 H22"); *)
  (*   admit. *)
  (*   by iRewrite (IHT _ _ (v :: ρ) v with "H1 H2"). *)
  (*   Check bi.sep_proper. *)
  (*   -  *)
  (*     About sbi_internal_eq. *)
  (*     Check sbi_internal_eq. *)
  (*   Set Printing All. *)
  (*   Check (1 ≡ 2)%I. *)
  (*   Check bi_emp_valid. *)
  (*   properness. *)
  (*   iRewrite (IHT _ _ ρ with "H1 H2"). *)
  (*   - iSplit; by [iApply (IHT1 with "H11 H21") | iApply (IHT2 with "H12 H22")]. *)
  (*   - iDestruct "Hv" as "[Hv1 | Hv2]"; by [iLeft ; iApply (IHT1 with "H11") | iRight; iApply (IHT2 with "H12")]. *)
  (*   - iFrame "Hv1". by iApply (IHT with "H1 H2"). *)
  (*   -  *)

  Lemma translations_types_equivalent_vals T T' T'' v ρ:
    (t_ty T T' → t_ty T T'' → ⟦ T' ⟧ ρ v ↔ ⟦ T'' ⟧ ρ v)%I.
  Proof.
    revert T' T'' ρ v.
    induction T => /=; iIntros (T' T'' ρ v) "#H1 #H2"; destruct T' => //=; destruct T'' => //=; cbn;
    try (iDestruct "H1" as "[H11 H12]");
    try (iDestruct "H2" as "[H21 H22]").

    all: iSplit; iIntros "#Hv"; try (iDestruct "Hv" as "[#Hv1 #Hv2]"); try iFrame "Hv1"; try by iApply (IHT with "H1 H2").

    (* To prove equivalence this way, I end up having to copy-paste proofs. *)
    - iSplit; by [iApply (IHT1 with "H11 H21") | iApply (IHT2 with "H12 H22")].
    - iSplit; by [iApply (IHT1 with "H11 H21") | iApply (IHT2 with "H12 H22")].
    - iDestruct "Hv" as "[Hv1 | Hv2]"; by [iLeft ; iApply (IHT1 with "H11") | iRight; iApply (IHT2 with "H12")].
    - iDestruct "Hv" as "[Hv1 | Hv2]"; by [iLeft ; iApply (IHT1 with "H11") | iRight; iApply (IHT2 with "H12")].
    - iIntros "!> **".
      iApply wp_wand.
      + iApply "Hv2". by iApply (IHT1 with "H11 H21").
      + iIntros. by iApply (IHT2 with "H12 H22").
    - iIntros "!> **".
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
    - fold t_path.
      iDestruct "H12" as "%". iDestruct "H22" as "%".
      iDestruct "Hv1" as "%".
      iDestruct "Hv2" as "[[] | H]". iRight.
      subst.
      iInduction p as [] "IHp" forall (p0 p1) "H"; destruct p0 => //; destruct p1 => //; cbn.
      fold t_vl.
      + iDestruct "H" as (σ1 φ1 d1) "[% [H Hφ]]". iDestruct "H" as (γ1) "[-> Hγ1]".
        (* These admits are syntactic lemmas provable on the translation. *)
        assert (∃ σ2 γ2, v2.[to_subst ρ] @ l1 ↘ dtysem σ2 γ2) as (σ2 & γ2 & ?) by admit.
        iAssert (∃ d, t_dm d (dtysem σ1 γ1))%I as (d) "#Htrd1". admit.
        iAssert (t_dm d (dtysem σ2 γ2))%I as "#Htrd2". admit.
        iPoseProof (t_dm_agree _ _ _ _ _ _ eq_refl with "Htrd1 Htrd2 Hγ1") as (σ γ φ) "[% [Hγ2 Hfoo]]".
        injectHyps.
        iExists σ, φ, (dtysem σ γ). repeat iSplit => //.
        * iExists _; iSplit =>//.
        * (* Since σ and σ1 come from
             [v1.[to_subst ρ] @ l1 ↘ dtysem σ1 γ1] and
             [v2.[to_subst ρ] @ l1 ↘ dtysem σ γ], they are closed, and arise
             from substituting [ρ] into the open σs in [v1] and [v2]. *)
          (* XXX We must restrict the hypotheses: this lemma only holds for ρ that are closed and of the right size.*)
          iAssert (⌜ length ρ = length σ1 ⌝)%I as "#Hlen". admit.
          iSpecialize ("Hfoo" $! ρ v with "Hlen").
          assert (subst_sigma σ ρ = σ) as -> by admit.
          assert (subst_sigma σ1 ρ = σ1) as -> by admit.
          repeat iModIntro.
          iRewrite -"Hfoo". done.
      +
        iDestruct "H11" as "[H11 ->]".
        iDestruct "H21" as "[H21 ->]".
        iSpecialize ("IHp" $! p0 p1 with "H11 H21").
        (* This induction doesn't seem to work - we must generalize by hand over
           the continuation I guess? *)
        admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Lemma translations_types_equivalent e T T' T'' Γ:
    (t_ty T T' → t_ty T T'' → Γ ⊨ e : T' → Γ ⊨ e : T'' )%I.
  Proof.
    iIntros "#A #B #[% C] /="; iSplit => //. iIntros (ρ) "!> #D".
    unfold interp_expr. simpl.
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
      { assert (is_syn_ty (TAll T1 T2)) by eauto using typed_ty_is_syn. simpl in H0. intuition. }

      iPoseProof (not_yet_fundamental Γ e1 _ _ _ HT1 with "Htr1") as "HsT1".
      iMod (not_yet_fundamental Γ (tv v2) _ _ _ HT2 with "Ht2 HTT1r") as "#HsT2".
      iPoseProof ("IHT" $! t1 (TAll T1' T2') with "Htr1 []") as "toto".
      { iModIntro. unfold t_ty; simpl. fold t_ty. iSplit; try done. }
      iPoseProof ("IHT1" $! (tv v) T1' with "Ht2 []") as "tata".
      { iModIntro. unfold t_ty; simpl. fold t_ty. done. }
      iMod "toto". iMod "tata".

      iAssert (t_ty (T2.|[v2/]) (T2'.|[v/])) as "#HHH".
      { admit. }
      iApply (translations_types_equivalent); try done.

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
      iMod (not_yet_fundamental Γ e1 _ _ _ HT1 with "Htr1 HtrTAll") as "#HsT1".
      iMod (not_yet_fundamental Γ e2 _ _ _ HT2 with "Htr2 HTTr") as "#HsT2".
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
