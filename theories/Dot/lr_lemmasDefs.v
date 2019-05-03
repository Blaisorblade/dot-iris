From iris.proofmode Require Import tactics.
From D Require Import tactics.
From D.Dot Require Import unary_lr_binding rules.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

From D Require Import locAsimpl.

Lemma norm_selfSubst ds s: selfSubst ds.|[up s] = ds.|[(vobj ds).[s] .: s].
Proof. by rewrite /selfSubst /=; asimpl. Qed.

Lemma dms_hasnt_map_mono ds l f:
  dms_hasnt ds l →
  dms_hasnt (map (mapsnd f) ds) l.
Proof.
  elim: ds => //; rewrite /dms_hasnt/mapsnd/= => [[l' d] ds IHds H].
  by case_decide; eauto 2.
Qed.

Lemma dms_lookup_head l d ds: dms_lookup l ((l, d) :: ds) = Some d.
Proof. by cbn; case_decide. Qed.

Lemma dms_lookup_mono l l' d d' ds:
  dms_hasnt ds l →
  dms_lookup l' ds = Some d' →
  dms_lookup l' ((l, d) :: ds) = Some d'.
Proof.
  rewrite /dms_hasnt /= => Hlds Hl; by case_decide; simplify_eq.
Qed.

Section Sec.
  Context `{HdotG: dotG Σ}.

  Lemma lift_dinterp_dms_vl_commute T ds ρ l:
    nclosed_vl (vobj ds) 0 →
    label_of_ty T = Some l →
    lift_dinterp_dms T ρ (selfSubst ds) -∗
    lift_dinterp_vl l (def_interp T) ρ (vobj ds).
  Proof.
    rewrite /lift_dinterp_dms => /= ? ->; iIntros "H".
    iDestruct "H" as (?l d (?&?&?)) "?"; simplify_eq.
    iSplit => //. iExists d; iFrame; iPureIntro. by eexists _.
  Qed.

  Lemma lift_dsinterp_dms_vl_commute T ds ρ:
    nclosed_vl (vobj ds) 0 →
    defs_interp T ρ (selfSubst ds) -∗
    interp T ρ (vobj ds).
  Proof.
    iIntros (Hcl) "#H".
    iPoseProof (defs_interp_v_closed with "H") as "%". move: H => Hclds.
    iInduction T as [] "IHT"; cbn;
    try by [| iDestruct "H" as (???) "?"].
    - iDestruct "H" as "[#H1 #H2]".
      by iSplit; [> iApply "IHT"| iApply "IHT1"].
    - by iApply (lift_dinterp_dms_vl_commute (TVMem _ _)).
    - by iApply (lift_dinterp_dms_vl_commute (TTMem _ _ _)).
  Qed.

  Lemma def2defs_head T l ρ d ds:
    label_of_ty T = Some l →
    nclosed ((l, d) :: ds) 0 →
    def_interp T ρ d -∗
    lift_dinterp_dms T ρ ((l, d) :: ds).
  Proof. iIntros; iExists l, d. eauto using dms_lookup_head. Qed.

  Lemma fv_pair_cons_dms l d ds n:
    nclosed ds n → nclosed d n → nclosed ((l, d) :: ds) n.
  Proof. by apply fv_pair_cons. Qed.
  Hint Resolve fv_pair_cons_dms.

  Lemma lift_dinterp_dms_mono T l ρ d ds:
    dms_hasnt ds l → nclosed d 0 → nclosed ds 0 →
    lift_dinterp_dms T ρ ds -∗
    lift_dinterp_dms T ρ ((l, d) :: ds).
  Proof.
    iIntros (???) "#HT"; iDestruct "HT" as (l' d' (?&?&?)) "#H".
    iExists _, _; iSplit; eauto 6 using dms_lookup_mono.
  Qed.

  Lemma defs_interp_mono T l ρ d ds:
    dms_hasnt ds l → nclosed d 0 → nclosed ds 0 →
    defs_interp T ρ ds -∗
    defs_interp T ρ ((l, d) :: ds).
  Proof.
    iIntros (Hlds Hcls Hclds) "#HT".
    iInduction T as [] "IHT" => //=;
      try by [iDestruct "HT" as (???) "?" | iApply lift_dinterp_dms_mono | auto].
    iDestruct "HT" as "[HT1 HT2]"; iSplit; by [>iApply "IHT"|iApply "IHT1"].
  Qed.

  Context Γ.

  Local Arguments lift_dinterp_vl: simpl never.
  Local Arguments lift_dinterp_dms: simpl never.
  Local Arguments def_interp_tmem: simpl never.
  Local Arguments def_interp_vmem: simpl never.

  (** Lemmas about definition typing. *)
  Lemma TVMem_I (V: ty) T v l:
    V :: Γ ⊨ tv v : T -∗
    Γ |L V ⊨d dvl v : TVMem l T.
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

  (* Check that Löb induction works as expected for proving introduction of
   * objects. Using Löb induction works easily.
   *
   * Γ, x: ▷ T ⊨ ds : T
   * ---------------------
   * Γ ⊨ nu x. ds : μ x. T
   *)
  Lemma T_New_I T ds:
     Γ |L T ⊨ds ds : T -∗
     Γ ⊨ tv (vobj ds) : TMu T.
  Proof.
    iIntros "/= #[% #Hds]"; move: H => Hclds.
    iSplit; auto using fv_tv, fv_vobj.
    iIntros " !> * #Hρ /="; iApply wp_value.
    iPoseProof (interp_env_ρ_closed with "Hρ") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "Hρ") as "%". move: H => Hlen.
    have Hclvds: nclosed_vl (vobj ds).[to_subst ρ] 0.
      by eapply (fv_to_subst_vl (vobj ds)); rewrite // Hlen; apply fv_vobj.
    iLöb as "IH".
    iApply lift_dsinterp_dms_vl_commute;
      rewrite // norm_selfSubst -to_subst_cons.
      iApply "Hds"; by iFrame "IH Hρ".
  Qed.

  Lemma DNil_I : Γ ⊨ds [] : TTop.
  Proof. iSplit => //. by iIntros "!> **". Qed.

  Lemma DCons_I d ds l T1 T2:
    dms_hasnt ds l →
    label_of_ty T1 = Some l →
    Γ  ⊨d d : T1 -∗ Γ  ⊨ds ds : T2 -∗
    Γ  ⊨ds (l, d) :: ds : TAnd T1 T2.
  Proof.
    iIntros (Hlds Hl) "[% #H1] [% #H2]". move: H H0 => Hcld Hclds.
    have Hclc: nclosed ((l, d) :: ds) (length Γ). by auto.
    iSplit => //; iIntros "!>" (ρ) "#HG /=".
    iSpecialize ("H1" with "HG"); iSpecialize ("H2" with "HG").
    iPoseProof (interp_env_ρ_closed with "HG") as "%". move: H => Hclρ.
    iPoseProof (interp_env_len_agree with "HG") as "%". move: H => Hlen. rewrite <-Hlen in *.
    have Hclsd: nclosed d.|[to_subst ρ] 0. by eapply fv_to_subst.
    have Hclsds: nclosed ds.|[to_subst ρ] 0. by eapply fv_to_subst.
    have Hclsc: nclosed ((l, d) :: ds).|[to_subst ρ] 0. by eapply fv_to_subst.
    iSplit.
    - destruct T1; simplify_eq; by iApply def2defs_head.
    - iApply defs_interp_mono => //; by apply dms_hasnt_map_mono.
  Qed.
End Sec.
