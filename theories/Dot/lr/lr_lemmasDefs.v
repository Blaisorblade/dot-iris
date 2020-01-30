From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).
(* (L T U V: ty) *)
Section Sec.
  Context `{HdlangG: dlangG Σ}.

  Local Hint Resolve dms_lookup_head dms_lookup_mono : core.
  Local Arguments lift_dinterp_dms: simpl never.

  Lemma lift_dinterp_dms_vl_commute T ds ρ l:
    label_of_ty T = Some l →
    lift_dinterp_dms ld⟦T⟧ ρ (selfSubst ds) -∗
    lift_dinterp_vl l d*⟦T⟧ vnil ρ (vobj ds).
  Proof.
    rewrite /lift_dinterp_dms /=. iIntros (?).
    iDestruct 1 as (?l d ?) "[% H]"; simplify_eq/=.
    iExists d; iFrame. by iExists ds.
  Qed.

  Lemma lift_dsinterp_dms_vl_commute T ds ρ:
    ds⟦T⟧ ρ (selfSubst ds) -∗
    ⟦T⟧ ρ (vobj ds).
  Proof.
    iIntros "H".
    iInduction T as [] "IHT";
      try iDestruct "H" as (???) "[_[]]"; first done.
    - iDestruct "H" as "[#H1 #H2]".
      by iSplit; [> iApply "IHT"| iApply "IHT1"].
    - by rewrite (lift_dinterp_dms_vl_commute (TVMem _ _)).
    - by rewrite (lift_dinterp_dms_vl_commute (TTMem _ _ _)).
  Qed.

  Lemma def2defs_head {T l ρ d ds}:
    d[ l ]⟦T⟧ ρ d -∗
    lift_dinterp_dms ld⟦T⟧ ρ ((l, d) :: ds).
  Proof. iIntros; iExists l, d. auto. Qed.

  Lemma lift_dinterp_dms_mono T l ρ d ds:
    dms_hasnt ds l →
    lift_dinterp_dms T ρ ds -∗
    lift_dinterp_dms T ρ ((l, d) :: ds).
  Proof.
    intros ?. iDestruct 1 as (l' d' ?) "#H".
    iExists l', d'. iSplit; auto.
  Qed.

  Lemma defs_interp_mono T l ρ d ds:
    dms_hasnt ds l →
    defs_interp T ρ ds -∗
    defs_interp T ρ ((l, d) :: ds).
  Proof.
    iIntros (Hlds) "HT".
    iInduction T as [] "IHT" => //=;
      try by [iDestruct "HT" as (????) "?" | iApply lift_dinterp_dms_mono].
    iDestruct "HT" as "[HT1 HT2]"; iSplit; by [>iApply "IHT"|iApply "IHT1"].
  Qed.

  Local Arguments lift_dinterp_vl: simpl never.
  (* Local Arguments ldlty_car: simpl never. *)
  (* Local Arguments def_interp_tmem: simpl never.
  Local Arguments def_interp_vmem: simpl never. *)

  (** This lemma is equivalent to pDOT's (Def-New). *)
  Lemma D_New_Mem_I Γ T l ds:
    TAnd (TLater T) (TSing (pself (pv (ids 1)) l)) :: Γ ⊨ds ds : T -∗
    Γ ⊨ { l := dpt (pv (vobj ds)) } : TVMem l (TMu T).
  Proof.
    iDestruct 1 as (Hwf) "#Hds"; iIntros "!>" (ρ Hpid) "#Hg"; cbn.
    rewrite def_interp_tvmem_eq path_wp_pv /=.
    iLöb as "IH".
    iApply lift_dsinterp_dms_vl_commute.
    rewrite norm_selfSubst.
    have Hs := path_includes_self ds ρ Hwf.
    iApply ("Hds" $! (vobj _ .: ρ) Hs with "[$IH $Hg]"); iIntros "!%".
    (* rewrite shead_eq /=. *)
    apply (path_includes_field_aliases (pv (var_vl 0)) ρ l (vobj ds) Hpid).
    (* move: Hpid; apply path_includes_field_aliases. *)
    (* exact: (path_includes_field_aliases (pv (var_vl 0)) ρ _ (vobj ds)). *)
  Qed.

  Context Γ.

  Lemma D_TVMem_Sub T1 T2 p l:
    Γ ⊨ T1, 0 <: T2, 0 -∗
    Γ ⊨ { l := dpt p } : TVMem l T1 -∗
    Γ ⊨ { l := dpt p } : TVMem l T2.
  Proof.
    iIntros "/= #Hsub #Hv !>" (ρ Hpid) "#Hg".
    iSpecialize ("Hv" $! ρ Hpid with "Hg").
    rewrite !def_interp_tvmem_eq.
    iApply (path_wp_wand with "Hv"); iIntros "!> **".
    by iApply ("Hsub" with "Hg").
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
    iDestruct 1 as (Hwf) "#Hds"; iIntros "!>" (ρ) "#Hg /= !>".
    rewrite -wp_value'.
    iLöb as "IH".
    iApply lift_dsinterp_dms_vl_commute.
    rewrite norm_selfSubst.
    have Hs := path_includes_self ds ρ Hwf.
    iApply ("Hds" $! (vobj _ .: ρ) Hs). by iFrame "IH Hg".
  Qed.

  Lemma DNil_I : Γ ⊨ds [] : TTop.
  Proof. by iSplit; last iIntros "!> **". Qed.

  Lemma DCons_I d ds l T1 T2:
    dms_hasnt ds l →
    Γ ⊨ { l := d } : T1 -∗ Γ ⊨ds ds : T2 -∗
    Γ ⊨ds (l, d) :: ds : TAnd T1 T2.
  Proof.
    iIntros (Hlds) "#HT1 [% #HT2]"; iSplit.
    by iIntros "!%"; cbn; constructor => //; by rewrite -dms_hasnt_notin_eq.
    iIntros "!>" (ρ [Hpid Hpids]%path_includes_split) "#Hg"; cbn.
    iSpecialize ("HT1" $! _  Hpid with "Hg"). iPoseProof "HT1" as (Hl) "_".
    iDestruct ("HT2" $! _  Hpids with "Hg") as "{HT2} HT2".
    repeat iSplit.
    - destruct T1; simplify_eq; iApply (def2defs_head with "HT1").
    - iApply (defs_interp_mono with "HT2"); by [apply dms_hasnt_subst | eapply nclosed_sub_app].
  Qed.
End Sec.
