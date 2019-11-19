From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.

Implicit Types (L T U V: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

Lemma norm_selfSubst ds s: selfSubst ds.|[up s] = ds.|[(vobj ds).[s] .: s].
Proof. by rewrite /selfSubst up_sub_compose. Qed.

Lemma dms_hasnt_map ds l f:
  dms_hasnt ds l →
  dms_hasnt (map (mapsnd f) ds) l.
Proof.
  elim: ds => //; rewrite /dms_hasnt/mapsnd/= => [[l' d] ds IHds H].
  by case_decide; eauto 2.
Qed.

Lemma dms_hasnt_subst l ds ρ : dms_hasnt ds l → dms_hasnt ds.|[ρ] l.
Proof. apply dms_hasnt_map. Qed.

Lemma dms_lookup_head l d ds: dms_lookup l ((l, d) :: ds) = Some d.
Proof. by cbn; case_decide. Qed.

Lemma dms_lookup_mono l l' d d' ds:
  dms_hasnt ds l →
  dms_lookup l' ds = Some d' →
  dms_lookup l' ((l, d) :: ds) = Some d'.
Proof.
  rewrite /dms_hasnt /= => Hlds Hl; by case_decide; simplify_eq.
Qed.

Lemma dms_hasnt_notin_eq l ds : dms_hasnt ds l ↔ l ∉ map fst ds.
Proof.
  elim: ds => [|[l' d] ds] /=; first by split; [inversion 2|].
  rewrite /dms_hasnt/= not_elem_of_cons => IHds. case_decide; naive_solver.
Qed.

Lemma ds_notin_subst l ds ρ :
  l ∉ map fst ds →
  l ∉ map fst ds.|[ρ].
Proof.
  (* elim: ds => [//|[l' d] ds IH]; cbn.
  rewrite !not_elem_of_cons. naive_solver. *)
  intros; by apply dms_hasnt_notin_eq, dms_hasnt_subst, dms_hasnt_notin_eq.
Qed.

Lemma wf_ds_nil : wf_ds ([] : dms). Proof. constructor. Qed.
Hint Resolve wf_ds_nil : core.

Lemma wf_ds_sub ds ρ : wf_ds ds → wf_ds ds.|[ρ].
Proof.
  elim: ds => [//=|[l d] ds IH]; cbn.
  inversion_clear 1; constructor; last by eauto.
  exact: ds_notin_subst.
Qed.

Lemma path_includes_self ds ρ : wf_ds ds → path_includes (pv (ids 0)) (vobj ds.|[up ρ] .: ρ) ds.
Proof. constructor; eexists; split_and!; by [| rewrite up_sub_compose|apply wf_ds_sub]. Qed.

Lemma path_includes_split p ρ l d ds :
  path_includes p ρ ((l, d) :: ds) →
  path_includes p ρ [(l, d)] ∧
  path_includes p ρ ds.
Proof.
  rewrite /path_includes !path_wp_pure_eq; cbn.
  intros (v & Hpw & ds' & -> & ((k1 & k2 & Hpid' & Hpids)%sublist_cons_l & Hno)).
  repeat (split_and! => //; try eexists); rewrite Hpid'.
  by apply sublist_inserts_l, sublist_skip, sublist_nil_l.
  by apply sublist_inserts_l, sublist_cons, Hpids.
Qed.

Lemma dms_has_in_eq l d ds : wf_ds ds →
  dms_has ds l d ↔ (l, d) ∈ ds.
Proof.
  rewrite /dms_has; elim: ds => [Hwf|[l' d'] ds IH /= /NoDup_cons [Hni Hwf]];
    first by split; [|inversion 1].
  rewrite elem_of_cons; case_decide; last naive_solver; split; first naive_solver.
  destruct 1; simplify_eq/=; try naive_solver.
  destruct Hni.
  by eapply elem_of_list_In, (in_map fst ds (_,_)), elem_of_list_In.
Qed.

Lemma dms_lookup_sublist l p ds :
  wf_ds ds → [(l, dvl p)] `sublist_of` ds →
  dms_lookup l ds = Some (dvl p).
Proof.
  rewrite sublist_cons_l; intros Hwf ?; ev; simplify_eq/=.
  apply dms_has_in_eq; [done|].
  rewrite elem_of_app elem_of_cons. naive_solver.
Qed.

Lemma path_includes_field_aliases p ρ l v :
  path_includes p ρ [(l, dvl (pv v))] →
  alias_paths (pself p.|[ρ] l) (pv v.[ρ]).
Proof.
  rewrite /path_includes/alias_paths/= !path_wp_pure_eq;
    intros (w & Hwp & ds & -> & Hsub & Hwf').
    repeat (econstructor; split_and?; try by [|constructor]).
  apply dms_lookup_sublist, Hsub. exact: wf_ds_sub.
Qed.

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  Local Hint Resolve dms_lookup_head dms_lookup_mono : core.

  Lemma lift_dinterp_dms_vl_commute T ds ρ l:
    label_of_ty T = Some l →
    lift_dinterp_dms T ρ (selfSubst ds) -∗
    lift_dinterp_vl l (def_interp_base T) ρ (vobj ds).
  Proof.
    rewrite /lift_dinterp_dms /=. iIntros (?).
    iDestruct 1 as (?l d ?) "[% H]"; simplify_eq.
    iExists d; iFrame. by iExists ds.
  Qed.

  Lemma lift_dsinterp_dms_vl_commute T ds ρ:
    defs_interp T ρ (selfSubst ds) -∗
    interp T ρ (vobj ds).
  Proof.
    iIntros "H".
    iInduction T as [] "IHT"; cbn;
      try iDestruct "H" as (???) "[_[]]"; first done.
    - iDestruct "H" as "[#H1 #H2]".
      by iSplit; [> iApply "IHT"| iApply "IHT1"].
    - by rewrite (lift_dinterp_dms_vl_commute (TVMem _ _)).
    - by rewrite (lift_dinterp_dms_vl_commute (TTMem _ _ _)).
  Qed.

  Lemma def2defs_head {T l ρ d ds}:
    def_interp T l ρ d -∗
    lift_dinterp_dms T ρ ((l, d) :: ds).
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
      try by [iDestruct "HT" as (???) "?" | iApply lift_dinterp_dms_mono].
    iDestruct "HT" as "[HT1 HT2]"; iSplit; by [>iApply "IHT"|iApply "IHT1"].
  Qed.

  Local Arguments lift_dinterp_vl: simpl never.
  Local Arguments lift_dinterp_dms: simpl never.
  Local Arguments def_interp_tmem: simpl never.
  Local Arguments def_interp_vmem: simpl never.

  (** This lemma is equivalent to pDOT's (Def-New). *)
  Lemma D_New_Mem_I Γ T l ds:
    TAnd (TLater T) (TSing (pself (pv (ids 1)) l)) :: Γ ⊨ds ds : T -∗
    Γ ⊨ { l := dvl (pv (vobj ds)) } : TVMem l (TMu T).
  Proof.
    iDestruct 1 as (Hwf) "#Hds"; iIntros "!>" (ρ Hpid) "#Hg /=".
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

  Lemma D_New_Mem_I' Γ V T l ds:
    (TLater V :: Γ) |L TAnd T (TSing (pself (pv (ids 1)) l)) ⊨ds ds : T -∗
    Γ |L V ⊨ { l := dvl (pv (vobj ds)) } : TVMem l (TMu T).
  Proof.
    iIntros "#H"; iApply D_New_Mem_I.
    iDestruct "H" as (Hwf) "#Hds". iFrame (Hwf).
    iIntros "!>" (ρ Hpid) "/= #[[??] [??]]".
    iApply ("Hds" with "[//] [$]").
  Qed.

  Context Γ.

  Lemma D_TVMem_Sub V T1 T2 p l:
    Γ |L V ⊨ T1, 0 <: T2, 0 -∗
    Γ |L V ⊨ { l := dvl p } : TVMem l T1 -∗
    Γ |L V ⊨ { l := dvl p } : TVMem l T2.
  Proof.
    iIntros "/= #Hsub #Hv !>" (ρ Hpid) "#Hg".
    iSpecialize ("Hv" $! ρ Hpid with "Hg").
    rewrite !def_interp_tvmem_eq.
    iApply (path_wp_wand with "Hv"); iIntros.
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
