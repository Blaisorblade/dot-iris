From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr synLemmas rules.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

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
  Context `{HdlangG: dlangG Σ}.

  Local Hint Resolve fv_dms_cons fv_of_val fv_vobj fv_dvl dms_lookup_head dms_lookup_mono.

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
    iIntros "#H".
    iInduction T as [] "IHT"; cbn;
      try by [|iDestruct "H" as (???) "[_[]]"].
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
    iIntros (?) "#HT"; iDestruct "HT" as (l' d' ?) "#H".
    iExists l', d'; iSplit; auto.
  Qed.

  Lemma defs_interp_mono T l ρ d ds:
    dms_hasnt ds l →
    defs_interp T ρ ds -∗
    defs_interp T ρ ((l, d) :: ds).
  Proof.
    iIntros (Hlds) "#HT".
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
    Γ |L V ⊨d{ l := dvl v } : TVMem l T.
  Proof.
    iIntros "/= #Hv !>" (ρ) "[#Hg #Hw]".
    iSplit => //; iExists _; iSplit => //.
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
    iIntros "/= #Hds !>" (ρ) "#Hg /=". rewrite -wp_value'.
    iLöb as "IH".
    iApply lift_dsinterp_dms_vl_commute.
    rewrite norm_selfSubst.
    iApply ("Hds" $! (vobj _ .: ρ)); by iFrame "IH Hg".
  Qed.

  Lemma DNil_I : Γ ⊨ds [] : TTop.
  Proof. by iIntros "!> **". Qed.

  Lemma DCons_I d ds l T1 T2:
    dms_hasnt ds l →
    Γ  ⊨d{ l := d } : T1 -∗ Γ  ⊨ds ds : T2 -∗
    Γ  ⊨ds (l, d) :: ds : TAnd T1 T2.
  Proof.
    iIntros (Hlds) "#HT1 #HT2 !>". iIntros (ρ) "#Hg /=".
    iSpecialize ("HT1" with "Hg"). iPoseProof "HT1" as (Hl) "_".
    iSplit.
    - destruct T1; simplify_eq; iApply (def2defs_head with "HT1").
    - iApply (defs_interp_mono with "(HT2 Hg)"); by [apply dms_hasnt_map_mono | eapply nclosed_sub_app].
  Qed.
End Sec.
