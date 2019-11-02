From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.

Implicit Types (L T U V: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

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
    intros ?. iDestruct 1 as (l' d' ?) "#H".
    iExists l', d'. iSplit; auto.
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

  Lemma def_interp_tvmem_eq l T v ρ:
    def_interp (TVMem l T) l ρ (dvl v) ⊣⊢
    ⟦ T ⟧ ρ v.
  Proof.
    iSplit. by iDestruct 1 as (_ vmem [= ->]) "$".
    iIntros "H"; iSplit; first done; iExists v. by auto.
  Qed.

  Context Γ.

  Local Arguments lift_dinterp_vl: simpl never.
  Local Arguments lift_dinterp_dms: simpl never.
  Local Arguments def_interp_tmem: simpl never.
  Local Arguments def_interp_vmem: simpl never.

  (** Lemmas about definition typing. *)
  Lemma TVMem_I V T v l:
    TLater V :: Γ ⊨ tv v : T -∗
    Γ |L V ⊨ { l := dvl v } : TVMem l T.
  Proof.
    iIntros "/= #Hv !>" (ρ) "[#Hg #Hw]".
    iApply def_interp_tvmem_eq.
    iApply wp_value_inv'; iApply "Hv"; by iSplit.
  Qed.

  Lemma T_Forall_I' V T1 T2 e:
    T1.|[ren (+1)] :: V :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    TLater V :: Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "/= #HeT !>" (vs) "#[HG HV]".
    rewrite -wp_value'. iExists _; iSplit; first done.
    iIntros "!>" (v); rewrite -(decomp_s _ (v .: vs)).
    iIntros "!> #Hv".
    iApply ("HeT" $! (v .: vs)); rewrite (interp_weaken_one T1 _ v) stail_eq.
    by iFrame "#".
  Qed.

  Lemma TVMem_All_I V T1 T2 e l:
    T1.|[ren (+1)] :: V :: Γ ⊨ e : T2 -∗
    Γ |L V ⊨ { l := dvl (vabs e) } : TVMem l (TAll T1 T2).
  Proof.
    iIntros "/= #He !>" (ρ) "#Hg".
    iSplit => //; iExists (vabs _); iSplit => //.
    iApply wp_value_inv'.
    iApply (T_Forall_I' with "He [$Hg]").
  Qed.

  Lemma TVMem_All_I' V T1 T2 e l L:
    T1.|[ren (+1)] :: V :: Γ ⊨ e : T2 -∗
    TLater V :: Γ  ⊨ TAll T1 T2, 0 <: L, 0 -∗
    Γ |L V ⊨ { l := dvl (vabs e) } : TVMem l L.
  Proof.
    iIntros "#He #Hsub !>" (ρ); iEval (simpl); iIntros "#Hg".
    iSplit => //; iExists (vabs _); iSplit => //.
    iApply ("Hsub" with "Hg").
    iApply wp_value_inv'.
    iApply (T_Forall_I' with "He Hg").
  Qed.

  Lemma TVMem_All_I_v1 V T1 T2 e l:
    T1.|[ren (+1)] :: V :: Γ ⊨ e : T2 -∗
    Γ |L V ⊨ { l := dvl (vabs e) } : TVMem l (TAll T1 T2).
  Proof.
    iIntros "/= #He !>" (ρ) "[#Hg #Hv]".
    iApply def_interp_tvmem_eq.
    iExists (e.|[_]); iSplit; first done.
    iIntros "!>!>" (w) "#Hw"; rewrite -(decomp_s _ (w .: ρ)).
    iApply "He".
    rewrite (interp_weaken_one T1 _ w) stail_eq. by iFrame "#".
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
    Γ ⊨ { l := d } : T1 -∗ Γ ⊨ds ds : T2 -∗
    Γ ⊨ds (l, d) :: ds : TAnd T1 T2.
  Proof.
    iIntros (Hlds) "#HT1 #HT2 !>". iIntros (ρ) "#Hg /=".
    iSpecialize ("HT1" with "Hg"). iPoseProof "HT1" as (Hl) "_".
    iSplit.
    - destruct T1; simplify_eq; iApply (def2defs_head with "HT1").
    - iApply (defs_interp_mono with "(HT2 Hg)"); by [apply dms_hasnt_map_mono | eapply nclosed_sub_app].
  Qed.
End Sec.
