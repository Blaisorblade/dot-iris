From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms).

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  Local Arguments lift_dinterp_dms: simpl never.
  Local Arguments lift_dinterp_vl: simpl never.
  (* Local Arguments ldlty_car: simpl never. *)
  (* Local Arguments def_interp_tmem: simpl never.
  Local Arguments def_interp_vmem: simpl never. *)

  (** This lemma is equivalent to pDOT's (Def-New). *)
  Lemma sD_New_Mem_I {Γ l ds} {T : ldslty Σ}:
    oAnd (oLater (ldslty_olty T)) (oSing (pself (pv (ids 1)) l)) :: Γ s⊨ds ds : T -∗
    Γ s⊨ { l := dpt (pv (vobj ds)) } : oLDVMem l (oMu (ldslty_olty T)).
  Proof.
    iDestruct 1 as (Hwf) "#Hds"; iIntros "!>" (ρ Hpid) "#Hg".
    rewrite def_interp_tvmem_eq path_wp_pv /=.
    iLöb as "IH".
    iApply ldslty_commute.
    rewrite norm_selfSubst.
    have Hs := path_includes_self ds ρ Hwf.
    iApply ("Hds" $! (vobj _ .: ρ) Hs with "[$IH $Hg]"). iIntros "!%".
    (* rewrite shead_eq /=. *)
    apply (path_includes_field_aliases (pv (var_vl 0)) ρ l (vobj ds) Hpid).
    (* move: Hpid; apply path_includes_field_aliases. *)
    (* exact: (path_includes_field_aliases (pv (var_vl 0)) ρ _ (vobj ds)). *)
  Qed.

  Lemma D_New_Mem_I Γ T l ds:
    TAnd (TLater T) (TSing (pself (pv (ids 1)) l)) :: Γ ⊨ds ds : T -∗
    Γ ⊨ { l := dpt (pv (vobj ds)) } : TVMem l (TMu T).
  Proof.
    iDestruct 1 as (Hwf) "#Hds"; iIntros "!>" (ρ Hpid) "#Hg".
    rewrite def_interp_tvmem_eq path_wp_pv /=.
    iLöb as "IH".
    iApply lift_dsinterp_dms_vl_commute. (* Only difference from proof above. *)
    rewrite norm_selfSubst.
    have Hs := path_includes_self ds ρ Hwf.
    iApply ("Hds" $! (vobj _ .: ρ) Hs with "[$IH $Hg]"). iIntros "!%".
    (* rewrite shead_eq /=. *)
    apply (path_includes_field_aliases (pv (var_vl 0)) ρ l (vobj ds) Hpid).
  Qed.

  (* Drop, syntactically admissible. *)
  Lemma D_TVMem_Sub {Γ T1 T2 p l}:
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
  Lemma sT_Obj_I (Γ : sCtx Σ) (T : ldslty Σ) ds:
     oLater (ldslty_olty T) :: Γ s⊨ds ds : T -∗
     Γ s⊨ tv (vobj ds) : oMu (ldslty_olty T).
  Proof.
    iDestruct 1 as (Hwf) "#Hds"; iIntros "!>" (ρ) "#Hg /= !>".
    rewrite -wp_value'.
    iLöb as "IH".
    iApply ldslty_commute.
    rewrite norm_selfSubst.
    have Hs := path_includes_self ds ρ Hwf.
    iApply ("Hds" $! (vobj _ .: ρ) Hs). by iFrame "IH Hg".
  Qed.

  Lemma T_Obj_I Γ T ds:
     Γ |L T ⊨ds ds : T -∗
     Γ ⊨ tv (vobj ds) : TMu T.
  Proof.
    (* rewrite /ietp /idstp. cbn -[setp sdstp].
    rewrite sT_Obj_I. *)
    iDestruct 1 as (Hwf) "#Hds"; iIntros "!>" (ρ) "#Hg /= !>".
    rewrite -wp_value'.
    iLöb as "IH".
    iApply lift_dsinterp_dms_vl_commute.
    rewrite norm_selfSubst.
    have Hs := path_includes_self ds ρ Hwf.
    iApply ("Hds" $! (vobj _ .: ρ) Hs). by iFrame "IH Hg".
  Qed.

  Lemma sD_Nil Γ : Γ s⊨ds [] : LDsTop.
  Proof. by iSplit; last iIntros "!> **". Qed.

  Lemma D_Nil Γ : Γ ⊨ds [] : TTop.
  Proof. apply sD_Nil. Qed.

  Lemma sD_Cons Γ d ds l T1 (T2 : ldsltyO Σ):
    dms_hasnt ds l →
    Γ s⊨ { l := d } : T1 -∗ Γ s⊨ds ds : T2 -∗
    Γ s⊨ds (l, d) :: ds : LDsAnd (ldlty2ldslty T1) T2.
  Proof.
    iIntros (Hlds) "#HT1 [% #HT2]"; iSplit.
    by iIntros "!%"; cbn; constructor => //; by rewrite -dms_hasnt_notin_eq.
    iIntros "!>" (ρ [Hpid Hpids]%path_includes_split) "#Hg"; cbn.
    iSpecialize ("HT1" $! _  Hpid with "Hg").
    iDestruct ("HT2" $! _  Hpids with "Hg") as "{HT2} HT2".
    (* iSplit; first by iApply sem_def2defs_head. *)
    iSplit; first by iApply (ldslty_def2defs_head (ldlty2ldslty _)).

    iApply (ldslty_mono with "HT2"); by [apply dms_hasnt_subst | eapply nclosed_sub_app].
  Qed.

  Lemma D_Cons Γ d ds l T1 T2:
    dms_hasnt ds l →
    Γ ⊨ { l := d } : T1 -∗ Γ ⊨ds ds : T2 -∗
    Γ ⊨ds (l, d) :: ds : TAnd T1 T2.
  Proof.
    (* rewrite /idstp /idtp; cbn [ldefs_interp LDsAnd] => Hlds.
    pose proof sD_Cons (V⟦ Γ ⟧* ) d ds l LD⟦ T1 ⟧ Ds⟦ T2 ⟧ Hlds.
    apply H.
    2: done. *)
  (* cbn -[sdstp sdtp]. *)

    iIntros (Hlds) "#HT1 [% #HT2]"; iSplit.
    by iIntros "!%"; cbn; constructor => //; by rewrite -dms_hasnt_notin_eq.
    iIntros "!>" (ρ [Hpid Hpids]%path_includes_split) "#Hg"; cbn.
    iSpecialize ("HT1" $! _  Hpid with "Hg").
    iDestruct ("HT2" $! _  Hpids with "Hg") as "{HT2} HT2".
    iSplit; first by iApply def2defs_head.
    iApply (ldslty_mono with "HT2"); by [apply dms_hasnt_subst | eapply nclosed_sub_app].
  Qed.
End Sec.
