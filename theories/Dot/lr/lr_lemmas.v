From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D Require Import swap_later_impl proper.
From D.Dot Require Import rules unary_lr typing_aux_defs later_sub_sem.

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms) (ρ : env).

Set Suggest Proof Using.
Set Default Proof Using "Type*".

Section LambdaIntros.
  Context `{HdlangG: dlangG Σ}.

  Lemma sT_All_I_Strong {Γ Γ'} T1 T2 e
    (Hctx : s⊨G Γ <:* oLater <$> Γ') :
    shift T1 :: Γ' s⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ s⊨ tv (vabs e) : oAll T1 T2.
  Proof.
    rewrite Hctx; iIntros "#HeT !>" (ρ) "#HG /= !>".
    rewrite -wp_value'. iExists _; iSplit; first done.
    iIntros "!>" (v) "#Hv"; rewrite up_sub_compose.
    (* Factor ▷ out of [s⟦ Γ ⟧* ρ] before [iNext]. *)
    rewrite senv_TLater_commute. iNext.
    iApply ("HeT" $! (v .: ρ) with "[$HG]").
    by rewrite (hoEnvD_weaken_one T1 vnil _ v) stail_eq.
  Qed.

  Lemma sT_All_I {Γ} T1 T2 e:
    shift T1 :: Γ s⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ s⊨ tv (vabs e) : oAll T1 T2.
  Proof.
    apply sT_All_I_Strong => ρ. rewrite senv_TLater_commute. by iIntros "$".
  Qed.

  Lemma T_All_I_Strong {Γ Γ'} T1 T2 e
    (Hctx : ⊨G Γ <:* TLater <$> Γ') :
    shift T1 :: Γ' ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    rewrite /ietp fmap_cons (interp_subst_commute T1 (ren (+1))).
    rewrite -(sT_All_I_Strong (Γ' := V⟦Γ'⟧*)) // => ρ.
    by rewrite -fmap_TLater_oLater.
  Qed.
End LambdaIntros.

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  (* An inverse of subsumption: subtyping is *equivalent* to convertibility
  for values. *)
  Lemma sSub_Skolem_P {Γ T1 T2 i j}:
    iterate oLater i (shift T1) :: Γ s⊨p pv (ids 0) : shift T2, j -∗
    (*───────────────────────────────*)
    Γ s⊨ T1, i <: T2, j.
  Proof.
    iIntros "#Htyp !>" (ρ v) "#Hg #HvT1".
    iEval rewrite -path_wp_pv_eq.
    iApply ("Htyp" $! (v .: ρ) with "[$Hg ]").
    by rewrite iterate_oLater_later; iApply "HvT1".
  Qed.

  Lemma sSub_Skolem_P' Γ T1 T2:
    shift T1 :: Γ s⊨p pv (ids 0) : shift T2, 0 -∗
    (*───────────────────────────────*)
    Γ s⊨ T1, 0 <: T2, 0.
  Proof. apply (sSub_Skolem_P (i := 0)). Qed.

  Lemma Sub_Skolem_P {Γ T1 T2 i j}:
    iterate TLater i (shift T1) :: Γ ⊨p pv (ids 0) : shift T2, j -∗
    (*───────────────────────────────*)
    Γ ⊨ T1, i <: T2, j.
  Proof.
    rewrite /iptp fmap_cons iterate_TLater_oLater !interp_subst_commute.
    exact: sSub_Skolem_P.
  Qed.

  Lemma sSub_Skolem_T {Γ T1 T2 i}:
    iterate oLater i (shift T1) :: Γ s⊨ tv (ids 0) : shift T2 -∗
    (*───────────────────────────────*)
    Γ s⊨ T1, i <: T2, 0.
  Proof. by rewrite sP_Val sSub_Skolem_P. Qed.

  Lemma Sub_Skolem_T {Γ T1 T2 i}:
    iterate TLater i (shift T1) :: Γ ⊨ tv (ids 0) : shift T2 -∗
    (*───────────────────────────────*)
    Γ ⊨ T1, i <: T2, 0.
  Proof.
    rewrite /istpi/ietp -sSub_Skolem_T fmap_cons iterate_TLater_oLater.
    by rewrite (interp_subst_commute T1) (interp_subst_commute T2).
  Qed.

  Lemma sDelay_Sub {Γ T U i j}:
    Γ s⊨ T, i <: U, j -∗
    oLater <$> Γ s⊨ oLater T, i <: oLater U, j.
  Proof.
    iIntros "#Hsub !>" (ρ v) "#Hg/=".
    rewrite !swap_later -later_impl senv_TLater_commute.
    iNext. iApply ("Hsub" with "Hg").
  Qed.

  Lemma Delay_Sub {Γ T U i j}:
    Γ ⊨ T, i <: U, j -∗
    TLater <$> Γ ⊨ TLater T, i <: TLater U, j.
  Proof. by rewrite /istpi fmap_TLater_oLater sDelay_Sub. Qed.

  Lemma sT_Var {Γ x τ}
    (Hx : Γ !! x = Some τ):
    (*──────────────────────*)
    Γ s⊨ of_val (ids x) : shiftN x τ.
  Proof.
    iIntros "/= !>" (ρ) "#Hg"; rewrite -wp_value'.
    by rewrite s_interp_env_lookup // id_subst.
  Qed.

  Lemma T_Var {Γ x τ}
    (Hx : Γ !! x = Some τ):
    (*──────────────────────*)
    Γ ⊨ of_val (ids x) : shiftN x τ.
  Proof.
    rewrite /ietp (interp_subst_commute τ (ren (+x))). apply sT_Var.
    by rewrite list_lookup_fmap Hx.
  Qed.

  Lemma sT_Sub {Γ e T1 T2 i}:
    Γ s⊨ e : T1 -∗
    Γ s⊨ T1, 0 <: T2, i -∗
    (*───────────────────────────────*)
    Γ s⊨ iterate tskip i e : T2.
  Proof.
    iIntros "/= #HeT1 #Hsub !>" (ρ) "#Hg !>".
    rewrite tskip_subst -wp_bind.
    iApply (wp_wand with "(HeT1 Hg)").
    iIntros (v) "#HvT1".
    (* We can swap ▷^i with WP (tv v)! *)
    rewrite -wp_pure_step_later // -wp_value.
    by iApply "Hsub".
  Qed.

  Lemma T_Sub {Γ e T1 T2 i}:
    Γ ⊨ e : T1 -∗ Γ ⊨ T1, 0 <: T2, i -∗ Γ ⊨ iterate tskip i e : T2.
  Proof. apply sT_Sub. Qed.

  (*
     x ∉ fv T
     ----------------------------------------------- (<:)
     Γ ⊨ mu x: T <: T    Γ ⊨ T <: mu(x: T)
  *)

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂ᶻ
     ----------------------------------------------- (<:-μ-X)
     Γ ⊨ μ (x: T₁ˣ) <: μ(x: T₂ˣ)
  *)
  Lemma sMu_Sub_Mu {Γ T1 T2 i j} :
    iterate oLater i T1 :: Γ s⊨ T1, i <: T2, j -∗
    Γ s⊨ oMu T1, i <: oMu T2, j.
  Proof.
    iIntros "/= #Hstp !>" (vs v) "#Hg #HT1".
    iApply ("Hstp" $! (v .: vs) v with "[# $Hg] [#//]").
    by rewrite iterate_oLater_later.
  Qed.

  (** Novel subtyping rules. [Sub_Bind_1] and [Sub_Bind_2] become
  derivable. *)
  Lemma sMu_Sub {Γ T i} : Γ s⊨ oMu (shift T), i <: T, i.
  Proof. iIntros "!> **". by rewrite oMu_shift. Qed.

  Lemma sSub_Mu {Γ T i} : Γ s⊨ T, i <: oMu (shift T), i.
  Proof. iIntros "!> **". by rewrite oMu_shift. Qed.

  (*
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma sTMu_equiv {Γ T v} : (Γ s⊨ tv v : oMu T) ≡ (Γ s⊨ tv v : T.|[v/]).
  Proof.
    iSplit; iIntros "#Htp !>" (vs) "#Hg !> /=";
    iDestruct (wp_value_inv' with "(Htp Hg)") as "{Htp} Hgoal";
    rewrite -wp_value/= (hoEnvD_subst_one _ v (v.[vs])); done.
  Qed.

  Lemma sT_Mu_I {Γ T v} : Γ s⊨ tv v : T.|[v/] -∗ Γ s⊨ tv v : oMu T.
  Proof. by rewrite sTMu_equiv. Qed.

  Lemma sT_Mu_E {Γ T v} : Γ s⊨ tv v : oMu T -∗ Γ s⊨ tv v : T.|[v/].
  Proof. by rewrite sTMu_equiv. Qed.

  Lemma Mu_Sub_Mu {Γ} T1 T2 i j:
    iterate TLater i T1 :: Γ ⊨ T1, i <: T2, j -∗
    Γ ⊨ TMu T1, i <: TMu T2, j.
  Proof.
    rewrite /istpi -sMu_Sub_Mu.
    by rewrite fmap_cons (iterate_TLater_oLater i T1).
  Qed.

  Lemma Mu_Sub {Γ} T i: Γ ⊨ TMu (shift T), i <: T, i.
  Proof.
    rewrite /istpi; cbn -[sstpi].
    rewrite (interp_subst_commute T (ren (+1))).
    apply sMu_Sub.
    (* iIntros "!>" (vs v) "**".
    by rewrite /= (lift_olty_eq (interp_subst_commute _ _)). *)
  Qed.

  Lemma Sub_Mu {Γ} T i: Γ ⊨ T, i <: TMu (shift T), i.
  Proof.
    rewrite /istpi; cbn -[sstpi].
    rewrite (interp_subst_commute T (ren (+1))).
    apply sSub_Mu.
    (* iIntros "!>" (vs v) "**".
    by rewrite /= (lift_olty_eq (interp_subst_commute _ _)). *)
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂
     ----------------------------------------------- (<:-Bind-1)
     Γ ⊨ μ (x: T₁ˣ) <: T₂
  *)
  (* Derive this rule from Mu_Sub_Mu and Mu_Sub. *)
  Lemma Sub_Bind_1 {Γ T1 T2 i j} :
    iterate TLater i T1 :: Γ ⊨ T1, i <: shift T2, j -∗
    Γ ⊨ TMu T1, i <: T2, j.
  Proof.
    iIntros "Hstp"; iApply (Sub_Trans with "[-] []").
    by iApply Mu_Sub_Mu. iApply Mu_Sub.
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ <: T₂ᶻ
     ----------------------------------------------- (<:-Bind-2)
     Γ ⊨ T₁ <: μ(x: T₂ˣ)
  *)
  Lemma Sub_Bind_2 {Γ T1 T2 i j} :
    iterate TLater i (shift T1) :: Γ ⊨ (shift T1), i <: T2, j -∗
    Γ ⊨ T1, i <: TMu T2, j.
  Proof.
    iIntros "Hstp"; iApply (Sub_Trans with "[] [-]").
    iApply Sub_Mu. by iApply Mu_Sub_Mu.
  Qed.

  Lemma T_Mu_I {Γ} T v: Γ ⊨ tv v : T.|[v/] -∗ Γ ⊨ tv v : TMu T.
  Proof. by rewrite /ietp -sT_Mu_I interp_subst_commute. Qed.

  Lemma T_Mu_E {Γ} T v: Γ ⊨ tv v : TMu T -∗ Γ ⊨ tv v : T.|[v/].
  Proof. by rewrite /ietp sT_Mu_E interp_subst_commute. Qed.

  Lemma sT_All_Ex {Γ e1 v2 T1 T2}:
    Γ s⊨ e1: oAll T1 T2 -∗
    Γ s⊨ tv v2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ s⊨ tapp e1 (tv v2) : T2.|[v2/].
  Proof.
    iIntros "/= #He1 #Hv2Arg !> * #HG !>".
    smart_wp_bind (AppLCtx (tv v2.[_])) v "#Hr {He1}" ("He1" with "[#//]").
    iDestruct "Hr" as (t ->) "#HvFun".
    rewrite -wp_pure_step_later; last done.
    iSpecialize ("HvFun" with "[#]"). {
      rewrite -wp_value_inv'. by iApply ("Hv2Arg" with "[]").
    }
    iNext. iApply wp_wand.
    - iApply "HvFun".
    - iIntros (v) "{HG HvFun Hv2Arg} H".
      rewrite /= (hoEnvD_subst_one T2 v2 v) //.
  Qed.

  Lemma T_All_Ex {Γ e1 v2 T1 T2}:
    Γ ⊨ e1: TAll T1 T2 -∗ Γ ⊨ tv v2 : T1 -∗ Γ ⊨ tapp e1 (tv v2) : T2.|[v2/].
  Proof. by rewrite /ietp (interp_subst_commute T2 (v2 .: ids)) -sT_All_Ex. Qed.

  Lemma sT_All_E {Γ e1 e2 T1 T2}:
    Γ s⊨ e1 : oAll T1 (shift T2) -∗
    Γ s⊨ e2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ s⊨ tapp e1 e2 : T2.
  Proof.
    iIntros "/= #He1 #Hv2 !>" (vs) "#HG !>".
    smart_wp_bind (AppLCtx (e2.|[_])) v "#Hr" ("He1" with "[]").
    smart_wp_bind (AppRCtx v) w "#Hw" ("Hv2" with "[]").
    iDestruct "Hr" as (t ->) "#Hv".
    rewrite -wp_pure_step_later // -wp_mono /=; first by iSpecialize ("Hv" with "Hw"); iNext.
    iIntros (v); by rewrite /= (hoEnvD_weaken_one T2 _ _ _).
  Qed.

  Lemma T_All_E {Γ e1 e2 T1 T2} :
    Γ ⊨ e1 : TAll T1 (shift T2) -∗ Γ ⊨ e2 : T1 -∗ Γ ⊨ tapp e1 e2 : T2.
  Proof. by rewrite /ietp -sT_All_E -(interp_subst_commute T2 (ren (+1))). Qed.

  Lemma sFld_Sub_Fld' {Γ T1 T2 i j l}:
    Γ s⊨ T1, i <: T2, j + i -∗
    Γ s⊨ cVMem l T1, i <: cVMem l T2, j + i.
  Proof.
    iIntros "#Hsub /= !>" (ρ v) "#Hg #HT1". setoid_rewrite laterN_plus.
    iDestruct "HT1" as (d) "#[Hdl #HT1]".
    iExists d; repeat iSplit => //.
    iDestruct "HT1" as (pmem) "[Heq HvT1]".
    iExists pmem; repeat iSplit => //; rewrite !path_wp_eq.
    iDestruct "HvT1" as (w) "[Hv HvT1]"; iExists w; iFrame "Hv".
    by iApply "Hsub".
  Qed.

  Lemma Fld_Sub_Fld' {Γ T1 T2 i j l}:
    Γ ⊨ T1, i <: T2, j + i -∗ Γ ⊨ TVMem l T1, i <: TVMem l T2, j + i.
  Proof. apply sFld_Sub_Fld'. Qed.

  Lemma Fld_Sub_Fld {Γ T1 T2 i l}:
    Γ ⊨ T1, i <: T2, i -∗ Γ ⊨ TVMem l T1, i <: TVMem l T2, i.
  Proof. iApply (Fld_Sub_Fld' (j := 0)). Qed.

  (* Stronger variant of [sT_Obj_E]. *)
  Lemma sT_Obj_E' {Γ e T l}:
    Γ s⊨ e : cVMem l (oLater T) -∗
    (*─────────────────────────*)
    Γ s⊨ tproj e l : T.
  Proof.
    iIntros "#HE /= !>" (ρ) "#HG !>".
    smart_wp_bind (ProjCtx l) v "#Hv {HE}" ("HE" with "[]").
    iDestruct "Hv" as (? Hl pmem ->) "Hv".
    rewrite -wp_pure_step_later //= path_wp_later_swap path_wp_to_wp. by [].
  Qed.

  Lemma sT_Obj_E {Γ e T l}:
    Γ s⊨ e : cVMem l T -∗
    (*─────────────────────────*)
    Γ s⊨ tproj e l : T.
  Proof.
    rewrite -sT_Obj_E'. iIntros "HE"; iApply (sT_Sub (i := 0) with "HE").
    rewrite -(sFld_Sub_Fld' (j := 0)).
    (* iApply Sub_Add_Later. *)
    by iIntros "!> ** !> /=".
  Qed.

  Lemma T_Obj_E {Γ e T l}: Γ ⊨ e : TVMem l T -∗ Γ ⊨ tproj e l : T.
  Proof. apply sT_Obj_E. Qed.
End Sec.

Section swap_based_typing_lemmas.
  Context `{!dlangG Σ} `{!SwapPropI Σ}.

  Lemma sAll_Sub_All {Γ T1 T2 U1 U2 i}:
    Γ s⊨ oLater T2, i <: oLater T1, i -∗
    iterate oLater (S i) (shift T2) :: Γ s⊨ oLater U1, i <: oLater U2, i -∗
    Γ s⊨ oAll T1 U1, i <: oAll T2 U2, i.
  Proof.
    rewrite iterate_S /=.
    iIntros "#HsubT #HsubU /= !>" (ρ v) "#Hg #HT1".
    iDestruct "HT1" as (t) "#[Heq #HT1]". iExists t; iSplit => //.
    iIntros (w).
    rewrite -!mlaterN_pers -mlaterN_impl.
    iIntros "!> #HwT2".
    iSpecialize ("HsubT" $! ρ w with "Hg HwT2").
    iSpecialize ("HsubU" $! (w .: ρ)); iEval (rewrite -forall_swap_impl) in "HsubU".
    iSpecialize ("HsubU" with "[# $Hg]").
    by rewrite iterate_oLater_later -swap_later /=; iApply hoEnvD_weaken_one.
    setoid_rewrite mlaterN_impl; setoid_rewrite mlater_impl.
    iNext i; iNext 1. iModIntro. iApply wp_wand.
    - iApply ("HT1" with "[]"). iApply "HsubT".
    - iIntros (u) "#HuU1". by iApply "HsubU".
  Qed.

  Lemma All_Sub_All {Γ} T1 T2 U1 U2 i:
    Γ ⊨ TLater T2, i <: TLater T1, i -∗
    iterate TLater (S i) (shift T2) :: Γ ⊨ TLater U1, i <: TLater U2, i -∗
    Γ ⊨ TAll T1 U1, i <: TAll T2 U2, i.
  Proof.
    rewrite /istpi fmap_cons iterate_TLater_oLater.
    rewrite (interp_subst_commute T2 (ren (+1))).
    apply sAll_Sub_All.
  Qed.

  Lemma sTyp_Sub_Typ' {Γ L1 L2 U1 U2 i j l}:
    Γ s⊨ oLater L2, j + i <: oLater L1, i -∗
    Γ s⊨ oLater U1, i <: oLater U2, i -∗
    Γ s⊨ cTMem l L1 U1, i <: cTMem l L2 U2, i.
  Proof.
    iIntros "#IHT #IHT1 /= !>" (ρ v) "#Hg #HT1".
    iDestruct "HT1" as (d) "[Hl2 H]".
    iDestruct "H" as (φ) "#[Hφl [HLφ #HφU]]".
    rewrite (comm plus).
    setoid_rewrite laterN_plus; setoid_rewrite mlaterN_impl.
    iExists d; repeat iSplit; first by iNext.
    iExists φ; repeat iSplitL; first by [iNext];
      rewrite -!mlaterN_pers;
      iIntros "!>" (w);
      iSpecialize ("IHT" $! ρ w with "Hg");
      iSpecialize ("IHT1" $! ρ w with "Hg");
      iNext i; iIntros.
    - iApply "HLφ" => //. by iApply "IHT".
    - iApply "IHT1". by iApply "HφU".
  Qed.

  Lemma sTyp_Sub_Typ {Γ L1 L2 U1 U2 i l}:
    Γ s⊨ oLater L2, i <: oLater L1, i -∗
    Γ s⊨ oLater U1, i <: oLater U2, i -∗
    Γ s⊨ cTMem l L1 U1, i <: cTMem l L2 U2, i.
  Proof. apply (sTyp_Sub_Typ' (j := 0)). Qed.

  Lemma Typ_Sub_Typ {Γ L1 L2 U1 U2 i l}:
    Γ ⊨ TLater L2, i <: TLater L1, i -∗
    Γ ⊨ TLater U1, i <: TLater U2, i -∗
    Γ ⊨ TTMem l L1 U1, i <: TTMem l L2 U2, i.
  Proof. apply sTyp_Sub_Typ. Qed.
End swap_based_typing_lemmas.
