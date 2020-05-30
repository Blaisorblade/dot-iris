(** * Binding-related semantic typing lemmas. *)
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D Require Import swap_later_impl proper.
From D.Dot Require Import rules unary_lr typing_aux_defs later_sub_sem.

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms) (ρ : env).

Set Suggest Proof Using.
Set Default Proof Using "Type*".

Section LambdaIntros.
  Context `{HdlangG: !dlangG Σ}.

  Lemma sT_All_I_Strong {Γ Γ'} T1 T2 e
    (Hctx : s⊨G Γ <:* oLater <$> Γ') :
    shift T1 :: Γ' s⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ s⊨ tv (vabs e) : oAll T1 T2.
  Proof.
    rewrite Hctx; iIntros "#HeT !> %ρ #HG /= !>".
    rewrite -wp_value'. iExists _; iSplit; first done.
    iIntros "!>" (v) "#Hv"; rewrite up_sub_compose.
    (* Factor ▷ out of [sG⟦ Γ ⟧* ρ] before [iNext]. *)
    rewrite senv_TLater_commute. iNext.
    iApply ("HeT" $! (v .: ρ) with "[$HG]").
    by rewrite hoEnvD_weaken_one.
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
  Context `{HdlangG: !dlangG Σ}.

  (* An inverse of subsumption: subtyping is *equivalent* to convertibility
  for values. *)
  Lemma sSub_Skolem_P {Γ T1 T2 i j}:
    oLaterN i (shift T1) :: Γ s⊨p pv (ids 0) : shift T2, j -∗
    (*───────────────────────────────*)
    Γ s⊨ T1, i <: T2, j.
  Proof.
    iIntros "#Htyp !> %ρ %v #Hg #HvT1".
    iEval rewrite -path_wp_pv_eq.
    iApply ("Htyp" $! (v .: ρ) with "[$Hg ]").
    by iApply "HvT1".
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

  Lemma sP_Var {Γ x τ}
    (Hx : Γ !! x = Some τ):
    (*──────────────────────*)
    ⊢ Γ s⊨p pv (ids x) : shiftN x τ, 0.
  Proof.
    iIntros "/= !> %ρ #Hg"; rewrite path_wp_pv_eq.
    by rewrite s_interp_env_lookup // id_subst.
  Qed.

  Lemma P_Var {Γ x τ}
    (Hx : Γ !! x = Some τ):
    (*──────────────────────*)
    ⊢ Γ ⊨p pv (ids x) : shiftN x τ, 0.
  Proof.
    rewrite /iptp (interp_subst_commute τ (ren (+x))). apply sP_Var.
    by rewrite list_lookup_fmap Hx.
  Qed.

  Lemma sT_Path {Γ τ p} :
    Γ s⊨p p : τ, 0 -∗ Γ s⊨ path2tm p : τ.
  Proof.
    iIntros "#Hep !> %ρ #Hg /="; rewrite path2tm_subst.
    by iApply (path_wp_to_wp with "(Hep Hg)").
  Qed.

  Lemma T_Path {Γ T p} :
    Γ ⊨p p : T, 0 -∗ Γ ⊨ path2tm p : T.
  Proof. apply sT_Path. Qed.

  Lemma T_Var {Γ x τ}
    (Hx : Γ !! x = Some τ):
    (*──────────────────────*)
    ⊢ Γ ⊨ of_val (ids x) : shiftN x τ.
  Proof. by iApply (T_Path (p := pv _)); iApply P_Var. Qed.

  Lemma sT_And_I Γ v T1 T2:
    Γ s⊨ tv v : T1 -∗
    Γ s⊨ tv v : T2 -∗
    Γ s⊨ tv v : oAnd T1 T2.
  Proof.
    iIntros "#HT1 #HT2 /= !> %ρ #Hg".
    iApply (wp_and_val with "(HT1 Hg) (HT2 Hg)").
  Qed.

  Lemma sT_Sub {Γ e T1 T2 i}:
    Γ s⊨ e : T1 -∗
    Γ s⊨ T1, 0 <: T2, i -∗
    (*───────────────────────────────*)
    Γ s⊨ iterate tskip i e : T2.
  Proof.
    iIntros "/= #HeT1 #Hsub !> %ρ #Hg !>".
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
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma sTMu_equiv {Γ T v} : (Γ s⊨ tv v : oMu T) ≡ (Γ s⊨ tv v : T.|[v/]).
  Proof.
    iSplit; iIntros "#Htp !> %ρ #Hg !> /=";
    iDestruct (wp_value_inv' with "(Htp Hg)") as "{Htp} Hgoal";
    by rewrite -wp_value /= hoEnvD_subst_one.
  Qed.

  Lemma sT_Mu_I {Γ T v} : Γ s⊨ tv v : T.|[v/] -∗ Γ s⊨ tv v : oMu T.
  Proof. by rewrite sTMu_equiv. Qed.

  Lemma sT_Mu_E {Γ T v} : Γ s⊨ tv v : oMu T -∗ Γ s⊨ tv v : T.|[v/].
  Proof. by rewrite sTMu_equiv. Qed.

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
    iIntros "/= #He1 #Hv2Arg !> * #Hg !>"; iSpecialize ("Hv2Arg" with "Hg").
    smart_wp_bind (AppLCtx (tv v2.[_])) v "#Hr {He1 Hg}" ("He1" with "Hg").
    iDestruct "Hr" as (t ->) "#HvFun".
    rewrite wp_value_inv' -wp_pure_step_later; last done.
    iSpecialize ("HvFun" with "Hv2Arg"); iNext.
    iApply (wp_wand with "HvFun"); iIntros (v) "{HvFun Hv2Arg} H".
    by rewrite /= hoEnvD_subst_one.
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
    iIntros "/= #He1 #Hv2 !> %ρ #HG !>".
    smart_wp_bind (AppLCtx (e2.|[_])) v "#Hr" ("He1" with "[]").
    smart_wp_bind (AppRCtx v) w "#Hw" ("Hv2" with "[]").
    iDestruct "Hr" as (t ->) "#Hv".
    rewrite -wp_pure_step_later // -wp_mono /=; first by iSpecialize ("Hv" with "Hw"); iNext.
    iIntros (v); by rewrite /= (hoEnvD_weaken_one T2 _ _ _).
  Qed.

  Lemma T_All_E {Γ e1 e2 T1 T2} :
    Γ ⊨ e1 : TAll T1 (shift T2) -∗ Γ ⊨ e2 : T1 -∗ Γ ⊨ tapp e1 e2 : T2.
  Proof. by rewrite /ietp -sT_All_E -(interp_subst_commute T2 (ren (+1))). Qed.

  Lemma sT_Obj_E {Γ e T l}:
    Γ s⊨ e : cVMem l T -∗
    (*─────────────────────────*)
    Γ s⊨ tproj e l : T.
  Proof.
    iIntros "#HE /= !> %ρ #HG !>".
    smart_wp_bind (ProjCtx l) v "#Hv {HE}" ("HE" with "[]").
    iDestruct "Hv" as (? Hl pmem ->) "Hv".
    by rewrite -wp_pure_step_later //= path_wp_to_wp.
  Qed.

  Lemma T_Obj_E {Γ e T l}: Γ ⊨ e : TVMem l T -∗ Γ ⊨ tproj e l : T.
  Proof. apply sT_Obj_E. Qed.
End Sec.
