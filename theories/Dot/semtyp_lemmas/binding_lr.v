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
    rewrite Hctx; iIntros ">HeT !> %ρ Hg /=".
    rewrite -wp_value'. iExists _; iSplit; first done.
    iIntros (v) "Hv"; rewrite up_sub_compose.
    (* Factor ▷ out of [sG⟦ Γ ⟧* ρ] before [iNext]. *)
    rewrite senv_TLater_commute. iNext.
    iApply ("HeT" $! (v .: ρ) with "[Hv $Hg]").
    by rewrite /= hoEnvD_weaken_one.
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

  Lemma sT_SkipN Γ e T i :
    Γ s⊨ e : oLaterN i T -∗
    Γ s⊨ iterate tskip i e : T.
  Proof.
    iIntros ">#He !> %ρ #Hg"; rewrite tskip_subst; iApply wp_bind.
    wp_wapply "(He Hg)"; iIntros "{He} /= %v Hv".
    by wp_pure.
  Qed.

  Lemma sT_Skip Γ e T :
    Γ s⊨ e : oLater T -∗ Γ s⊨ tskip e : T.
  Proof. have := sT_SkipN Γ e T 1. rewrite iterate_S iterate_0. apply. Qed.

  Lemma sT_Sub {Γ e T1 T2}:
    Γ s⊨ e : T1 -∗
    Γ s⊨ T1 <:[0] T2 -∗
    (*───────────────────────────────*)
    Γ s⊨ e : T2.
  Proof.
    iIntros ">HeT1 >Hsub !> %ρ #Hg".
    wp_wapply "(HeT1 Hg)".
    iIntros (v) "HvT1 /=".
    iApply ("Hsub" with "Hg HvT1").
  Qed.

  (*
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma sTMu_equiv {Γ T v} : (Γ s⊨ tv v : oMu T) ≡ (Γ s⊨ tv v : T.|[v/]).
  Proof.
    iSplit; iIntros ">#Htp !> %ρ #Hg /=";
    iDestruct (wp_value_inv' with "(Htp Hg)") as "{Htp} Hgoal";
    by rewrite -wp_value /= hoEnvD_subst_one.
  Qed.

  Lemma sT_All_Ex {Γ e1 v2 T1 T2}:
    Γ s⊨ e1: oAll T1 T2 -∗
    Γ s⊨ tv v2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ s⊨ tapp e1 (tv v2) : T2.|[v2/].
  Proof.
    iIntros ">He1 >Hv2Arg !> %ρ #Hg".
    iSpecialize ("Hv2Arg" with "Hg"); rewrite /= wp_value_inv'.
    wp_wapply "(He1 Hg)"; iIntros "{Hg} %v /=".
    iDestruct 1 as (t ->) "HvFun"; iSpecialize ("HvFun" with "Hv2Arg").
    wp_pure. wp_wapply "HvFun"; iIntros "%v H".
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
    iIntros "/= >He1 >He2 !> %ρ #Hg".
    wp_wapply "(He1 Hg)"; iIntros "%v"; iDestruct 1 as (t ->) "Hv /=".
    wp_wapply "(He2 Hg)"; iIntros "{Hg} %w Hw /=".
    iSpecialize ("Hv" with "Hw"). wp_pure. wp_wapply "Hv".
    iIntros "%v H". by rewrite /= (hoEnvD_weaken_one T2 _ _ _).
  Qed.

  Lemma T_All_E {Γ e1 e2 T1 T2} :
    Γ ⊨ e1 : TAll T1 (shift T2) -∗ Γ ⊨ e2 : T1 -∗ Γ ⊨ tapp e1 e2 : T2.
  Proof. by rewrite /ietp -sT_All_E -(interp_subst_commute T2 (ren (+1))). Qed.

  Lemma sT_Obj_E {Γ e T l}:
    Γ s⊨ e : oVMem l T -∗
    (*─────────────────────────*)
    Γ s⊨ tproj e l : T.
  Proof.
    iIntros ">He !> %ρ Hg".
    wp_wapply "(He Hg)"; iIntros "%v /=".
    iDestruct 1 as (? Hl pmem ->) "Hv /=".
    wp_pure. by rewrite -path_wp_to_wp.
  Qed.
End Sec.
