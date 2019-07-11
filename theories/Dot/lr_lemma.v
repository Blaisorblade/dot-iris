From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D.Dot Require Import rules synLemmas unary_lr_binding step_fv.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).
Section Sec.
  Context `{HdlangG: dlangG Σ} Γ.

  Lemma wp_wand_cl e Φ Ψ:
    WP e {{ v, Φ v }} -∗ ⌜ nclosed e 0 ⌝ -∗ (∀ v, Φ v -∗ ⌜ nclosed_vl v 0 ⌝ -∗ Ψ v) -∗ WP e {{ v, Ψ v }}.
  Proof.
    iIntros "/= He" (Hcle) "Himpl". iApply (wp_wand_wf _ _ e Φ (flip nclosed 0) Hcle with "He [Himpl]").
    intros. by eapply nclosed_prim_step.
    iIntros (v Hclv) "/= H". iApply ("Himpl" with "H [%]"). exact: fv_of_val_inv.
  Qed.

  Lemma T_Sub e T1 T2 i:
    (Γ ⊨ e : T1 →
    Γ ⊨ [T1, 0] <: [T2, i] →
    (*───────────────────────────────*)
    Γ ⊨ iterate tskip i e : T2)%I.
  Proof.
    iIntros "/= #[% #HeT1] #Hsub". move: H => Hcle.
    iSplit; first by eauto using nclosed_tskip_i.
    iIntros "!>" (vs) "#Hg".
    rewrite tskip_subst tskip_n_to_fill -wp_bind.
    iApply (wp_wand_cl _ (⟦ T1 ⟧ (to_subst vs))) => //.
    - iApply ("HeT1" with "[//]").
    - by rewrite -interp_env_cl_app.
    - iIntros (v) "#HvT1 %".
      (* We can swap ▷^i with WP (tv v)! *)
      rewrite -tskip_n_to_fill -wp_pure_step_later // -wp_value.
      by iApply "Hsub".
  Qed.

  Lemma T_Var x T:
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ ⊨ tv (ids x) : T.|[ren (+x)].
  Proof.
    iIntros (Hx) "/=". iSplit; eauto using lookup_fv. iIntros "!> * #Hg".
    rewrite -wp_value' interp_env_lookup; by [].
  Qed.

  (*
     x ∉ fv T
     ----------------------------------------------- (<:)
     Γ ⊨ mu x: T <: T    Γ ⊨ T <: mu(x: T)
  *)

  Lemma interp_TMu_ren T ρ v: ⟦ TMu T.|[ren (+1)] ⟧ (to_subst ρ) v ≡ ⟦ T ⟧ (to_subst ρ) v.
  Proof. by rewrite /= (interp_weaken_one v T ρ v). Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂ᶻ
     ----------------------------------------------- (<:-μ-X)
     Γ ⊨ μ (x: T₁ˣ) <: μ(x: T₂ˣ)
  *)
  (* Notation "◁ n T ▷" := (iterate TLater n T). *)
  Lemma Sub_Mu_X T1 T2 i j:
    (iterate TLater i T1 :: Γ ⊨ [T1, i] <: [T2, j] →
     Γ ⊨ [TMu T1, i] <: [TMu T2, j])%I.
  Proof.
    iIntros "/= #Hstp !>" (vs v Hclv) "#Hg #HT1".
    iApply ("Hstp" $! (v :: vs) v with "[#//] [# $Hg] [#//]").
    by rewrite iterate_TLater_later.
  Qed.

  (* Novel subtyping rules. Sub_Mu_1 and Sub_Mu_2 become (sort-of?)
  derivable. *)
  Lemma Sub_Mu_A T i: (Γ ⊨ [TMu T.|[ren (+1)], i] <: [T, i])%I.
  Proof. iIntros "!>" (vs v Hcl) "**". by rewrite (interp_TMu_ren T vs v). Qed.

  Lemma Sub_Mu_B T i: (Γ ⊨ [T, i] <: [TMu T.|[ren (+1)], i])%I.
  Proof. iIntros "!>" (vs v Hcl) "**". by rewrite (interp_TMu_ren T vs v). Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂
     ----------------------------------------------- (<:-Mu-1)
     Γ ⊨ μ (x: T₁ˣ) <: T₂
  *)
  (* Sort-of-show this rule is derivable from Sub_Mu_X and Sub_Mu_A. *)
  Lemma Sub_Mu_1 T1 T2 i j:
    (iterate TLater i T1 :: Γ ⊨ [T1, i] <: [T2.|[ren (+1)], j] →
     Γ ⊨ [TMu T1, i] <: [T2, j])%I.
  Proof. iIntros "Hstp"; iApply (Sub_Trans with "[-] []"). by iApply Sub_Mu_X. iApply Sub_Mu_A. Qed.
  (*
     Γ, z: T₁ᶻ ⊨ T₁ <: T₂ᶻ
     ----------------------------------------------- (<:-Bind-2)
     Γ ⊨ T₁ <: μ(x: T₂ˣ)
  *)

  Lemma Sub_Mu_2 T1 T2 i j:
    (iterate TLater i T1.|[ren (+1)] :: Γ ⊨ [T1.|[ren (+1)], i] <: [T2, j] →
    Γ ⊨ [T1, i] <: [TMu T2, j])%I.
  Proof. iIntros "Hstp"; iApply (Sub_Trans with "[] [-]"). iApply Sub_Mu_B. by iApply Sub_Mu_X. Qed.

  (*
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma TMu_equiv T v: (Γ ⊨ tv v : TMu T) ≡ (Γ ⊨ tv v : T.|[v/]).
  Proof.
    iSplit; iIntros "/= #[% #Htp]"; iFrame "%"; iIntros "!>" (vs) "Hg";
    iDestruct (wp_value_inv with "(Htp Hg)") as "{Htp} Hgoal";
    rewrite -wp_value (interp_subst_closed T v (v.[to_subst vs])); done.
  Qed.

  Lemma TMu_I T v: Γ ⊨ tv v : T.|[v/] -∗ Γ ⊨ tv v : TMu T.
  Proof. by rewrite TMu_equiv. Qed.

  Lemma TMu_E T v: Γ ⊨ tv v : TMu T -∗ Γ ⊨ tv v : T.|[v/].
  Proof. by rewrite TMu_equiv. Qed.

  Lemma T_Forall_E e1 e2 T1 T2:
    (Γ ⊨ e1 : TAll T1 T2.|[ren (+1)] →
     Γ ⊨ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
     Γ ⊨ tapp e1 e2 : T2)%I.
  Proof.
    iIntros "/= [% #He1] #[% Hv2]". iSplit; eauto using fv_tapp. iIntros "!>" (vs) "#HG".
    smart_wp_bind (AppLCtx (e2.|[_])) v "#[_ Hr]" "He1".
    smart_wp_bind (AppRCtx v) w "#Hw" "Hv2".
    iDestruct "Hr" as (t ->) "#Hv".
    rewrite -wp_pure_step_later // -wp_mono /=; first by iApply "Hv".
    iIntros (v); by rewrite (interp_weaken_one w T2 vs v).
  Qed.

  Lemma T_Forall_Ex e1 v2 T1 T2:
    (Γ ⊨ e1: TAll T1 T2 →
     Γ ⊨ tv v2 : T1 →
    (*────────────────────────────────────────────────────────────*)
     Γ ⊨ tapp e1 (tv v2) : T2.|[v2/])%I.
  Proof.
    iIntros "/= [% #He1] [% #Hv2Arg]". move: H H0 => Hcle1 Hclv2. iSplit; eauto using fv_tapp. iIntros " !> * #HG".
    move: Hclv2 => /fv_of_val_inv Hclv2.
    smart_wp_bind (AppLCtx (tv v2.[_])) v "[_ #Hr] {He1}" ("He1" with "[#//]").
    iDestruct "Hr" as (t ->) "#HvFun".
    rewrite -wp_pure_step_later; last done. iNext.
    iApply wp_wand.
    - iApply "HvFun". rewrite -wp_value_inv'. by iApply "Hv2Arg".
    - iIntros (v) "{HG HvFun Hv2Arg} H".
      rewrite (interp_subst_closed T2 v2 v) //.
  Qed.

  (** Restricting this to index 0 appears necessary: it seems we can't swap [▷^i
      (∀ v, P v)] to [∀ v, ▷^i (P v)] (at least, tactics don't do this swap).
      We'd need this swap, and then [iIntros (v)], to specialize the hypothesis
      and drop the [▷^i] modality.*)
  Lemma T_Forall_I T1 T2 e:
    (T1.|[ren (+1)] :: Γ ⊨ e : T2 →
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2)%I.
  Proof.
    iIntros "/= #[% #HeT]". move: H => Hcle.
    iSplit; eauto using fv_of_val, fv_vabs.
    iIntros " !>" (vs) "#HG".
    rewrite -wp_value'.
    iSplit.
    {
      apply fv_vabs in Hcle.
      by iApply (interp_env_cl_app_vl (vabs e) Hcle).
    }
    iExists _; iSplitL; first done.
    iIntros "!> !>" (v) "#Hv /=".
    iSpecialize ("HeT" $! (v :: vs) with "[$HG]").
    by rewrite (interp_weaken_one v T1 vs v).
    (* time locAsimpl. (* 10x faster than asimpl. *) *)
    (* 20x faster than asimpl. *)
    by cbn; locAsimpl' (e.|[_].|[_]).
  Qed.

  Lemma T_Mem_E e T l:
    (Γ ⊨ e : TVMem l T →
    (*─────────────────────────*)
    Γ ⊨ tproj e l : T)%I.
  Proof.
    iIntros "#[% #HE] /=". iSplit; auto using fv_tproj. iIntros " !>" (vs) "#HG".
    smart_wp_bind (ProjCtx l) v "#[% Hv] {HE}" "HE".
    iDestruct "Hv" as (? Hl vmem ->) "Hv".
    rewrite -wp_pure_step_later // -wp_value. by [].
  Qed.


End Sec.
