From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D Require Import swap_later_impl.
From D.Dot Require Import rules synLemmas unary_lr.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

Section LambdaIntros.
  Context `{HdlangG: dlangG Σ}.

  Lemma T_Forall_I {Γ} T1 T2 e:
    T1.|[ren (+1)] :: Γ ⊨ e : T2 -∗
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2.
  Proof.
    iIntros "/= #HeT !>" (vs) "#HG".
    rewrite -wp_value'. iExists _; iSplit; first done.
    iIntros "!> !>" (v) "#Hv"; rewrite -(decomp_s e (v .: vs)).
    iApply ("HeT" $! (v .: vs) with "[$HG]").
    by rewrite (interp_weaken_one T1 _ v).
  Qed.

  (** Lemmas about definition typing. *)
  Lemma TVMem_I {Γ} V T v l:
    V :: Γ ⊨ tv v : T -∗
    Γ |L V ⊨ { l := dvl v } : TVMem l T.
  Proof.
    iIntros "/= #Hv !>" (ρ) "[#Hg #Hw]".
    iApply def_interp_tvmem_eq.
    iNext. iApply wp_value_inv'; iApply "Hv"; by iSplit.
  Qed.
End LambdaIntros.

Section Sec.
  Context `{HdlangG: dlangG Σ} Γ.

  Lemma T_Sub e T1 T2 i:
    Γ ⊨ e : T1 -∗
    Γ ⊨ T1, 0 <: T2, i -∗
    (*───────────────────────────────*)
    Γ ⊨ iterate tskip i e : T2.
  Proof.
    iIntros "/= #HeT1 #Hsub !>" (ρ) "#Hg".
    rewrite tskip_subst -wp_bind.
    iApply (wp_wand with "(HeT1 Hg)").
    iIntros (v) "#HvT1".
    (* We can swap ▷^i with WP (tv v)! *)
    rewrite -wp_pure_step_later // -wp_value.
    by iApply "Hsub".
  Qed.

  Lemma T_Var x T:
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ ⊨ tv (ids x) : T.|[ren (+x)].
  Proof.
    iIntros (Hx) "/= !> * #Hg".
    rewrite -wp_value' interp_env_lookup; by [].
  Qed.

  (*
     x ∉ fv T
     ----------------------------------------------- (<:)
     Γ ⊨ mu x: T <: T    Γ ⊨ T <: mu(x: T)
  *)

  Lemma interp_TMu_ren T ρ v: ⟦ TMu T.|[ren (+1)] ⟧ ρ v ≡ ⟦ T ⟧ ρ v.
  Proof. by rewrite /= (interp_weaken_one T (_ .: ρ) v). Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂ᶻ
     ----------------------------------------------- (<:-μ-X)
     Γ ⊨ μ (x: T₁ˣ) <: μ(x: T₂ˣ)
  *)
  (* Notation "◁ n T ▷" := (iterate TLater n T). *)
  Lemma Sub_Mu_X T1 T2 i j:
    iterate TLater i T1 :: Γ ⊨ T1, i <: T2, j -∗
    Γ ⊨ TMu T1, i <: TMu T2, j.
  Proof.
    iIntros "/= #Hstp !>" (vs v) "#Hg #HT1".
    iApply ("Hstp" $! (v .: vs) v with "[# $Hg] [#//]").
    by rewrite iterate_TLater_later.
  Qed.

  (* Novel subtyping rules. Sub_Mu_1 and Sub_Mu_2 become (sort-of?)
  derivable. *)
  Lemma Sub_Mu_A T i: Γ ⊨ TMu T.|[ren (+1)], i <: T, i.
  Proof. iIntros "!>" (vs v) "**". by rewrite (interp_TMu_ren T vs v). Qed.

  Lemma Sub_Mu_B T i: Γ ⊨ T, i <: TMu T.|[ren (+1)], i.
  Proof. iIntros "!>" (vs v) "**". by rewrite (interp_TMu_ren T vs v). Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂
     ----------------------------------------------- (<:-Mu-1)
     Γ ⊨ μ (x: T₁ˣ) <: T₂
  *)
  (* Sort-of-show this rule is derivable from Sub_Mu_X and Sub_Mu_A. *)
  Lemma Sub_Mu_1 T1 T2 i j:
    iterate TLater i T1 :: Γ ⊨ T1, i <: T2.|[ren (+1)], j -∗
    Γ ⊨ TMu T1, i <: T2, j.
  Proof. iIntros "Hstp"; iApply (Sub_Trans with "[-] []"). by iApply Sub_Mu_X. iApply Sub_Mu_A. Qed.
  (*
     Γ, z: T₁ᶻ ⊨ T₁ <: T₂ᶻ
     ----------------------------------------------- (<:-Bind-2)
     Γ ⊨ T₁ <: μ(x: T₂ˣ)
  *)

  Lemma Sub_Mu_2 T1 T2 i j:
    iterate TLater i T1.|[ren (+1)] :: Γ ⊨ T1.|[ren (+1)], i <: T2, j -∗
    Γ ⊨ T1, i <: TMu T2, j.
  Proof. iIntros "Hstp"; iApply (Sub_Trans with "[] [-]"). iApply Sub_Mu_B. by iApply Sub_Mu_X. Qed.

  (*
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma TMu_equiv T v: (Γ ⊨ tv v : TMu T) ≡ (Γ ⊨ tv v : T.|[v/]).
  Proof.
    iSplit; iIntros "/= #Htp !>" (vs) "Hg";
    iDestruct (wp_value_inv with "(Htp Hg)") as "{Htp} Hgoal";
    rewrite -wp_value (interp_subst_one T v (v.[vs])); done.
  Qed.

  Lemma TMu_I T v: Γ ⊨ tv v : T.|[v/] -∗ Γ ⊨ tv v : TMu T.
  Proof. by rewrite TMu_equiv. Qed.

  Lemma TMu_E T v: Γ ⊨ tv v : TMu T -∗ Γ ⊨ tv v : T.|[v/].
  Proof. by rewrite TMu_equiv. Qed.

  Lemma T_Forall_E e1 e2 T1 T2:
    Γ ⊨ e1 : TAll T1 T2.|[ren (+1)] -∗
    Γ ⊨ e2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 e2 : T2.
  Proof.
    iIntros "/= #He1 #Hv2 !>" (vs) "#HG".
    smart_wp_bind (AppLCtx (e2.|[_])) v "#Hr" "He1".
    smart_wp_bind (AppRCtx v) w "#Hw" "Hv2".
    iDestruct "Hr" as (t ->) "#Hv".
    rewrite -wp_pure_step_later // -wp_mono /=; first by iApply "Hv".
    iIntros (v); by rewrite (interp_weaken_one T2 _ v).
  Qed.

  Lemma T_Forall_Ex e1 v2 T1 T2:
    Γ ⊨ e1: TAll T1 T2 -∗
    Γ ⊨ tv v2 : T1 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 (tv v2) : T2.|[v2/].
  Proof.
    iIntros "/= #He1 #Hv2Arg !> * #HG".
    smart_wp_bind (AppLCtx (tv v2.[_])) v "#Hr {He1}" ("He1" with "[#//]").
    iDestruct "Hr" as (t ->) "#HvFun".
    rewrite -wp_pure_step_later; last done. iNext.
    iApply wp_wand.
    - iApply "HvFun". rewrite -wp_value_inv'. by iApply "Hv2Arg".
    - iIntros (v) "{HG HvFun Hv2Arg} H".
      rewrite (interp_subst_one T2 v2 v) //.
  Qed.

  Lemma T_Mem_E e T l:
    Γ ⊨ e : TVMem l T -∗
    (*─────────────────────────*)
    Γ ⊨ tproj e l : T.
  Proof.
    iIntros "#HE /= !>" (vs) "#HG".
    smart_wp_bind (ProjCtx l) v "#Hv {HE}" "HE".
    iDestruct "Hv" as (? Hl vmem ->) "Hv".
    rewrite -wp_pure_step_later // -wp_value. by [].
  Qed.

  Lemma Sub_TVMem_Variant' T1 T2 i j l:
    Γ ⊨ TLater T1, i <: TLater T2, j + i -∗
    Γ ⊨ TVMem l T1, i <: TVMem l T2, j + i.
  Proof.
    iIntros "#Hsub /= !>" (ρ v) "#Hg #HT1". setoid_rewrite laterN_plus.
    iDestruct "HT1" as (d) "#[Hdl #HT1]".
    iExists d; repeat iSplit => //.
    iDestruct "HT1" as (vmem) "[Heq HvT1]".
    iExists vmem; repeat iSplit => //.
    by iApply "Hsub".
  Qed.

  Lemma Sub_TVMem_Variant T1 T2 i l:
    Γ ⊨ TLater T1, i <: TLater T2, i -∗
    Γ ⊨ TVMem l T1, i <: TVMem l T2, i.
  Proof. iApply (Sub_TVMem_Variant' _ _ _ 0). Qed.
End Sec.

Section swap_based_typing_lemmas.
  Context `{!dlangG Σ} {Γ} `{!SwapPropI Σ}.

  Lemma Sub_TAllConCov T1 T2 U1 U2 i:
    Γ ⊨ TLater T2, i <: TLater T1, i -∗
    iterate TLater (S i) T2.|[ren (+1)] :: Γ ⊨ TLater U1, i <: TLater U2, i -∗
    Γ ⊨ TAll T1 U1, i <: TAll T2 U2, i .
  Proof.
    rewrite iterate_S /=.
    iIntros "#HsubT #HsubU /= !>" (ρ v) "#Hg #HT1".
    iDestruct "HT1" as (t) "#[Heq #HT1]". iExists t; iSplit => //.
    iIntros (w).
    rewrite -!mlaterN_pers -mlater_wand -mlaterN_wand.
    iIntros "!> #HwT2".
    iSpecialize ("HsubT" $! ρ w with "Hg HwT2").
    iSpecialize ("HsubU" $! (w .: ρ)); iEval (rewrite -forall_swap_wand) in "HsubU".
    iSpecialize ("HsubU" with "[# $Hg]").
    by rewrite iterate_TLater_later -swap_later; iApply interp_weaken_one.
    setoid_rewrite mlaterN_wand; setoid_rewrite mlater_wand.
    iNext i; iNext 1. iApply wp_wand.
    - iApply "HT1". iApply "HsubT".
    - iIntros (u) "#HuU1". by iApply "HsubU".
  Qed.

  Lemma Sub_TTMem_Variant L1 L2 U1 U2 i l:
    Γ ⊨ TLater L2, i <: TLater L1, i -∗
    Γ ⊨ TLater U1, i <: TLater U2, i -∗
    Γ ⊨ TTMem l L1 U1, i <: TTMem l L2 U2, i.
  Proof.
    iIntros "#IHT #IHT1 /= !>" (ρ v) "#Hg #HT1".
    iDestruct "HT1" as (d) "[Hl2 H]".
    iDestruct "H" as (φ) "#[Hφl [HLφ #HφU]]".
    setoid_rewrite mlaterN_wand.
    iExists d; repeat iSplit => //.
    iExists φ; repeat iSplitL => //;
      rewrite -!mlaterN_pers;
      iIntros "!>" (w);
      iSpecialize ("IHT" $! ρ w with "Hg");
      iSpecialize ("IHT1" $! ρ w with "Hg");
      iNext; iIntros.
    - iApply "HLφ" => //. by iApply "IHT".
    - iApply "IHT1". by iApply "HφU".
  Qed.
End swap_based_typing_lemmas.
