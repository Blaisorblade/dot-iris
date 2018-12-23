From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre.

(** Paolo to Amin: it seems below we might need something vaguely similar to the following. Not sure they're exactly true as stated. *)
Section wp_extra.
Context `{irisG Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* (** A variant of wp_wand that requires proof of [Φ v -∗ Ψ v] only if [v] is an evaluation result. *) *)
(* Lemma wp_wand_steps s E e Φ Ψ: *)
(*     (WP e @ s; E {{ v, Φ v }} -∗ *)
(*     (** The nsteps premise is wrong for a multithreaded program logic, feel free to use a more accurate one. *)
(*         This one might be fine for DOT. *) *)
(*     (∀ v σ1 κ σ2 i, ⌜ nsteps i ([e], σ1) κ ([of_val v], σ2) ⌝ -∗ Φ v -∗ Ψ v)-∗ *)
(*     WP e @ s; E {{ v, Ψ v }})%I. *)
(* Admitted. *)

End wp_extra.

From iris.program_logic Require Import lifting language ectxi_language.
From Dot Require Import tactics unary_lr rules synLemmas.
Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).
Section Sec.
  Context `{HdotG: dotG Σ} Γ.

  Lemma wp_wand_cl e Φ Ψ:
    (WP e {{ v, Φ v }} -∗ ⌜ fv_n e 0 ⌝ -∗ (∀ v, Φ v -∗ ⌜ fv_n_vl v 0 ⌝ -∗ Ψ v) -∗ WP e {{ v, Ψ v }})%I.
  Admitted.

  Lemma T_Sub e T1 T2 :
    (Γ ⊨ e : T1 →
    Γ ⊨ [T1, 0] <: [T2, 0] →
    (*───────────────────────────────*)
    Γ ⊨ e : T2)%I.
  Proof.
    iIntros "/= * #[% #HeT1] #Hsub". move: H => Hcle. iFrame "%". iIntros " !> * #Hg".
    (* match type of wp_wand with *)
    (* | ?H => let x := eval simpl in H in idtac x *)
    (* end. *)
    (* Check wp_wand. *)
    (* iApply wp_wand. *)
    iApply (wp_wand_cl (e.|[to_subst ρ]) _ (⟦ T2 ⟧ ρ)).
    3: {iIntros; iApply "Hsub" => //. }
    iApply ("HeT1" $! ρ with "Hg").
    iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen.
    iPoseProof (interp_env_ρ_closed with "Hg") as "%". move: H => Hclρ.
    iPureIntro. rewrite <- Hlen in Hcle. by apply fv_to_subst.
  Qed.

  Lemma T_Var x T:
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ ⊨ tv (var_vl x) : T.|[ren (+x)].
  Proof.
    iIntros (Hx) "/=". iSplit; eauto using lookup_fv. iIntros "!> * #Hg".
    iApply wp_value'.
    by iApply interp_env_lookup.
  Qed.

  Lemma Sub_Refl T i : Γ ⊨ [T, i] <: [T, i].
  Proof. by iIntros "/= !> **". Qed.

  Lemma Sub_Trans T1 T2 T3 i1 i2 i3 : (Γ ⊨ [T1, i1] <: [T2, i2] →
                                       Γ ⊨ [T2, i2] <: [T3, i3] →
                                       Γ ⊨ [T1, i1] <: [T3, i3])%I.
  Proof.
    iIntros "#Hsub1 #Hsub2 /= !> * % #Hg #HT".
    iApply "Hsub2" => //. by iApply "Hsub1".
  Qed.

  Lemma Sub_Mono e T i :
    (Γ ⊨ [T, i] <: [T, S i])%I.
  Proof. by iIntros "!> **". Qed.

  Lemma Later_Sub e T i :
    (Γ ⊨ [TLater T, i] <: [T, S i])%I.
  Proof. by iIntros "/= !>" (ρ v Hclv) "#HG #[Hcl HT] !>". Qed.

  Lemma Sub_Later e T i :
    (Γ ⊨ [T, S i] <: [TLater T, i])%I.
  Proof. iIntros "/= !> ** !>". naive_solver. Qed.

  Lemma Sub_Index_Incr e T U i j:
    (Γ ⊨ [T, i] <: [U, j] →
     Γ ⊨ [T, S i] <: [U, S j])%I.
  Proof. iIntros "/= #Hsub !> ** !>". by iApply "Hsub". Qed.

  Lemma T_Skip e T i:
    (Γ ⊨ e : T, S i →
     Γ ⊨ tskip e : T, i)%I.
  Proof.
    iIntros "/= [% #HT]". iSplit; auto using fv_tskip. iIntros " !> * #HG".
    iApply wp_pure_step_later; auto.
    iSpecialize ("HT" $! ρ with "HG"). by iModIntro.
  Qed.

  Lemma And1_Sub T1 T2 i: Γ ⊨ [TAnd T1 T2, i] <: [T1, i].
  Proof. by iIntros "/= !> * ? ? [? ?]". Qed.
  Lemma And2_Sub T1 T2 i: Γ ⊨ [TAnd T1 T2, i] <: [T2, i].
  Proof. by iIntros "/= !> * ? ? [? ?]". Qed.

  (* Lemma stp_andi T1 T2 ρ v: *)
  (*   ⟦T1⟧ ρ v -∗ *)
  (*   ⟦T2⟧ ρ v -∗ *)
  (*   ⟦TAnd T1 T2⟧ ρ v. *)
  (* Proof. iIntros; by iSplit. Qed. *)

  Lemma Sub_And S T1 T2 i j:
    Γ ⊨ [S, i] <: [T1, j] -∗
    Γ ⊨ [S, i] <: [T2, j] -∗
    Γ ⊨ [S, i] <: [TAnd T1 T2, j].
  Proof.
    iIntros "/= #H1 #H2 !> * #Hcl #Hg #HS".
    iSpecialize ("H1" with "Hcl Hg HS").
    iSpecialize ("H2" with "Hcl Hg HS").
    iModIntro; by iSplit.
  Qed.

  Lemma Sub_Or1 T1 T2 i: Γ ⊨ [T1, i] <: [TOr T1 T2, i].
  Proof. iIntros "/= !> ** !>"; naive_solver. Qed.
  Lemma Sub_Or2 T1 T2 i: Γ ⊨ [T2, i] <: [TOr T1 T2, i].
  Proof. iIntros "/= !> ** !>"; naive_solver. Qed.

  Lemma Or_Sub S T1 T2 i j:
    Γ ⊨ [T1, i] <: [S, j] -∗
    Γ ⊨ [T2, i] <: [S, j] -∗
    Γ ⊨ [TOr T1 T2, i] <: [S, j].
  Proof. iIntros "/= #H1 #H2 !> * #Hcl #Hg #[HT1 | HT2]"; by [iApply "H1" | iApply "H2"]. Qed.

  Lemma Sub_Top T i:
    Γ ⊨ [T, i] <: [TTop, i].
  Proof. by iIntros "!> ** /=". Qed.

  Lemma Bot_Sub T i:
    Γ ⊨ [TBot, i] <: [T, i].
  Proof. by iIntros "/= !> ** !>". Qed.

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
    iIntros "/= #Hstp !> * % #Hg #HT1".
    iApply ("Hstp" $! (v :: ρ) _);
      rewrite ?iterate_TLater_later //; by iSplit.
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂
     ----------------------------------------------- (<:-Mu-1)
     Γ ⊨ μ (x: T₁ˣ) <: T₂
  *)

  Lemma Sub_Mu_1 T1 T2 i j:
    (iterate TLater i T1 :: Γ ⊨ [T1, i] <: [T2.|[ren (+1)], j] →
     Γ ⊨ [TMu T1, i] <: [T2, j])%I.
  Proof.
    iIntros "/= #Hstp !> * % #Hg #HT1".
    iApply (interp_weaken_one v).
    iApply ("Hstp" $! (v :: ρ)); rewrite ?iterate_TLater_later //; by iSplit.
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ <: T₂ᶻ
     ----------------------------------------------- (<:-Bind-2)
     Γ ⊨ T₁ <: μ(x: T₂ˣ)
  *)
  Lemma Sub_Mu_2 T1 T2 i j:
    (iterate TLater i T1.|[ren (+1)] :: Γ ⊨ [T1.|[ren (+1)], i] <: [T2, j] →
    Γ ⊨ [T1, i] <: [TMu T2, j])%I.
  Proof.
    iIntros "/= #Hstp !> * % #Hg #HT1".
    rewrite -(interp_weaken_one v T1 ρ v).
    iApply ("Hstp" $! (_ :: _) _); rewrite ?iterate_TLater_later //; by iSplit.
  Qed.

  Lemma T_Forall_E e1 e2 T1 T2:
    (Γ ⊨ e1: TAll T1 T2.|[ren (+1)] →
     Γ ⊨ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
     Γ ⊨ tapp e1 e2 : T2)%I.
  Proof.
    iIntros "/= #[% He1] #[% Hv2]". iSplit; eauto using fv_tapp. iIntros " !> * #HG".
    smart_wp_bind (AppLCtx (e2.|[to_subst ρ])) v "#[% Hv]" "He1".
    smart_wp_bind (AppRCtx v) w "#Hw" "Hv2".
    iApply wp_mono; [|iApply "Hv"]; auto.
    iIntros (v0) "#H".
    by iApply (interp_weaken_one w).
  Qed.

  Lemma T_Forall_Ex e1 v2 T1 T2:
    (Γ ⊨ e1: TAll T1 T2 →
     Γ ⊨ tv v2 : T1 →
    (*────────────────────────────────────────────────────────────*)
     Γ ⊨ tapp e1 (tv v2) : T2.|[v2/])%I.
  Proof.
    iIntros "/= #[% He1] #[% Hv2Arg]". move: H H0 => Hcle1 Hclv2. iSplit; eauto using fv_tapp. iIntros " !> * #HG".
    (* iAssert (⌜ length ρ = length Γ ⌝)%I as "%". by iApply interp_env_len_agree. move: H => Hlen. *)
    iAssert (⌜ fv_n_vl v2 (length Γ) ⌝)%I as "%". by iPureIntro; apply fv_tv_inv. move: H => Hcl.
    (* assert (fv_n_vl v2 (length ρ)). by rewrite Hlen. *)
    smart_wp_bind (AppLCtx (tv v2.[to_subst ρ])) v "#[% HvFun]" "He1".
    iApply wp_wand.
    - iApply fupd_wp.
      iApply "HvFun".
      iApply wp_value_inv'; by iApply "Hv2Arg".
    - iIntros (v0) "#H". by iApply (interp_subst_closed _ T2 v2 v0).
  Qed.

  Lemma T_Forall_I T1 T2 e:
    (T1.|[ren (+1)] :: Γ ⊨ e : T2 →
    (*─────────────────────────*)
    Γ ⊨ tv (vabs e) : TAll T1 T2)%I.
  Proof.
    iIntros "/= #[% HeT]". move: H => Hcle.
    iSplit; eauto using fv_tv, fv_vabs.
    iIntros " !> * #HG".
    iPoseProof (interp_env_ρ_closed with "HG") as "%". move: H => Hclρ.
    iAssert (⌜ length ρ = length Γ ⌝)%I as "%". by iApply interp_env_len_agree. move: H => Hlen.
    iApply wp_value'.
    iSplit.
    { 
      iPureIntro. rewrite <- Hlen in *.
      pose proof (fv_to_subst (tv (vabs e)) ρ) as Hfv. asimpl in Hfv.
      (* apply fv_tv_inv, Hfv => //; apply fv_tv, fv_vabs, Hcle. *)
      eauto using fv_tv_inv, fv_vabs, fv_tv.
    }
    iIntros "!>" (v) "#Hv".
    iSpecialize ("HeT" $! (v :: ρ)).
    iApply wp_pure_step_later; trivial.
    asimpl.
    iApply "HeT".
    iFrame "HG".
    iNext. by iApply (interp_weaken_one v).
  Qed.

  Lemma T_Mem_E e T l:
    (Γ ⊨ e : TVMem l T →
    (*─────────────────────────*)
    Γ ⊨ tproj e l : T)%I.
  Proof.
    iIntros "#[% HE] /=". iSplit; auto using fv_tproj. iIntros " !>" (ρ) "#HG".
    smart_wp_bind (ProjCtx l) v "#[% Hv]" "HE".
    iDestruct "Hv" as (d) "[% [% Hv]]".
    iDestruct "Hv" as (vmem) "[% Hv]".
    simplOpen ds; subst.
    match goal with H: _ @ _ ↘ _ |- _ => inversion H; ev; injectHyps end.
    iApply wp_pure_step_later; eauto.
    by iApply wp_value'.
  Qed.

  (* BEWARE NONSENSE IN NOTES:
     Γ ⊨ x: Tˣ
     ----------------------------------------------- (<:)
     Γ ⊨ mu(x: Tˣ) <: Tˣ    Γ ⊨ Tˣ <: mu(x: Tˣ)

     Luckily we don't need that, all the rules that exist before appear reasonable. *)

  (*
     Γ ⊨ z: Tᶻ
     =============================================== (T-Rec-I/T-Rec-E)
     Γ ⊨ z: mu(x: Tˣ)
   *)
  Lemma ivstp_rec_eq T v:
    (ivtp Γ (TMu T) v ∗-∗
    ivtp Γ T.|[v/] v)%I.
  Proof.
    iSplit; iIntros "/= #[% #Htp]"; iSplit => //; iIntros " !> * #Hg";
    iApply interp_subst_closed => //; by iApply "Htp".
  Qed.

  Lemma ivstp_rec_i T v:
    ((∀ ρ1 ρ2, (∀ x, x < length Γ → ρ1 x = ρ2 x) → v.[ρ1] = v.[ρ2]) ->
    ivtp Γ T.|[v/] v -∗
    ivtp Γ (TMu T) v).
  Proof. by intros; iDestruct ivstp_rec_eq as "[? ?]". Qed.

  Lemma ivstp_rec_e T v:
    ((∀ ρ1 ρ2, (∀ x, x < length Γ → ρ1 x = ρ2 x) → v.[ρ1] = v.[ρ2]) ->
    ivtp Γ (TMu T) v -∗
    ivtp Γ T.|[v/] v).
  Proof. by intros; iDestruct ivstp_rec_eq as "[? ?]". Qed.

End Sec.
