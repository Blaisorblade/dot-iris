(** * Semantic lemmas not used by the fundamental theorem.
Some are used in examples. *)
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D Require Import iris_prelude swap_later_impl proper.
From D.Dot Require Import rules path_repl.
From D.Dot Require Export old_fundamental dsub_lr.

Implicit Types (Σ : gFunctors).
Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms) (ρ : env) (l : label).

Set Implicit Arguments.
Unset Strict Implicit.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

Section Lemmas.
  Context `{HdotG: !dlangG Σ}.

  Lemma sP_ISub' {Γ} p T1 T2 i:
    Γ s⊨p p : T1, i -∗
    Γ s⊨ T1, i <: T2, i -∗
    (*───────────────────────────────*)
    Γ s⊨p p : T2, i.
  Proof. have := !!(@sP_ISub _ _ Γ p T1 T2 i 0). by rewrite (plusnO i). Qed.

  (** For https://github.com/lampepfl/dotty/blob/85962b19ddf4f1909189bf07b40f9a05849f9bbf/compiler/src/dotty/tools/dotc/core/TypeComparer.scala#L553. *)
  Lemma singleton_Mu_dotty_approx_0 {Γ p i T1 T2} :
    iterate TLater i (TAnd T1 (TSing (shift p))) :: Γ ⊨ T1, i <: T2, i -∗
    Γ ⊨p p : TMu T1, i -∗
    Γ ⊨ TSing p, i <: TMu T2, i.
  Proof.
    (* Demonstrate why this rule is not easy to derive.*)
    (* iIntros "Hsub Hp".
    iApply sSngl_Sub_Self.
    iApply (sP_ISub' with "Hp").
    iApply Mu_Sub_Mu.
    (* We're stuck! *)
    Restart. *)
    iIntros "#Hsub #Hp %ρ %v #Hg Heq".
    iSpecialize ("Hp" with "Hg").
    iAssert (▷^i ⟦ T1 ⟧ (v .: ρ) v)%I as "#HT1".
    by iNext i; iDestruct "Heq" as %Heq;
      rewrite (alias_paths_elim_eq _ Heq) path_wp_pv_eq.
    iApply ("Hsub" $! (v .: ρ) v with "[#$Hg] HT1").
    iEval rewrite iterate_TLater_oLater /= hsubst_comp. iFrame "Heq HT1".
  Qed.

  (** What Dotty actually checks uses substitution twice. A simple case is the following: *)
  Lemma singleton_Mu_dotty_approx_1 {Γ p i T1 T2 T1' T2'}
    (Hrepl1 : T1 .Tp[ p /]~ T1') (Hrepl2 : T2 .Tp[ p /]~ T2'):
    Γ ⊨ T1', i <: T2', i -∗
    Γ ⊨p p : TMu T1, i -∗
    Γ ⊨ TSing p, i <: TMu T2, i.
  Proof.
    iIntros "#Hsub #Hp %ρ %v #Hg /= Heq"; iSpecialize ("Hp" with "Hg").
    iSpecialize ("Hsub" $! ρ v with "[#$Hg] [#]"); iNext i;
      iDestruct "Heq" as %Heq;
      rewrite -(psubst_one_repl Hrepl1, psubst_one_repl Hrepl2) //
        (alias_paths_elim_eq _ Heq) path_wp_pv_eq //.
  Qed.

  (** Unlike [sDistr_And_Or_Sub], this is also derivable syntactically; see [iDistr_Or_And_Sub_inv]. But much easier to
  derive in the model. *)
  Lemma sDistr_Or_And_Sub_inv {Γ S T U i}:
    ⊢ Γ s⊨ oAnd (oOr S U) (oOr T U), i <: oOr (oAnd S T) U , i.
  Proof. iIntros "%% Hg [[HS|HT] [HT'|HU]] !> /="; eauto with iFrame. Qed.

  Lemma sAnd_Fld_Sub_Distr_2 Γ l T1 T2 i:
    ⊢ Γ s⊨ cVMem l (oAnd T1 T2), i <: oAnd (cVMem l T1) (cVMem l T2), i.
  Proof.
    iIntros "%ρ %v _ H"; iNext.
    iSplit; iApply (cVMem_respects_sub with "[] H"); by iIntros "%_ [??]".
  Qed.

  (* This should also follows internally from covariance, once that's proven. *)
  Lemma sAnd_Fld_Sub_Distr_Or_1 Γ l T1 T2 i:
    ⊢ Γ s⊨ oOr (cVMem l T1) (cVMem l T2), i <: cVMem l (oOr T1 T2), i.
  Proof.
    iIntros "%ρ %v _ [H|H]"; iNext;
      iApply (cVMem_respects_sub with "[] H"); iIntros "% $".
  Qed.

  Lemma sAnd_Fld_Sub_Distr_Or_2 Γ l T1 T2 i:
    ⊢ Γ s⊨ cVMem l (oOr T1 T2), i <: oOr (cVMem l T1) (cVMem l T2), i.
  Proof.
    iIntros "%ρ %v _ #H"; iNext.
    iDestruct "H" as (d Hl pmem ->) "#H"; rewrite -path_wp_or -!oDVMem_eq.
    iDestruct "H" as "#[H|H]"; [iLeft | iRight]; iExists _; iFrame (Hl) "H".
  Qed.

  Lemma sSub_Later_Sub Γ T1 T2 i j:
    Γ s⊨ T1, i.+1 <: T2, j.+1 -∗
    Γ s⊨ oLater T1, i <: oLater T2, j.
  Proof.
    iIntros "/= #Hsub %ρ %v #Hg #HT1".
    iSpecialize ("Hsub" $! _ v with "Hg").
    rewrite !swap_later.
    by iApply "Hsub".
  Qed.

  Lemma sSub_Index_Incr Γ T U i j:
    Γ s⊨ T, i <: U, j -∗
    Γ s⊨ T, i.+1 <: U, j.+1.
  Proof. iIntros "/= #Hsub ** !>". by iApply "Hsub". Qed.

  Lemma sSub_Later_Mono Γ T U i j:
    Γ s⊨ T, i <: U, j -∗
    Γ s⊨ oLater T, i <: oLater U, j.
  Proof.
    iIntros "/= #Hsub %% Hg HT". rewrite !swap_later.
    by iApply ("Hsub" with "Hg HT").
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
    iIntros "Hstp"; iApply (sSub_Trans with "[-] []").
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
    iIntros "Hstp"; iApply (sSub_Trans with "[] [-]").
    iApply Sub_Mu. by iApply Mu_Sub_Mu.
  Qed.

  Lemma sDelay_Sub {Γ T U i j}:
    Γ s⊨ T, i <: U, j -∗
    oLater <$> Γ s⊨ oLater T, i <: oLater U, j.
  Proof.
    iIntros "#Hsub %ρ %v #Hg/=".
    rewrite !swap_later -later_impl senv_TLater_commute.
    iNext. iApply ("Hsub" with "Hg").
  Qed.

  Lemma Delay_Sub {Γ T U i j}:
    Γ ⊨ T, i <: U, j -∗
    TLater <$> Γ ⊨ TLater T, i <: TLater U, j.
  Proof. by rewrite /istpi fmap_TLater_oLater sDelay_Sub. Qed.

  Lemma sSub_LaterN {Γ T} i j:
    ⊢ Γ s⊨ T, j + i <: oLaterN j T, i.
  Proof.
    elim: j T => [|j IHj] T; rewrite 1?oLaterN_0 1?oLaterN_Sr ?plusSn.
    apply sSub_Refl.
    iApply sSub_Trans; [iApply sSub_Later|iApply IHj].
  Qed.

  Lemma sLaterN_Sub {Γ T} i j :
    ⊢ Γ s⊨ oLaterN j T, i <: T, j + i.
  Proof.
    elim: j T => [|j IHj] T; rewrite 1?oLaterN_0 1?oLaterN_Sr ?plusSn.
    apply sSub_Refl.
    iApply sSub_Trans; [iApply IHj|iApply sLater_Sub].
  Qed.

  Lemma sP_LaterN {Γ i j} p T :
    Γ s⊨p p : oLaterN j T, i -∗
    Γ s⊨p p : T, i + j.
  Proof.
    rewrite comm; elim: j i => [//|j IHj] i; rewrite plus_Snm_nSm.
    by rewrite -(IHj i.+1) -sP_Later.
  Qed.

  Lemma sP_Var0 {Γ T}
    (Hx : Γ !! 0 = Some T):
    (*──────────────────────*)
    ⊢ Γ s⊨p pv (ids 0) : T, 0.
  Proof. rewrite -(hsubst_id T). apply (sP_Var Hx). Qed.

  (*
  Useful in contexts where we make [pty_interp] more opaque, such as some
  larger examples.
  *)
  Lemma uT_Obj_I Γ T ds:
    TLater T :: Γ u⊨ds ds : T -∗
    Γ u⊨ tv (vobj ds) : TMu T.
  Proof. apply suT_Obj_I. Qed.

  (* Currently unused, and irregular, even tho they do hold for unstamped semanntic typing. *)
  Lemma sT_Mu_I {Γ T v} : Γ s⊨ tv v : T.|[v/] -∗ Γ s⊨ tv v : oMu T.
  Proof. by rewrite sTMu_equiv. Qed.

  Lemma sT_Mu_E {Γ T v} : Γ s⊨ tv v : oMu T -∗ Γ s⊨ tv v : T.|[v/].
  Proof. by rewrite sTMu_equiv. Qed.

  Lemma T_Mu_I {Γ} T v: Γ ⊨ tv v : T.|[v/] -∗ Γ ⊨ tv v : TMu T.
  Proof. by rewrite /ietp -sT_Mu_I interp_subst_commute. Qed.

  Lemma T_Mu_E {Γ} T v: Γ ⊨ tv v : TMu T -∗ Γ ⊨ tv v : T.|[v/].
  Proof. by rewrite /ietp sT_Mu_E interp_subst_commute. Qed.

  Lemma suetp_var_lift1 {Γ} x T1 T2:
    (Γ s⊨ tv (ids x) : T1 -∗ Γ s⊨ tv (ids x) : T2) ⊢
    Γ su⊨ tv (ids x) : T1 -∗ Γ su⊨ tv (ids x) : T2.
  Proof.
    iIntros "#Hr #H1"; iMod (suetp_var with "H1") as "{H1} H1"; iModIntro.
    by iExists (tv (ids x)); iSplit; last iApply ("Hr" with "H1").
  Qed.

  Lemma uT_Mu_I {Γ} T x: Γ u⊨ tv (ids x) : T.|[ids x/] -∗ Γ u⊨ tv (ids x) : TMu T.
  Proof. iApply suetp_var_lift1; iApply T_Mu_I. Qed.

  Lemma uT_Mu_E {Γ} T x: Γ u⊨ tv (ids x) : TMu T -∗ Γ u⊨ tv (ids x) : T.|[ids x/].
  Proof. iApply suetp_var_lift1; iApply T_Mu_E. Qed.
End Lemmas.
