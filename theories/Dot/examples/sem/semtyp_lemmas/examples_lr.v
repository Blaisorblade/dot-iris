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

  Lemma sP_LaterN {Γ i j} p T :
    Γ s⊨p p : oLaterN j T, i -∗
    Γ s⊨p p : T, i + j.
  Proof.
    rewrite Nat.add_comm; elim: j i => [//|j IHj] i; rewrite plus_Snm_nSm.
    by rewrite -(IHj i.+1) -sP_Later.
  Qed.

  Lemma sP_Var0 {Γ T}
    (Hx : Γ !! 0 = Some T):
    (*──────────────────────*)
    ⊢ Γ s⊨p pv (ids 0) : T, 0.
  Proof. rewrite -(hsubst_id T). apply (sP_Var Hx). Qed.

  Lemma sStp_Skolem_P' {Γ T1 T2 i} `{!SwapPropI Σ} :
    oLaterN i (shift T1) :: Γ s⊨p pv (ids 0) : shift T2, i  -∗
    (*───────────────────────────────*)
    Γ s⊨ T1 <:[i] T2.
  Proof.
    have := !!sStp_Skolem_P (Γ := Γ) (T1 := T1) (T2 := T2) (i := i) (j := 0).
    rewrite plusnO oLaterN_0. apply.
  Qed.

  (** For https://github.com/lampepfl/dotty/blob/85962b19ddf4f1909189bf07b40f9a05849f9bbf/compiler/src/dotty/tools/dotc/core/TypeComparer.scala#L553. *)
  Lemma singleton_Mu_dotty_approx_0 {Γ p i T1 T2} `{SwapPropI Σ} :
    iterate TLater i (TAnd T1 (TSing (shift p))) :: Γ ⊨ T1, i <: T2, i -∗
    Γ ⊨p p : TMu T1, i -∗
    Γ ⊨ TSing p, i <: TMu T2, i.
  Proof.
    (* Demonstrate why this rule is not easy to derive.*)
    (* rewrite /istpi -!sstpd_to_sstpi; iIntros "Hsub Hp".
    iApply sSngl_Stp_Self.
    iApply (sP_Sub with "Hp").
    iApply Mu_Stp_Mu.
    (* We're stuck! *)
    Restart.
    rewrite /istpi -!sstpd_to_sstpi; iIntros "#Hsub #Hp".
    iApply sStp_Trans. {
      iApply sStp_And.
      - iApply (sSngl_Stp_Self with "Hp").
      - iApply sStp_Refl.
    }
    iApply sStp_Skolem_P'.
    iApply sP_Sub. { iApply (sP_LaterN (i := 0)). by iApply sP_Var0. }
    rewrite fmap_cons iterate_TLater_oLater.
    (* We're stuck again! *)
    Fail iApply "Hsub".
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

  (*
     Γ, z: T₁ᶻ ⊨ T₁ᶻ <: T₂
     ----------------------------------------------- (<:-Bind-1)
     Γ ⊨ μ (x: T₁ˣ) <: T₂
  *)
  (* Derive this rule from Mu_Stp_Mu and Mu_Stp. *)
  Lemma Stp_Bind_1 {Γ T1 T2 i} `{SwapPropI Σ} :
    iterate TLater i T1 :: Γ ⊨ T1 <:[i] shift T2 -∗
    Γ ⊨ TMu T1 <:[i] T2.
  Proof.
    iIntros "Hstp"; iApply (sStp_Trans with "[-] []").
    by iApply Mu_Stp_Mu. iApply Mu_Stp.
  Qed.

  (*
     Γ, z: T₁ᶻ ⊨ T₁ <: T₂ᶻ
     ----------------------------------------------- (<:-Bind-2)
     Γ ⊨ T₁ <: μ(x: T₂ˣ)
  *)
  Lemma Stp_Bind_2 {Γ T1 T2 i} `{SwapPropI Σ} :
    iterate TLater i (shift T1) :: Γ ⊨ shift T1 <:[i] T2 -∗
    Γ ⊨ T1 <:[i] TMu T2.
  Proof.
    iIntros "Hstp"; iApply (sStp_Trans with "[] [-]").
    iApply Stp_Mu. by iApply Mu_Stp_Mu.
  Qed.

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
