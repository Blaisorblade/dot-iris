(** * Semantic lemmas not used by the fundamental theorem.
Some are used in examples. *)
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D Require Import iris_prelude succ_notation swap_later_impl proper.
From D.Dot Require Import rules path_repl.
From D.Dot Require Import unary_lr later_sub_sem sub_lr fundamental.

Implicit Types (Σ : gFunctors).
Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms) (ρ : env) (l : label).

Set Implicit Arguments.
Unset Strict Implicit.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

Section Lemmas.
  Context `{HdotG: !dlangG Σ}.

  Lemma sP_Sub' {Γ} p T1 T2 i:
    Γ s⊨p p : T1, i -∗
    Γ s⊨ T1, i <: T2, i -∗
    (*───────────────────────────────*)
    Γ s⊨p p : T2, i.
  Proof. have := !!(@sP_Sub _ _ Γ p T1 T2 i 0). by rewrite (plusnO i). Qed.

  (** For https://github.com/lampepfl/dotty/blob/85962b19ddf4f1909189bf07b40f9a05849f9bbf/compiler/src/dotty/tools/dotc/core/TypeComparer.scala#L553. *)
  Lemma singleton_Mu_dotty_approx_0 {Γ p i T1 T2} :
    iterate TLater i (TAnd T1 (TSing (shift p))) :: Γ ⊨ T1, i <: T2, i -∗
    Γ ⊨p p : TMu T1, i -∗
    Γ ⊨ TSing p, i <: TMu T2, i.
  Proof.
    (* Demonstrate why this rule is not easy to derive.*)
    (* iIntros "Hsub Hp".
    iApply Sngl_Sub_Self.
    iApply (sP_Sub' with "Hp").
    iApply Mu_Sub_Mu.
    (* We're stuck! *)
    Restart. *)
    iIntros "#Hsub #Hp !> %ρ %v #Hg Heq".
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
    iIntros "#Hsub #Hp !> %ρ %v #Hg /= Heq"; iSpecialize ("Hp" with "Hg").
    iSpecialize ("Hsub" $! ρ v with "[#$Hg] [#]"); iNext i;
      iDestruct "Heq" as %Heq;
      rewrite -(psubst_one_repl Hrepl1, psubst_one_repl Hrepl2) //
        (alias_paths_elim_eq _ Heq) path_wp_pv_eq //.
  Qed.

  (** Unlike [sDistr_And_Or_Sub], this is also derivable syntactically; see [iDistr_Or_And_Sub_inv]. But much easier to
  derive in the model. *)
  Lemma sDistr_Or_And_Sub_inv {Γ S T U i}:
    ⊢ Γ s⊨ oAnd (oOr S U) (oOr T U), i <: oOr (oAnd S T) U , i.
  Proof. iIntros "!> %% Hg [[HS|HT] [HT'|HU]] !> /="; eauto with iFrame. Qed.

  Lemma sAnd_Fld_Sub_Distr_2 Γ l T1 T2 i:
    ⊢ Γ s⊨ cVMem l (oAnd T1 T2), i <: oAnd (cVMem l T1) (cVMem l T2), i.
  Proof.
    iIntros "/= !> %ρ %v #Hg #H". iNext.
    iDestruct "H" as (d? pmem Hlook) "H".
    rewrite -path_wp_and; iDestruct "H" as "[H1 H2]".
    iSplit; repeat (iExists _; repeat iSplit => //).
  Qed.

  (* This should also follows internally from covariance, once that's proven. *)
  Lemma sAnd_Fld_Sub_Distr_Or_1 Γ l T1 T2 i:
    ⊢ Γ s⊨ oOr (cVMem l T1) (cVMem l T2), i <: cVMem l (oOr T1 T2), i.
  Proof.
    iIntros "/= !> %ρ %v #Hg [#H| #H]"; iNext;
      iDestruct "H" as (d? pmem?) "#H"; repeat (iExists _; repeat iSplit => //);
      rewrite -path_wp_or; by [iLeft | iRight].
  Qed.

  Lemma sAnd_Fld_Sub_Distr_Or_2 Γ l T1 T2 i:
    ⊢ Γ s⊨ cVMem l (oOr T1 T2), i <: oOr (cVMem l T1) (cVMem l T2), i.
  Proof.
    iIntros "!> %ρ %v _ #H"; iNext.
    iDestruct "H" as (d Hl pmem ->) "#H"; rewrite -path_wp_or -!oDVMem_eq.
    iDestruct "H" as "#[H|H]"; [iLeft | iRight]; iExists _; iFrame (Hl) "H".
  Qed.

  Lemma sSub_Later_Sub Γ T1 T2 i j:
    Γ s⊨ T1, S i <: T2, S j -∗
    Γ s⊨ oLater T1, i <: oLater T2, j.
  Proof.
    iIntros "/= #Hsub !> %ρ %v #Hg #HT1".
    iSpecialize ("Hsub" $! _ v with "Hg").
    rewrite !swap_later.
    by iApply "Hsub".
  Qed.

  Lemma sSub_Index_Incr Γ T U i j:
    Γ s⊨ T, i <: U, j -∗
    Γ s⊨ T, S i <: U, S j.
  Proof. iIntros "/= #Hsub !> ** !>". by iApply "Hsub". Qed.

  Lemma sSub_Later_Mono Γ T U i j:
    Γ s⊨ T, i <: U, j -∗
    Γ s⊨ oLater T, i <: oLater U, j.
  Proof.
    iIntros "/= #Hsub !> %% Hg HT". rewrite !swap_later.
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

  Lemma sSub_Skolem_T {Γ T1 T2 i}:
    oLaterN i (shift T1) :: Γ s⊨ tv (ids 0) : shift T2 -∗
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
    iIntros "#Hsub !> %ρ %v #Hg/=".
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

  Lemma sP_Later {Γ} p T i :
    Γ s⊨p p : oLater T, i -∗
    Γ s⊨p p : T, S i.
  Proof.
    rewrite (sP_Sub (j := 1) (T1 := oLater T) (T2 := T)) !(plus_comm i 1).
    iIntros "Hsub"; iApply "Hsub"; iApply sLater_Sub.
  Qed.

  Lemma sP_LaterN {Γ i j} p T :
    Γ s⊨p p : oLaterN j T, i -∗
    Γ s⊨p p : T, i + j.
  Proof.
    rewrite comm; elim: j i => [//|j IHj] i; rewrite plus_Snm_nSm.
    by rewrite -(IHj (S i)) -sP_Later.
  Qed.

  Lemma sT_Var0 {Γ T}
    (Hx : Γ !! 0 = Some T):
    (*──────────────────────*)
    ⊢ Γ s⊨ tv (ids 0) : T.
  Proof. rewrite -(hsubst_id T). apply (sT_Var Hx). Qed.
End Lemmas.
