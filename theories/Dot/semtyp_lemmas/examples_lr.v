(** * Semantic lemmas not used by the fundamental theorem.
Some are used in examples. *)
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D Require Import iris_prelude succ_notation swap_later_impl proper.
From D.Dot Require Import rules path_repl unary_lr.
From D.Dot Require Import binding_lr tsel_lr tdefs_lr
  path_repl_lr sub_lr.

Implicit Types (Σ : gFunctors).
Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms) (ρ : env) (l : label).

Set Implicit Arguments.
Unset Strict Implicit.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

Section Lemmas.
  Context `{HdotG: !dlangG Σ}.

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
    iIntros "#Hsub #Hp !> %ρ %v #Hg #Heq".
    iSpecialize ("Hp" with "Hg").
    iAssert (▷^i ⟦ T1 ⟧ (v .: ρ) v)%I as "#HT1".
    by iNext i; iDestruct "Heq" as %Heq;
      rewrite (alias_paths_elim_eq _ Heq) path_wp_pv_eq.
    iApply ("Hsub" $! (v .: ρ) v with "[$Hg] HT1").
    iEval rewrite iterate_TLater_oLater /= hsubst_comp. iFrame "Heq HT1".
  Qed.

  (** What Dotty actually checks uses substitution twice. A simple case is the following: *)
  Lemma singleton_Mu_dotty_approx_1 {Γ p i T1 T2 T1' T2'}
    (Hrepl1 : T1 .Tp[ p /]~ T1') (Hrepl2 : T2 .Tp[ p /]~ T2'):
    Γ ⊨ T1', i <: T2', i -∗
    Γ ⊨p p : TMu T1, i -∗
    Γ ⊨ TSing p, i <: TMu T2, i.
  Proof.
    iIntros "#Hsub #Hp !> %ρ %v #Hg /= #Heq".
    iSpecialize ("Hp" with "Hg").
    iSpecialize ("Hsub" $! ρ v with "[#$Hg] [#]");
      iNext i; iDestruct "Heq" as %Heq;
      rewrite -(psubst_one_repl Hrepl1, psubst_one_repl Hrepl2) //
        (alias_paths_elim_eq _ Heq) path_wp_pv_eq //.
  Qed.

  (** Unlike [sDistr_And_Or_Sub], this is also derivable syntactically; see [iDistr_Or_And_Sub_inv]. But much easier to
  derive in the model. *)
  Lemma sDistr_Or_And_Sub_inv {Γ S T U i}:
    ⊢ Γ s⊨ oAnd (oOr S U) (oOr T U), i <: oOr (oAnd S T) U , i.
  Proof. iIntros "!> %% #Hg [[HS|HT] [HT'|HU]] !> /="; eauto with iFrame. Qed.

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
    iIntros "/= !> %ρ %v #Hg #H". iNext.
    iDestruct "H" as (d? pmem?) "#H"; rewrite -path_wp_or.
    iDestruct "H" as "#[H | H]"; [> iLeft | iRight];
      repeat (iExists _; repeat iSplit => //).
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


End Lemmas.
