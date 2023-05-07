(** * Semantic lemmas not used by the fundamental theorem.
Some are used in examples. *)
From iris.proofmode Require Import proofmode.

From D Require Import iris_prelude numbers swap_later_impl.
From D.Dot Require Import rules path_repl.
From D.Dot Require Export dot_semtypes dsub_lr sub_lr binding_lr.

Implicit Types (Σ : gFunctors).
Implicit Types (v : vl) (e : tm) (d : dm) (ds : dms) (ρ : env) (l : label).

Set Implicit Arguments.
Unset Strict Implicit.

Section Lemmas.
  Context `{HdotG : !dlangG Σ}.

  Lemma sP_ISub' {Γ} p T1 T2 i :
    Γ s⊨p p : T1, i -∗
    Γ s⊨ T1, i <: T2, i -∗
    (*───────────────────────────────*)
    Γ s⊨p p : T2, i.
  Proof. have := !!(@sP_ISub _ _ Γ p T1 T2 i 0). by rewrite (plusnO i). Qed.

  Lemma sP_LaterN {Γ i j} p T :
    Γ s⊨p p : oLaterN j T, i -∗
    Γ s⊨p p : T, i + j.
  Proof.
    rewrite Nat.add_comm; elim: j i => [//|j IHj] i; rewrite Nat_add_succ_r_l.
    by rewrite -(IHj i.+1) -sP_Later.
  Qed.

  Lemma sP_Var0 {Γ T}
    (Hx : Γ !! 0 = Some T) :
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

  (* Currently unused, and irregular, even tho they do hold for unstamped semanntic typing. *)
  Lemma sT_Mu_I {Γ T v} : Γ s⊨ tv v : T.|[v/] -∗ Γ s⊨ tv v : oMu T.
  Proof. by rewrite sTMu_equiv. Qed.

  Lemma sT_Mu_E {Γ T v} : Γ s⊨ tv v : oMu T -∗ Γ s⊨ tv v : T.|[v/].
  Proof. by rewrite sTMu_equiv. Qed.
End Lemmas.

(*

From iris Require Import later_credits.
From iris.base_logic Require Import fancy_updates.
Section foo.
  Context `{HdotG : !dlangG Σ} `{!invGS Σ}.
  Context `[!RecTyInterp Σ].
  (* Goal FUpd (iProp Σ).
  apply _. *)

  Definition sstpl i Γ (T1 T2 : olty Σ) : iProp Σ :=
    <PB> ∀ ρ v, sG⟦Γ⟧* ρ -∗ £ i -∗ oClose T1 ρ v -∗ oClose T2 ρ v.

  #[global] Arguments sstpl /.
  #[global] Instance sstpl_persistent i Γ T1 T2 : Persistent (sstpl i Γ T1 T2) := _.
  Notation "Γ s⊨ T1 <:[ i  ] T2" := (sstpl i Γ T1 T2).

  Lemma sStp_And Γ T U1 U2 i j :
    Γ s⊨ T <:[i] U1 -∗
    Γ s⊨ T <:[j] U2 -∗
    Γ s⊨ T <:[i + j] oAnd U1 U2.
  Proof.
    pupd; iIntros "#H1 #H2 !> %ρ %v #Hg [Ci Cj]".
    iSpecialize ("H1" $! ρ v with "Hg Ci"); iSpecialize ("H2" $! ρ v with "Hg Cj").
    iIntros "#H".
    iSplit; [iApply "H1" | iApply "H2"]; iApply "H".
  Qed.

  Lemma sDistr_And_Or_Stp Γ {S T U i} : ⊢ Γ s⊨ oAnd (oOr S T) U <:[i] oOr (oAnd S U) (oAnd T U).
  Proof.
    pupd; iIntros "!> %ρ %v #Hg Ci [[HS|HT] Hu] /="; [iLeft|iRight]; iFrame.
  Qed.

  Definition ofLaterN n (τ : oltyO Σ) :=
    Olty (λI args ρ v, □ |={⊤}▷=>^n τ args ρ v).
  Notation ofLater := (ofLaterN 1).


  #[global] Instance lc_pers i : Persistent (£ i).
  Proof. Admitted.
  #[global] Instance lc_affine i : Affine (£ i).
  Proof. Admitted.
  Instance into_and_lc_add : `(IntoAnd b £ (n + m) £ n £ m).
  Proof. Admitted.

  Lemma sLater_Stp_Eq {Γ T U i} `{SwapPropI Σ} :
    Γ s⊨ T <:[i] U ⊣⊢
    Γ s⊨ ofLater T <:[i] ofLater U.
  Proof.
    iSplit; pupd. {
      iIntros "#W !> %ρ %v #Hg #Ci #V /= !>".
      iApply ("W" $! ρ v with "Hg Ci V").
    }
    iIntros "#W !> %ρ %v #Hg #Ci #V".
    iSpecialize ("W" $! ρ v with "Hg Ci").
    iSplitL. iFrame "Ci".
    admit.
    iApply (lc_fupd_elim_later with "C").
    iNext.
    later_credits
    by rewrite sstpd_delay_oLaterN_plus. Qed.


  Lemma lsTyp_Sub_Typ l i j Γ L1 L2 U1 U2 :
    Γ s⊨ L2 <:[ i ] L1 -∗
    Γ s⊨ U1 <:[ j ] U2 -∗
    Γ s⊨ oTMem l L1 U1 <:[ i + j ] oTMem l L2 U2.
  Proof.
    pupd. iIntros "#HT1 #HT2 !> %ρ %v #Hg #[Ci Cj]".
    rewrite !oTMem_eq.
    iDestruct 1 as (φ d Hl) "#[Hφl [#HLφ #HφU]]".
    iExists φ, d; iFrame (Hl) "Hφl".
    iSplitL "Ci"; iIntros "" (w) "!>".
    all: iIntros "#H".
    1: iSpecialize ("HT1" $! ρ w with "Hg Ci").
    2: iSpecialize ("HT2" $! ρ w with "Hg Cj").
    {
      iApply ("HLφ" $! w with "(HT1 H)").
    }
    iApply ("HT2" with "(HφU H)").
  Qed.


End foo.
  *)
