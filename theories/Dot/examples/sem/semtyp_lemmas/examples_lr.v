(** * Semantic lemmas not used by the fundamental theorem.
Some are used in examples. *)
From iris.proofmode Require Import tactics.

From D Require Import iris_prelude swap_later_impl.
From D.Dot Require Import rules path_repl.
From D.Dot Require Export dot_semtypes dsub_lr sub_lr binding_lr.

Implicit Types (Σ : gFunctors).
Implicit Types (v : vl) (e : tm) (d : dm) (ds : dms) (ρ : env) (l : label).

Set Implicit Arguments.
Unset Strict Implicit.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

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
    rewrite Nat.add_comm; elim: j i => [//|j IHj] i; rewrite plus_Snm_nSm.
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
