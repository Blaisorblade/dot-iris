From iris.proofmode Require Import tactics.

From D.Dot.lr Require Import unary_lr.
From D.Dot.syn Require Import syn pathrepl.

Implicit Types
         (T : ty) (v w : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (Γ : ctx) (vs : vls) (l : label).

Implicit Types (Pv : vl → Prop).
Set Nested Proofs Allowed.

(* Useful ???*)
Lemma psubst_path_eq p q r: psubst_path p q r =
  match (decide (r = p)) with
  | left _ => q
  | _ =>
    match r with
    | pv _ => r
    | pself r' l => pself (psubst_path p q r') l
    end
  end.
Proof. by case: r. Qed.

Definition path_wp_purel {Σ} p Pv : iProp Σ := (⌜path_wp_pure p Pv⌝%I : iProp Σ).
Global Arguments path_wp_purel /.

Section path_repl.
  Context `{dlangG Σ}.
  Implicit Types (φ: vl → iProp Σ).

  Notation alias_paths p q ρ := (@alias_paths Σ p q ρ).
(*
  Lemma and_equivI {PROP : sbi} (P1 P2 Q1 Q2 : PROP) :
    P1 ≡ P2 ⊢@{PROP} Q1 ≡ Q2 -∗
    (P1 ∧ Q1) ≡ (P2 ∧ Q2).
  Proof.
  Admitted. *)

  (* Notation path_wp_purel p Pv := (@path_wp_purel Σ p Pv). *)
  Lemma alias_paths_symm p q ρ :
    alias_paths p q ρ -∗ alias_paths q p ρ.
  Proof. iIntros "!%". exact: alias_paths_pure_symm. Qed.

  Lemma alias_paths_elim_eq' φ p q ρ:
    alias_paths p q ρ ⊢
    ⌜path_wp p.|[ρ] φ ≡ path_wp q.|[ρ] φ⌝.
  Proof. iIntros "!%". apply alias_paths_elim_eq. Qed.

  Lemma alias_paths_elim_wand φ p q ρ:
    alias_paths_pure p q ρ →
    path_wp p.|[ρ] φ ⊢ path_wp q.|[ρ] φ.
  Proof. iIntros (->%(alias_paths_elim_eq φ)) "$". Qed.
  Lemma alias_paths_elim_wand' φ p q ρ:
    alias_paths p q ρ ⊢
    path_wp p.|[ρ] φ -∗ path_wp q.|[ρ] φ.
  Proof. iIntros (->%(alias_paths_elim_wand φ)) "$". Qed.


  Lemma rewrite_tsel_psubst2 p q l ρ v r:
    alias_paths p r ρ ⊢
    ⟦ TSel q l ⟧ ρ v ≡ ⟦ TSel (q .p[ p := r ]) l ⟧ ρ v.
  Proof. exact: path_replacement_equiv'. Qed.

  (* That's false, as we don't know that q terminates from the hyp. *)
  (* Lemma path_replacement_equiv_0 {p r ρ} q:
    alias_paths p r ρ ⊢@{iPropI Σ}
    alias_paths q (q .p[p := r]) ρ.
  Proof.
    elim: q => [w | q IHq l] /=; case_decide; simplify_eq/=.
    - by iIntros.
    - rewrite -alias_paths_refl_vl. by iIntros.
    - by iIntros.
    - rewrite /= IHq !alias_paths_eq /=.
      iDestruct 1 as (vr) "#[Hq Hqr]".
      (* We don't know that [pself q l] terminates! *)
  Abort. *)

  (* Lemma rewrite_ty_path_repl'_slow p q T1 T2 ρ v:
    T1 ~p[ p := q ] T2 →
    ⌜alias_paths_pure p q ρ⌝ ⊢@{iPropI Σ} (* p : q.type *)
    ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v.
  Proof.
    move => Hrew; move: v ρ.
    induction Hrew => v ρ;
      iIntros "/= #H"; iProperness; last
      iApply path_replacement_equiv';
      try by [|iApply IHHrew; rewrite ?alias_path_pure_weaken].
  Qed. *)


      (* rewrite -?exists_equivI; iIntros; rewrite -?f_equiv.
    1-2: rewrite -forall_equivI; iIntros (w).
    by iRewrite (IHHrew w with "H").
    rewrite -f_equiv -wp_equivI; iIntros.
    1-2: by iApply IHHrew; rewrite // hsubst_comp subst_comp ren_scons.
    all: rewrite -exists_equivI; iIntros (w); rewrite -!f_equiv.
    by iRewrite (IHHrew w with "H").
    rewrite -?and2_equivI.
    rewrite -f_equiv.
    all: rewrite -forall_equivI; iIntros (v0); by iRewrite (IHHrew v0 with "H").
  Qed. *)
      (* rewrite -f_equiv -wp_equivI; iIntros.

       iApply "H".
    (* iDestruct 1 as (t Heq) "#H1"; iExists t; iSplit; first done; iIntros "!>!>" (w) "#Ha"; *)
      by iRewrite (IHHrew w with "H").
      iApply internal_eq_proper. exist_proper.
    f_equiv.
    properness.
    iDestruct 1 as "H1".
    iDestruct 1 as (t Heq) "H1". iExists t; iSplit; first done; iIntros "!>!>" (w) "#Ha"; iApply "H1"; by iApply IHHrew. *)

    (* move HE: (pv vr) => q Hrew.
    iInduction Hrew as [] "IHHrew" forall (v ρ vr HE); subst q;
      last iApply rewrite_tsel_psubst2; iIntros "/= #H";
      try by iRewrite ("IHHrew" $! v with "[//] H").
      try by iRewrite ("IHHrew" with "[//] H").
       iApply prop_ext; iModIntro; iSplit. *)

(* Axiom skip: forall a, a. *)
  (* Special cases, any use? *)
  (* Lemma path_replacement_equiv_special {p vr ρ} q (φ : vl → iProp Σ):
    path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) ⊢@{iPropI Σ}
    path_wp q.|[ρ] φ ≡ path_wp (q .p[p := pv vr]).|[ρ] φ.
  Proof. rewrite -path_replacement_equiv' -simpl_alias_1.
  by iIntros "!%". Qed.

  Lemma rewrite_tsel_psubst2_special p q l ρ v vr:
    path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) ⊢@{iPropI Σ}
    ⟦ TSel q l ⟧ ρ v ≡ ⟦ TSel (q .p[ p := pv vr ]) l ⟧ ρ v.
  Proof. exact: path_replacement_equiv_special. Qed. *)

  (* Lemma rewrite_ty_path_repl p T1 T2 ρ v vr:
    T1 ~p[ p := pv vr ] T2 →
    path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) ⊢@{iPropI Σ}
    □(⟦ T1 ⟧ ρ v ∗-∗ ⟦ T2 ⟧ ρ v).
  Proof.
    (* V1: gets type error at Qed, due to [dependent induction]. *)
    intros Hrew; move: v ρ; dependent induction Hrew => v ρ;
    (* V2 *)
    (* move HE: (pv vr) => q; move => Hrew; move: v ρ vr HE. induction Hrew => v ρ vr HE; subst q; *)
      last apply skip; iIntros "/= #H !>"; iSplit.
    1-4: iIntros "[??]"; iFrame; by iApply IHHrew.
    1-4: iIntros "[?|?]"; iFrame; by (iLeft + iRight); iApply IHHrew.
    1-2: iIntros "? !>"; by iApply IHHrew.
    1-2: iDestruct 1 as (t Heq) "#H1"; iExists t; iSplit; first done; iIntros "!>!>" (w) "#Ha"; iApply "H1"; by iApply IHHrew.
    1-2: iDestruct 1 as (t Heq) "#H1"; iExists t; iSplit; first done; iIntros "!>!>" (w) "#Ha";
      iApply (wp_wand with "(H1 Ha)").
    1-4: iIntros; iApply IHHrew; rewrite // hsubst_comp subst_comp ren_scons; iApply "H".
    1-2: iDestruct 1 as (d Hl vm Heq) "H1"; iExists d; iSplit; first done; iExists vm; iSplit; first done; by iApply IHHrew.
    1-4: iDestruct 1 as (d Hl ψ) "[Hl #[HL HU]]"; iExists d; iSplit; first done; iExists ψ; iSplit; first done; iModIntro; iSplit; iIntros.
      1-8: try ((iApply "HL" || iApply "HU"); by [iApply IHHrew|]).
      1-2: iApply IHHrew; by [iApply "HL"|iApply "HU"|].
  Qed. *)

  (* Looks very false. *)
  (* Lemma swap_substs p q r ρ: (q .p[ p := r ]).|[ren ρ] = q.|[ren ρ] .p[ p.|[ren ρ] := r.|[ren ρ]].
  Proof.
    induction q eqn:Heq; cbn; case_decide; try by simplify_eq/=; rewrite 1?decide_True.
    case_decide => //=.
    rewrite H1. f_equal.
    simplify_eq/=.
  elim: q => /= [v | q IHq l]; case_decide; simplify_eq/=; try by rewrite 1?decide_True.

  rewrite decide_False; simplify_eq/=. done. naive_solver. congruence. *)
End path_repl.
