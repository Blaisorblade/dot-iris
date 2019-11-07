From D.Dot.syn Require Import syn.

Implicit Types
         (T : ty) (v : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (Γ : ctx) (vs : vls) (l : label).

Reserved Notation "r .p[ p := q  ]" (at level 65).
Definition psubst_path p q : path → path := fix F r :=
  match (decide (r = p)) with
  | left _ => q
  | _ =>
    match r with
    | pv _ => r (* XXX no, values can contain paths! OTOH, pDOT path replacement doesn't do this. *)
    | pself r' l => pself (F r') l
    end
  end.
Notation "r .p[ p := q  ]" := (psubst_path p q r).

Reserved Notation "T1 ~p[ p := q  ] T2" (at level 70).
Inductive ty_path_repl (p q : path) : ty → ty → Prop :=
| ty_path_repl_TAnd1 T1 T2 U :
  T1 ~p[ p := q ] T2 →
  TAnd T1 U ~p[ p := q ] TAnd T2 U
| ty_path_repl_TAnd2 T1 T2 U :
  T1 ~p[ p := q ] T2 →
  TAnd U T1 ~p[ p := q ] TAnd U T2
| ty_path_repl_TOr1 T1 T2 U :
  T1 ~p[ p := q ] T2 →
  TOr T1 U ~p[ p := q ] TOr T2 U
| ty_path_repl_TOr2 T1 T2 U :
  T1 ~p[ p := q ] T2 →
  TOr U T1 ~p[ p := q ] TOr U T2
| ty_path_repl_TLater T1 T2 :
  T1 ~p[ p := q ] T2 →
  TLater T1 ~p[ p := q ] TLater T2
| ty_path_repl_TAll1 T1 T2 U :
  T1 ~p[ p := q ] T2 →
  TAll T1 U ~p[ p := q ] TAll T2 U
| ty_path_repl_TAll2 T1 T2 U :
  T1 ~p[ p.|[ren (+1)] := q.|[ren (+1)] ] T2 →
  TAll U T1 ~p[ p := q ] TAll U T2
| ty_path_repl_TMu T1 T2 :
  T1 ~p[ p.|[ren (+1)] := q.|[ren (+1)] ] T2 →
  TMu T1 ~p[ p := q ] TMu T2
| ty_path_repl_TVMem T1 T2 l :
  T1 ~p[ p := q ] T2 →
  TVMem l T1 ~p[ p := q ] TVMem l T2
| ty_path_repl_TTMem1 T1 T2 U l :
  T1 ~p[ p := q ] T2 →
  TTMem l T1 U ~p[ p := q ] TTMem l T2 U
| ty_path_repl_TTMem2 T1 T2 U l :
  T1 ~p[ p := q ] T2 →
  TTMem l U T1 ~p[ p := q ] TTMem l U T2
| ty_path_repl_TSel r l :
  TSel r l ~p[ p := q ] TSel (r .p[ p := q ]) l
where "T1 ~p[ p := q  ] T2" := (ty_path_repl p q T1 T2) .

Lemma psubst_path_id p q : q .p[ p := p ] = q.
Proof. elim: q => /= *; case_decide; by f_equal. Qed.

Lemma ty_path_repl_id p T1 T2 : T1 ~p[ p := p ] T2 → T1 = T2.
Proof. intros Hr; dependent induction Hr; by rewrite // ?IHHr // psubst_path_id. Qed.

Lemma psubst_path_self p q: p .p[ p := q ] = q.
Proof. case: p => /= [^~s]; by rewrite decide_True. Qed.

Lemma ren_scons v ρ : ren (+1) >> v .: ρ = ρ. Proof. done. Qed.

From D.Dot.lr Require Import unary_lr.
From iris.proofmode Require Import tactics.

Section foo.
  Context `{dlangG Σ}.

  Lemma exists_equivI {A} {PROP: sbi} (φ1 φ2 : A -d> PROP) :
    (∀ x, φ1 x ≡ φ2 x) ⊢@{PROP}
    (∃ x, φ1 x) ≡ ∃ x, φ2 x.
  Proof.
    rewrite -discrete_fun_equivI.
    apply (@f_equiv _ _ _ (λ φ : _ -d> _, ∃ x, φ x)%I). solve_proper.
  Qed.

  Lemma forall_equivI {A} {PROP: sbi} (φ1 φ2 : A -d> PROP) :
    (∀ x, φ1 x ≡ φ2 x) ⊢@{PROP}
    (∀ x, φ1 x) ≡ ∀ x, φ2 x.
  Proof.
    rewrite -discrete_fun_equivI.
    apply (@f_equiv _ _ _ (λ φ : _ -d> _, ∀ x, φ x)%I). solve_proper.
  Qed.

  Lemma wp_equivI (φ1 φ2 : vl -d> iPropO Σ) t :
    (∀ x, φ1 x ≡ φ2 x) ⊢@{iPropI Σ}
    WP t {{ φ1 }} ≡ WP t {{ φ2 }}.
  Proof.
    rewrite -discrete_fun_equivI.
    apply (@f_equiv _ _ _ (λ φ : _ -d> _, WP t {{ φ }})%I). solve_proper.
  Qed.

  Lemma or2_equivI {PROP : sbi} (P1 P2 Q : PROP) :
    P1 ≡ P2 ⊢@{PROP} (P1 ∨ Q) ≡ (P2 ∨ Q).
  Proof. apply (@f_equiv _ _ _ (λ P, P ∨ Q)%I). solve_proper. Qed.

  Lemma and2_equivI {PROP : sbi} (P1 P2 Q : PROP) :
    P1 ≡ P2 ⊢@{PROP} (P1 ∧ Q) ≡ (P2 ∧ Q).
  Proof. apply (@f_equiv _ _ _ (λ P, P ∧ Q)%I). solve_proper. Qed.

  Lemma wand2_equivI {PROP : sbi} (P1 P2 Q : PROP) :
    P1 ≡ P2 ⊢@{PROP} (P1 -∗ Q) ≡ (P2 -∗ Q).
  Proof. apply (@f_equiv _ _ _ (λ P, P -∗ Q)%I). solve_proper. Qed.

  Lemma rewrite_tsel_psubst p l ρ v vr:
    path_wp p.|[ρ] (λ w : vl, ⌜w = vr.[ρ]⌝) -∗
    ⟦ TSel p l ⟧ ρ v -∗ ⟦ TSel (pv vr) l ⟧ ρ v.
  Proof.
    iIntros "Hp /="; iEval (rewrite path_wp_eq).
    iDestruct 1 as (vr') "[Hp' H]"; iDestruct "H" as (ψ d Hl) "H".
    iDestruct (path_wp_det with "Hp Hp'") as %<-; iClear "Hp Hp'".
    iExists ψ, d. iFrame (Hl) "H".
  Qed.

  Lemma rewrite_tsel_psubst' p l ρ v vr :
    path_wp p.|[ρ] (λ w : vl, ⌜w = vr.[ρ]⌝) -∗
    ⟦ TSel p l ⟧ ρ v -∗ ⟦ TSel (p .p[ p := pv vr ]) l ⟧ ρ v.
  Proof. rewrite psubst_path_self. exact: rewrite_tsel_psubst. Qed.

  (* Argh, we must also replace by longer paths :-( *)
  Lemma path_replacement_equiv_plain {p vr ρ} q (φ : vl → iProp Σ):
    path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) ⊢@{iPropI Σ}
    path_wp q.|[ρ] φ ≡ path_wp (q .p[p := pv vr]).|[ρ] φ.
  Proof.
    elim: q φ => [w | q IHq l'] φ /=; case_decide; simplify_eq/=.
    - by iIntros (->).
    - by iIntros "_".
    - rewrite !path_wp_eq.
      iDestruct 1 as (v1) "#[Hq A]"; iDestruct "A" as %(v1' &Hl & ->).
      iApply prop_ext; iModIntro; iSplit; last iIntros "Hφ"; eauto.
      iDestruct 1 as (v2) "[Hq' A]"; iDestruct "A" as (v2' Hl') "Hφ".
      iDestruct (path_wp_det with "Hq Hq'") as %->; iClear "Hq Hq'".
      by objLookupDet.
    - iApply IHq.
  Qed.

  Lemma rewrite_tsel_psubst2 p q l ρ v vr:
    path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) ⊢@{iPropI Σ}
    ⟦ TSel q l ⟧ ρ v ≡ ⟦ TSel (q .p[ p := pv vr ]) l ⟧ ρ v.
  Proof. exact: path_replacement_equiv_plain. Qed.

  Lemma path_replacement_equiv p q vr ρ (φ : vl → iProp Σ):
    □path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) ⊢@{iPropI Σ}
    □(path_wp q.|[ρ] φ ∗-∗ path_wp (q .p[p := pv vr]).|[ρ] φ).
  Proof.
    iIntros "#H !>".
    iRewrite -(path_replacement_equiv_plain q φ with "H").
    by rewrite -wand_iff_refl.
  Qed.

(*
  Lemma and_equivI {PROP : sbi} (P1 P2 Q1 Q2 : PROP) :
    P1 ≡ P2 ⊢@{PROP} Q1 ≡ Q2 -∗
    (P1 ∧ Q1) ≡ (P2 ∧ Q2).
  Proof.
  Admitted. *)
  Ltac iProperness :=
    repeat first
    [ rewrite -!f_equiv
    | rewrite -exists_equivI; iIntros
    | rewrite -forall_equivI; iIntros
    | rewrite -wp_equivI; iIntros
    | progress rewrite -?and2_equivI -?wand2_equivI -?or2_equivI
    ].


  Lemma rewrite_ty_path_repl_plain p T1 T2 ρ v vr:
    T1 ~p[ p := pv vr ] T2 →
    path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) ⊢@{iPropI Σ} (* p : vr.type *)
    ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v.
  Proof.
    move HE: (pv vr) => q; move => Hrew; move: v ρ vr HE.
    Time induction Hrew => v ρ vr HE; subst q; last apply path_replacement_equiv_plain;
      iIntros "/= #H"; iProperness;
      try by [iApply IHHrew; rewrite // hsubst_comp subst_comp ren_scons].
  Qed.

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

  (* Lemma rewrite_ty_path_repl p T1 T2 ρ v vr:
    T1 ~p[ p := pv vr ] T2 →
    path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) -∗ (* p : vr.type *)
    (⟦ T1 ⟧ ρ v ∗-∗ ⟦ T2 ⟧ ρ v).
  Proof.
    (* V1: gets type error at Qed, due to [dependent induction]. *)
    (* intros Hrew; move: v ρ; dependent induction Hrew => v ρ; *)
    (* V2 *)
    move HE: (pv vr) => q; move => Hrew; move: v ρ vr HE. induction Hrew => v ρ vr HE; subst q;
      last apply rewrite_tsel_psubst2; iIntros "/= #H !>"; iSplit.
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

  Lemma path_replacement p q vr ρ φ:
    □path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) ⊢@{iPropI Σ}
    □(path_wp q.|[ρ] φ -∗ path_wp (q .p[p := pv vr]).|[ρ] φ).
  Proof.
    iIntros "#Heq !> HA".
    (* rewrite (path_replacement_equiv_plain q φ); by iApply (internal_eq_iff with "Heq"). *)
    iApply (path_replacement_equiv with "Heq HA").
  Qed.

  Lemma path_replacement_2 p q vr ρ φ:
    □path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) ⊢@{iPropI Σ}
    □(path_wp (q .p[p := pv vr]).|[ρ] φ -∗ path_wp q.|[ρ] φ).
  Proof.
    iIntros "#Heq !> HA".
    iApply (path_replacement_equiv with "Heq HA").
  Qed.

  (* Lemma TMu_E Γ T v: Γ ⊨ tv v : TMu T -∗ Γ ⊨ tv v : T.|[ids 0/] .p [.
  Proof. by rewrite TMu_equiv. Qed.

  Lemma TMu_I Γ T v: Γ ⊨ tv v : T.|[v/] -∗ Γ ⊨ tv v : TMu T.
  Proof. by rewrite TMu_equiv. Qed. *)

  (* Looks very false. *)
  (* Lemma swap_substs p q r ρ: (q .p[ p := r ]).|[ren ρ] = q.|[ren ρ] .p[ p.|[ren ρ] := r.|[ren ρ]].
  Proof.
    induction q eqn:Heq; cbn; case_decide; try by simplify_eq/=; rewrite 1?decide_True.
    case_decide => //=.
    rewrite H1. f_equal.
    simplify_eq/=.
  elim: q => /= [v | q IHq l]; case_decide; simplify_eq/=; try by rewrite 1?decide_True.

  rewrite decide_False; simplify_eq/=. done. naive_solver. congruence. *)

End foo.
