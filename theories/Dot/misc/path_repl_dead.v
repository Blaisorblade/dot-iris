From iris.proofmode Require Import tactics.

From D.Dot.syn Require Import syn pathrepl.
From D.Dot.lr Require Import unary_lr path_wp.

Implicit Types
         (T : ty) (v w : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (Γ : ctx) (vs : vls) (l : label).

Implicit Types (Pv : vl → Prop).
Set Nested Proofs Allowed.

Section equivI_utils.
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
End equivI_utils.

Ltac iProperness :=
  repeat first
  [ iEval (progress rewrite -(wp_equivI, exists_equivI, forall_equivI)); iIntros
  (* f_equiv must come before those others for performance. *)
  | iEval (progress rewrite -(f_equiv, and2_equivI, wand2_equivI, or2_equivI))
  ].

Definition psubst_path p q : path → path := fix F r :=
  match (decide (r = p)) with
  | left _ => q
  | _ =>
    match r with
    | pv _ => r (* XXX no, values can contain paths! OTOH, pDOT path replacement doesn't do this. *)
    | pself r' l => pself (F r') l
    end
  end.
Notation "r .p[ p := q  ]" := (psubst_path p q r) (at level 65).

Lemma psubst_path_id p q : q .p[ p := p ] = q.
Proof. elim: q => /= *; case_decide; by f_equal. Qed.

Lemma psubst_path_self p q: p .p[ p := q ] = q.
Proof. case: p => /= *; by rewrite decide_True. Qed.

(** Lemma [psubst_path_implies] requires [path_repl_longer], which
requires a diversion to prove.
I'm not sure going through sizes is the shortest proof, but that's the
obvious way on paper, and works well in Coq too. *)
Section psubst_path_implies_lemmas.
  Definition append_ls p (ls : list label) : path := foldr (flip pself) p ls.

  Fixpoint path_size p := match p with
    | pv _ => 0
    | pself p _ => 1 + path_size p
    end.

  Lemma occurs_in_path_repl {p1 p2 p q} :
    p1 ~pp[ p := q ] p2 →
    ∃ n, n + path_size p = path_size p1.
  Proof.
    elim => [|p1' p2' l Hr [n IHr]];
      [ by exists 0 | exists (S n); by rewrite /= IHr].
  Qed.

  Lemma path_size_append p ls :
    path_size (append_ls p ls) = length ls + path_size p.
  Proof. by elim: ls => /= [| _ ls ->]. Qed.

  Lemma path_repl_longer ls {p p1 p2 q l} :
    p1 ~pp[ p := q ] p2 →
    ~append_ls p1 (l :: ls) = p.
  Proof.
    move => /occurs_in_path_repl [ls' Hr] /(f_equal path_size).
    rewrite /= path_size_append. lia.
  Qed.
End psubst_path_implies_lemmas.

(** Path substitution agrees with path replacement. *)
Lemma psubst_path_implies p1 p2 p q :
  p1 ~pp[ p := q ] p2 →
  p1 .p[ p := q ] = p2.
Proof.
  move => Hr.
  elim: Hr => [|p1' p2' l Hr IHr] /=; first exact: psubst_path_self.
  case_decide as Hdec => //; last by rewrite -IHr.
  exfalso; exact: (path_repl_longer []).
Qed.

Definition path_path_repl_rtc p q := rtc (path_path_repl p q).
Notation "p1 ~pp[ p := q  ]* p2" := (path_path_repl_rtc p q p1 p2) (at level 70).

Lemma path_path_repl_self_rtc p q p1 p2 l :
  p1 ~pp[ p := q ]* p2 →
  pself p1 l ~pp[ p := q ]* pself p2 l.
Proof.
  elim => [//| p1' p2' p3' Hrepl H IHrepl].
  by eapply rtc_l, IHrepl; constructor.
Qed.

(** The Kleene start of path replacement agrees with path substitution.
  In fact, there can be only 0 or 1 steps anyway. *)
Lemma psubst_path_rtc_implies_rev p1 p2 p q :
  p1 .p[ p := q ] = p2 →
  p1 ~pp[ p := q ]* p2.
Proof.
  move => <- {p2}.
  elim: p1 => [v|p1 IHp1 l] /=; case_decide as Hdec;
    [|done| |exact: path_path_repl_self_rtc];
  rewrite Hdec; apply rtc_once; constructor.
Qed.

(**
https://en.wikipedia.org/wiki/Idempotence#Idempotent_functions *)
Definition IdempotentUnary {A} (f: A → A) := ∀ x, f (f x) = f x.

Goal ~(∀ p q, IdempotentUnary (psubst_path p q)).
Proof.
  move => Hpsubst_path_idempotent.
  set p0 := pv (ids 0).
  move: (Hpsubst_path_idempotent p0 (pself p0 "A") p0).
  by repeat (simplify_eq/=; case_decide).
Qed.

(* Lemma psubst_path_idempotent p q: Idempotent (psubst_path p q).
Proof.
  (* elim => [v|p1 IHp1 l]/=. case_decide as Hdec.
  rewrite -Hdec.
   simplify_eq/=. try case_decide; simplify_eq/= => //.
  admit.
  admit.
  next.
  move => p1. *)
Admitted. *)

(* Lemma replacing_again_wont_save_you p q p1 p2:
  p1 ≠ p2 →
  p1 .p[ p := q ] ≠ p2 → ~ p1 ~pp[ p := q ]* p2.
Proof.
  move => Hne Hne2 Hr.
  elim: Hr Hne Hne2 => [//|p1' p2' {}p2 Hh Ht IHr] Hne Hne2.
  move: (Hh) => /psubst_path_implies Hq1.
  simplify_eq.
  apply IHr => //.
  by rewrite psubst_path_idempotent.
Qed. *)

  (* inversion Hrepl as [|? q1 ? Hh Ht]; simplify_eq.
  move: (Hh) => /psubst_path_implies Hq1.
  inversion Ht as [|? q2 ? Hh' Ht' Heq1 Heq2]; first simplify_eq.
  move: (Hh') => /psubst_path_implies Hq2.
  have ?: q1 = q2. simplify_eq. by rewrite psubst_path_idempotent.
  simplify_eq.

  induction Hrepl.
  rewrite/Decision.
  elim => [v//| p1' p2' p3' Hrepl H IHrepl].
  by eapply rtc_l, IHrepl; constructor.
Admitted. *)

(* Lemma psubst_path_rtc_dec p1 p2 p q :
  Decision (p1 ~pp[ p := q ]* p2).
Proof.
  case: (decide (p1 = p2)) => [->|Hne]; first by left; constructor.
  case: (decide (p1 .p[ p := q ] = p2)) => [<-|Hne2];
    first by left; exact: psubst_path_rtc_implies_rev.
  right => Hrepl. exact: replacing_again_wont_save_you.
Qed. *)


Section psubst_path_implies_lemmas_extras.
  Lemma occurs_in_path_repl_append {p1 p2 p q} :
    p1 ~pp[ p := q ] p2 →
    ∃ ls, append_ls p ls = p1.
  Proof.
    elim => [|p1' p2' l' Hr [ls' IHr]];
      [ exists [] | exists (l' :: ls')]; by simplify_eq.
  Qed.

  Lemma paths_well_founded {ls1 ls2 p q l} :
    append_ls q (l :: ls1) = p →
    ~append_ls p ls2 = q.
  Proof.
    move => /(f_equal path_size) Heq1 /(f_equal path_size) Heq2.
    move: Heq1 Heq2. rewrite !path_size_append /=. lia.
  Qed.

  Lemma path_repl_longer2 ls {p p1 p2 q l} :
    p1 ~pp[ p := q ] p2 →
    ~append_ls p1 (l :: ls) = p.
  Proof.
    move => /occurs_in_path_repl_append [ls' Hr] Happ.
    exact: paths_well_founded.
  Qed.
End psubst_path_implies_lemmas_extras.

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

(* No reason for bundling subst any more. *)
Notation alias_paths_subst p q ρ := (alias_paths p.|[ρ] q.|[ρ]).

Lemma alias_paths_weaken p q ρ v:
  alias_paths_subst p.|[ren (+1)] q.|[ren (+1)] (v .: ρ) =
  alias_paths_subst p q ρ.
Proof. by rewrite !hsubst_comp ren_scons. Qed.

Lemma alias_paths_equiv_pure p q:
  alias_paths p q ↔
    (∃ u, path_wp_pure p (λ vp, vp = u)) ∧
    ∀ Pv, path_wp_pure p Pv ↔ path_wp_pure q Pv.
Proof.
  rewrite alias_paths_sameres; split.
  - destruct 1 as (v & Hp & Hq).
    split. by eauto. intros Pv.
    rewrite !path_wp_pure_eq.
    f_equiv => w; split => -[Hr];
      [ rewrite -(path_wp_pure_det Hp Hr)
      | rewrite -(path_wp_pure_det Hq Hr)]; auto.
  - intros [[u Hp] Heq]. exists u.
    split; by [|rewrite -Heq].
Qed.

Definition alias_pathsI {Σ} p q : iProp Σ := ⌜alias_paths p q⌝.
Definition alias_paths_substI {Σ} p q ρ : iProp Σ := ⌜alias_paths_subst p q ρ⌝.
Section path_repl.
  Context `{dlangG Σ}.
  Implicit Types (φ: vl → iProp Σ).

  Notation alias_pathsI p q := (@alias_pathsI Σ p q).
  Notation alias_paths_substI p q ρ := (@alias_paths_substI Σ p q ρ).
(*
  Lemma and_equivI {PROP : sbi} (P1 P2 Q1 Q2 : PROP) :
    P1 ≡ P2 ⊢@{PROP} Q1 ≡ Q2 -∗
    (P1 ∧ Q1) ≡ (P2 ∧ Q2).
  Proof.
  Admitted. *)

  Lemma alias_paths_substI_symm p q :
    alias_pathsI p q -∗ alias_pathsI q p.
  Proof. iIntros "!%". exact: alias_paths_symm. Qed.

  Lemma alias_paths_substI_elim_eq' φ p q:
    alias_pathsI p q ⊢
    ⌜path_wp p φ ≡ path_wp q φ⌝.
  Proof. iIntros "!%". apply alias_paths_elim_eq. Qed.

  Lemma alias_paths_subst_elim_wand φ p q:
    alias_paths p q →
    path_wp p φ ⊢ path_wp q φ.
  Proof. iIntros (->%(alias_paths_elim_eq φ)) "$". Qed.

  Lemma alias_paths_subst_elim_wand' φ p q:
    alias_pathsI p q ⊢
    path_wp p φ -∗ path_wp q φ.
  Proof. iIntros (->%(alias_paths_subst_elim_wand φ)) "$". Qed.

  Lemma alias_paths_substI_eq p q:
    alias_pathsI p q ⊣⊢
    ∃ v,
      path_wp p (λ vp : vl, ⌜vp = v⌝) ∧
      path_wp q (λ vq : vl, ⌜vq = v⌝).
  Proof. iIntros "!%". apply alias_paths_sameres. Qed.

  Lemma alias_paths_subst_samepwp' p q:
    alias_pathsI p q ⊣⊢
      (∃ u, path_wp p (λ vp, ⌜vp = u⌝)) ∧
      ∀ φ, ⌜path_wp p φ ≡ path_wp q φ⌝.
  Proof. iIntros "!%". apply alias_paths_samepwp. Qed.


  (** Beware: we can do path replacement *before* substitution,
      even tho substitution and path replacement don't commute nicely.

      As a special case, we get the less surprising:
      [alias_paths_subst_pure p r ids → path_wp q φ ≡ path_wp (q .p[p := r]) φ].

      But we do need the general form. *)
  Lemma path_replacement_equiv_alt {p r ρ} q (φ : vl → iProp Σ):
    alias_paths_subst p r ρ →
    path_wp q.|[ρ] φ ≡ path_wp (q .p[p := r]).|[ρ] φ.
  Proof.
    elim: q φ => [w | q IHq l] φ /=; case_decide.
    - simplify_eq. apply (alias_paths_elim_eq φ (pv w.[ρ]) r.|[ρ]).
    - done.
    - simplify_eq.
      rewrite /= !path_wp_eq alias_paths_sameres /=.
      destruct 1 as (vr & (vq & Hq & w & Hl & ->)%path_wp_pure_eq & Hr).
      iSplit.
      + iDestruct 1 as (vq' Hq' vr' Hl') "Hφ".
        rewrite (path_wp_pure_det Hq' Hq) in Hl'.
        objLookupDet. eauto.
      + iDestruct 1 as (vr' Hr') "Hφ".
        rewrite (path_wp_pure_det Hr' Hr).
        eauto.
    - exact: IHq.
  Qed.

  Lemma path_replacement_equiv_alt' {p r ρ} q (φ : vl → iProp Σ):
    alias_paths_substI p r ρ ⊢
    path_wp q.|[ρ] φ ≡ path_wp (q .p[p := r]).|[ρ] φ.
  Proof. iIntros (?) "!%". exact: path_replacement_equiv_alt. Qed.

  Lemma rewrite_tsel_psubst2 p q l ρ v r:
    alias_paths_substI p r ρ ⊢
    ⟦ TSel q l ⟧ ρ v ≡ ⟦ TSel (q .p[ p := r ]) l ⟧ ρ v.
  Proof. exact: path_replacement_equiv_alt'. Qed.


  (* That's false, as we don't know that q terminates from the hyp. *)
  (* Lemma path_replacement_equiv_0 {p r ρ} q:
    alias_paths_subst p r ρ ⊢@{iPropI Σ}
    alias_paths_subst q (q .p[p := r]) ρ.
  Proof.
    elim: q => [w | q IHq l] /=; case_decide; simplify_eq/=.
    - by iIntros.
    - rewrite -alias_paths_subst_refl_vl. by iIntros.
    - by iIntros.
    - rewrite /= IHq !alias_paths_subst_sameres /=.
      iDestruct 1 as (vr) "#[Hq Hqr]".
      (* We don't know that [pself q l] terminates! *)
  Abort. *)

  (* Lemma rewrite_ty_path_repl'_slow p q T1 T2 ρ v:
    T1 ~p[ p := q ] T2 →
    ⌜alias_paths_subst_pure p q ρ⌝ ⊢@{iPropI Σ} (* p : q.type *)
    ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v.
  Proof.
    move => Hrew; move: v ρ.
    induction Hrew => v ρ;
      iIntros "/= #H"; iProperness; last
      iApply path_replacement_equiv';
      try by [|iApply IHHrew; rewrite ?alias_paths_subst_weaken].
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

  Lemma rewrite_ty_path_repl' p q T1 T2 ρ v:
    T1 ~p[ p := q ] T2 →
    alias_paths_substI p q ρ ⊢
    ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v.
  Proof. iIntros "!%". exact: rewrite_ty_path_repl. Qed.

  Lemma TMu_E_bad Γ T T' p i :
    nclosed p (length Γ) →
    nclosed T (1 + length Γ) →
    T.|[ids (1 + length Γ)/] ~p[ pv (ids (1 + length Γ)) := p ] T' →
    Γ ⊨p p : TMu T, i -∗ Γ ⊨p p : TMu T', i.
  Proof.
    intros Hclp HclT Hrepl.
    iIntros "#Hp !>" (ρ) "Hg"; iSpecialize ("Hp" with "Hg"); iNext.
    rewrite !path_wp_eq.
    iDestruct "Hp" as (v Heq) "Hp"; iExists v; iFrame (Heq).
    have Hal: alias_paths p.|[ρ] (pv v). exact Heq.
    (* iApply interp_weaken_one. *)
    (* rewrite interp_subst_compose_ind. asimpl. *)
    (* Check (rewrite_ty_path_repl Hrepl). *)
    cbn.
    rewrite -(rewrite_ty_path_repl Hrepl).
    rewrite interp_subst_one /=.
    (* iApply "Hp". *)
    asimpl.
    (* rewrite interp_subst_one /=.
    admit. *)
  Abort.

  Lemma TMu_E_real_bad Γ T T' p ρ v :
    alias_paths p.|[ρ] (pv v.[ρ]) →
    T.|[v/] ~p[ pv v := p ] T' →
    path_wp p.|[ρ] (⟦ TMu T ⟧ ρ) -∗ path_wp p.|[ρ] (⟦ T' ⟧ ρ).
  Proof.
    intros Heq0 Hrepl.
    rewrite !path_wp_eq.
    iDestruct 1 as (w Heq) "Hp"; iExists w; iFrame (Heq).
    have ?: w = v.[ρ]. exact: path_wp_pure_det.
    subst.
    have Hal: alias_paths p.|[ρ] (pv v.[ρ]). apply Heq.
    (* have Hal2: alias_paths p.|[ρ] (pv v).|[ρ]. admit. *)
    (* cbn. iPoseProof (rewrite_ty_path_repl with "Hp") as "Hp'". *)
    iApply (rewrite_ty_path_repl Hrepl).
    exact: alias_paths_symm.
    by rewrite interp_subst_one.
  Qed.

  Let Ts := TAnd (TAnd (TSel (pv (ids 0)) "A") (TSel (pv (ids 1)) "B"))
      (TSel (pv (ids 2)) "B").
  Let HclTs : nclosed Ts 3. solve_fv_congruence. Qed.
  (* Eval cbv in Ts.|[ids (1 + 1)/]. *)
End path_repl.
