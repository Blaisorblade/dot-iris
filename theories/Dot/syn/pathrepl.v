From iris.proofmode Require Import tactics.

From D.Dot.syn Require Import syn.
From D.Dot.lr Require Import unary_lr.
From iris.program_logic Require Import ectx_language.
From D.pure_program_logic Require Import lifting.

Implicit Types
         (T : ty) (v w : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (Γ : ctx) (vs : vls) (l : label) (Pv : vl → Prop).
Set Nested Proofs Allowed.

Definition alias_paths p q :=
  path_wp_pure p (λ vp, path_wp_pure q (λ vq, vp = vq)).

Lemma alias_paths_pv_eq_1 p vr :
  alias_paths p (pv vr) ↔ path_wp_pure p (λ w, w = vr).
Proof. done. Qed.

Lemma alias_paths_pv_eq_2 p vr :
  alias_paths (pv vr) p ↔ path_wp_pure p (λ w, w = vr).
Proof. by rewrite -path_wp_pure_swap. Qed.

Lemma alias_paths_refl_vl v :
  alias_paths (pv v) (pv v).
Proof. done. Qed.

Lemma alias_paths_sameres p q:
  alias_paths p q ↔
  ∃ v,
    path_wp_pure p (λ vp, vp = v) ∧
    path_wp_pure q (λ vq, vq = v).
Proof.
  rewrite /alias_paths !path_wp_pure_eq. split => -[vp];
    [ rewrite (path_wp_pure_swap q) |
      rewrite -(path_wp_pure_swap q) ]; eauto.
Qed.

Lemma alias_paths_symm p q :
  alias_paths p q → alias_paths q p.
Proof. rewrite !alias_paths_sameres. intros; ev; eauto. Qed.

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

Reserved Notation "p1 ~pp[ p := q  ] p2" (at level 70).
Inductive path_path_repl (p q : path) : path → path → Prop :=
| path_path_repl_base : p ~pp[ p := q ] q
| path_path_repl_self p1 p2 l :
  p1 ~pp[ p := q ] p2 →
  pself p1 l ~pp[ p := q ] pself p2 l
where "p1 ~pp[ p := q  ] p2" := (path_path_repl p q p1 p2) .

Lemma psubst_path_id p1 p2 p : p1 ~pp[ p := p ] p2 → p1 = p2.
Proof. by elim; intros; simplify_eq/=. Qed.

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
| ty_path_repl_TSel p1 p2 l :
  p1 ~pp[ p := q ] p2 →
  TSel p1 l ~p[ p := q ] TSel p2 l
where "T1 ~p[ p := q  ] T2" := (ty_path_repl p q T1 T2) .

Definition ty_path_repl_rtc p q := rtc (ty_path_repl p q).
Notation "T1 ~p[ p := q  ]* T2" := (ty_path_repl_rtc p q T1 T2) (at level 70).

Lemma ty_path_repl_id p T1 T2 : T1 ~p[ p := p ] T2 → T1 = T2.
Proof.
  intros Hr; dependent induction Hr; rewrite // ?IHHr //.
  f_equiv; exact: psubst_path_id.
Qed.

(* XXX For Iris *)
Hint Extern 1 (environments.envs_entails _ (_ ∗-∗ _)) => iSplit : core.

Section path_repl.
  Context `{dlangG Σ}.
  Implicit Types (φ: vl → iProp Σ).

  Notation path_wp p φ := (@path_wp Σ p φ).

  (* Not provable through pure props for impure [φ]. *)
  Lemma alias_paths_samepwp p q:
    alias_paths p q ↔
      (∃ u, path_wp_pure p (λ vp, vp = u)) ∧
      ∀ φ, path_wp p φ ≡ path_wp q φ.
  Proof.
    rewrite alias_paths_sameres; split.
    - destruct 1 as (v & Hp & Hq).
      split; first by [eauto]; intros φ.
      rewrite !path_wp_eq. f_equiv => w.
      rewrite !path_wp_pureable; do 2 f_equiv.
      split => Hr; [ rewrite -(path_wp_pure_det Hp Hr)
        | rewrite -(path_wp_pure_det Hq Hr)]; auto.
    - destruct 1 as ((u & Hp) & Heq). exists u; split; first done.
      (* Yes, completely insane. *)
      apply (pure_soundness (M := iResUR Σ)).
      iRevert (Hp). by rewrite -!path_wp_pureable Heq.
  Qed.

  Lemma alias_paths_elim_eq φ p q:
    alias_paths p q →
    path_wp p φ ≡ path_wp q φ.
  Proof. intros ?%alias_paths_samepwp. intuition. Qed.

  (** Beware: we can do path replacement *before* substitution,
      even tho substitution and path replacement don't commute nicely.

      As a special case, we get the less surprising:
      [alias_paths_subst p r ids → path_wp q φ ≡ path_wp (q .p[p := r]) φ].

      But we do need the general form. *)
  Lemma path_replacement_equiv {p q ρ} p1 p2 (φ : vl → iProp Σ):
    p1 ~pp[ p := q ] p2 →
    alias_paths p.|[ρ] q.|[ρ] →
    path_wp p1.|[ρ] φ ≡ path_wp p2.|[ρ] φ.
  Proof.
    move => Hrepl.
    elim: Hrepl φ => [| p1' p2' l Hrepl IHrepl] φ /=.
    exact: alias_paths_elim_eq.
    apply IHrepl.
  Qed.

  Lemma rewrite_ty_path_repl {p q T1 T2 ρ v}:
    T1 ~p[ p := q ] T2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v.
  Proof.
    move => Hrew; move: v ρ.
    induction Hrew => v ρ He /=; properness;
      by [|exact: path_replacement_equiv|iApply IHHrew; rewrite ?hsubst_comp].
  Qed.

  Lemma rewrite_ty_path_repl_rtc {p q T1 T2 ρ v}:
    T1 ~p[ p := q ]* T2 →
    alias_paths p.|[ρ] q.|[ρ] → (* p : q.type *)
    ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v.
  Proof.
    move => Hr Hal.
    elim: Hr => [//|T T' T'' Hr Hrs IHr].
    by rewrite (rewrite_ty_path_repl Hr Hal) IHr.
  Qed.

  Lemma ren_scons v ρ : ren (+1) >> v .: ρ = ρ.
  Proof. done. Qed.

  (** Define substitution of [pv (ids 0)] by [p] in terms of the
      transitive closure of path replacement.
      Here it's crucial to use the transitive closure of path replacement
      to substitute all occurrences. *)
  Definition psubst_one T p T' :=
    T ~p[ pv (ids 0) := p.|[ren (+1)] ]* T'.|[ren (+1)].
  Notation "T .p[ p /]~ T'" := (psubst_one T p T') (at level 65).

  Lemma psubst_one_repl {T T' p v w ρ}:
    T .p[ p /]~ T' →
    alias_paths p.|[ρ] (pv v) →
    ⟦ T ⟧ (v .: ρ) w ≡ ⟦ T' ⟧ ρ w.
  Proof.
    intros Hrepl Hal.
    rewrite -(interp_weaken_one T' (v .: ρ) _)
      -(rewrite_ty_path_repl_rtc Hrepl) // hsubst_comp ren_scons /=.
    exact: alias_paths_symm.
  Qed.

  Lemma TMu_E_p Γ T T' p i :
    T .p[ p /]~ T' →
    Γ ⊨p p : TMu T, i -∗ Γ ⊨p p : T', i.
  Proof.
    intros Hrepl.
    iIntros "#Hp !>" (ρ) "Hg /="; iSpecialize ("Hp" with "Hg"); iNext.
    rewrite !path_wp_eq.
    iDestruct "Hp" as (v Heq) "Hp"; iExists v; iFrame (Heq).
    by rewrite (psubst_one_repl Hrepl).
  Qed.

  Lemma TMu_I_p Γ T T' p i :
    T .p[ p /]~ T' →
    Γ ⊨p p : T', i -∗ Γ ⊨p p : TMu T, i.
  Proof.
    intros Hrepl.
    iIntros "#Hp !>" (ρ) "Hg /="; iSpecialize ("Hp" with "Hg"); iNext.
    rewrite !path_wp_eq.
    iDestruct "Hp" as (v Heq) "Hp"; iExists v; iFrame (Heq).
    by rewrite (psubst_one_repl Hrepl).
  Qed.

  Lemma T_Forall_Ex_p Γ e1 p2 T1 T2 T2':
    T2 .p[ p2 /]~ T2' →
    Γ ⊨ e1: TAll T1 T2 -∗
    Γ ⊨p p2 : T1, 0 -∗
    (*────────────────────────────────────────────────────────────*)
    Γ ⊨ tapp e1 (path2tm p2) : T2'.
  Proof.
    intros Hrepl.
    iIntros "#He1 #Hp2 !>" (ρ) "#Hg /=".
    smart_wp_bind (AppLCtx _) v "#Hr {He1}" ("He1" with "Hg").
    iDestruct "Hr" as (t ->) "#HvFun".
    iSpecialize ("Hp2" with "Hg").
    iDestruct (path_wp_eq with "Hp2") as (pw Hpwp) "Hp2'".
    move: (Hpwp) => /path_wp_exec_pure Hex.
    iApply (wp_bind (fill [AppRCtx _])).
    rewrite path2tm_subst -wp_pure_step_later // -wp_value plength_subst_inv /=.
    rewrite -wp_pure_step_later; last done. iNext; iNext.
    iApply wp_wand; first by iApply "HvFun".
    iIntros (v) "{Hg HvFun} #Hres".
    by rewrite (psubst_one_repl Hrepl).
  Qed.
End path_repl.
