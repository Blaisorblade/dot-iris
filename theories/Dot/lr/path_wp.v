From iris.proofmode Require Import tactics.
From D Require Import iris_prelude.
From D.Dot Require Import dlang_inst rules.
From D.pure_program_logic Require Import lifting.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx) (ρ : env) (Pv : vl → Prop).

(* Auxiliary. *)

Lemma PureExec_to_terminates n φ e v : PureExec φ n e (tv v) → φ → terminates e.
Proof. intros HP Hφ. exists v. eapply nsteps_rtc, HP, Hφ. Qed.

Lemma plength_subst_inv p s :
  plength p.|[s] = plength p.
Proof. by elim: p => [v| p /= ->]. Qed.

Lemma path2tm_subst p ρ: (path2tm p).|[ρ] = path2tm p.|[ρ].
Proof. by elim: p => /= [//|p -> l]. Qed.

Inductive path_wp_pure : path → (vl → Prop) → Prop :=
| pwp_pv vp Pv : Pv vp → path_wp_pure (pv vp) Pv
| pwp_pself p vp q l Pv : path_wp_pure p (eq vp) → vp @ l ↘ dvl q → path_wp_pure q Pv →
  path_wp_pure (pself p l) Pv .
Local Hint Constructors path_wp_pure : core.

Lemma path_wp_pure_inv_pv Pv v : path_wp_pure (pv v) Pv ↔ Pv v.
Proof. split; by [inversion_clear 1 | auto]. Qed.

Lemma path_wp_pure_inv_pself Pv p l : path_wp_pure (pself p l) Pv →
  ∃ vp q, path_wp_pure p (eq vp) ∧ vp @ l ↘ dvl q ∧ path_wp_pure q Pv ∧
  path_wp_pure (pself p l) Pv.
Proof. inversion_clear 1; naive_solver. Qed.
 (* exists vp, q. by econstructor. *)
 (* exists vp, q. eauto. apply H4.
 exists vp, (pself p l). eauto. apply H4.
 eexists _, _. intros. apply H4. Unshelve. apply vp.
 Qed.
 info_eauto. exists vp, q. by econstructor. *)

(** * Pure path weakest precondition. *)
(* Fixpoint path_wp_pure p Pv {struct p} : Prop :=
  match p with
  | pself p l =>
  ∃ vp q, path_wp_pure p (eq vp) → vp @ l ↘ dvl q → path_wp_pure q Pv →
  path_wp_pure (pself p l) Pv
  (* path_wp_pure p (λ v, ∃ p, v @ l ↘ dvl p ∧ path_wp_pure p Pv) *)
  | pv vp => Pv vp
  end. *)

Global Instance Proper_pwp_pure: Proper ((=) ==> pointwise_relation _ iff ==> iff) path_wp_pure.
Proof.
  (* The induction works best in this shape, but this instance is best kept local. *)
  have Proper_pwp_2: ∀ p, Proper (pointwise_relation _ iff ==> iff) (path_wp_pure p).
  by rewrite /pointwise_relation => p P1 P2 HPeq; split;
    induction 1; naive_solver.
  solve_proper.
Qed.

Lemma path_wp_pure_wand {Pv1 Pv2 p}:
  path_wp_pure p Pv1 →
  (∀ v, Pv1 v → Pv2 v) →
  path_wp_pure p Pv2.
Proof. elim; eauto. Qed.
(* elim => [v Pv Hpv| p' vp q l Pv Hpv IHp' Hl Hq IHq] Hwand; eauto. *)
  (* by constructor; apply Hwand.
  elim: p Pv1 Pv2 => /= [v|p IHp l] Pv1 Pv2 Hp Hwand;
    first by apply Hwand.
  apply: (IHp _ _ Hp) => {IHp Hp} v [vq [??]].
  eauto.
Qed. *)

Lemma path_wp_pure_eq p Pv :
  path_wp_pure p Pv ↔ ∃ v, path_wp_pure p (eq v) ∧ Pv v.
Proof.
  split.
  - elim; naive_solver.
  - move => [v [Hpeq HPv]]. dependent induction Hpeq; naive_solver.
Qed.

Lemma path_wp_pure_det {p v1 v2}:
  path_wp_pure p (eq v1) →
  path_wp_pure p (eq v2) →
  v1 = v2.
Proof.
  move => Hp1 Hp2; move: v2 Hp2; induction Hp1; intros; inverse Hp2; first naive_solver.
  lazymatch goal with H1 : ?vp @ l ↘ dvl ?q, H2 : ?vp0 @ l ↘ dvl ?q0 |- _ =>
    (suff ?: q = q0 by subst; auto);
    (suff ?: vp = vp0 by subst; objLookupDet);
    auto
  end.
Qed.

Lemma path_wp_pure_swap p w :
  path_wp_pure p (λ v, v = w) ↔
  path_wp_pure p (eq w).
Proof. split => Hp; exact: path_wp_pure_wand. Qed.

Lemma path_wp_exec_pure p v :
  path_wp_pure p (eq v) →
  ∃ n, PureExec True n (path2tm p) (tv v).
Proof.
  move HE: (eq v) => P Hp; move: v HE; induction Hp; intros; simplify_eq.
  by exists 0; constructor.
  have [m /(_ I) Hs1] := IHHp1 _ eq_refl.
  have [n /(_ I) Hs2] := IHHp2 _ eq_refl.
  exists (S m + n) => _ /=.
  eapply (nsteps_trans (S m)), Hs2; eapply nsteps_r.
  by apply (pure_step_nsteps_ctx (fill_item (ProjCtx l))), Hs1.
  by apply nsteps_once_inv, pure_tproj.
Qed.

Definition alias_paths p q :=
  path_wp_pure q (λ vp, path_wp_pure p (eq vp)).
Hint Unfold alias_paths : core.

Lemma alias_paths_pv_eq_1 p vr :
  alias_paths p (pv vr) ↔ path_wp_pure p (eq vr).
Proof. rewrite /alias_paths. by setoid_rewrite path_wp_pure_inv_pv. Qed.

Hint Extern 1 (path_wp_pure _ _) => by apply path_wp_pure_swap : core.

Lemma alias_paths_pv_eq_2 p vr :
  alias_paths (pv vr) p ↔ path_wp_pure p (eq vr).
Proof.
  rewrite /alias_paths -path_wp_pure_swap.
  by setoid_rewrite path_wp_pure_inv_pv.
Qed.

Lemma alias_paths_self p v :
  alias_paths p (pv v) → alias_paths p p.
Proof.
  rewrite alias_paths_pv_eq_1 /alias_paths !path_wp_pure_eq; naive_solver.
Qed.

Lemma alias_paths_refl_vl v :
  alias_paths (pv v) (pv v).
Proof. eauto. Qed.

Lemma alias_paths_sameres p q:
  alias_paths p q ↔
  ∃ v,
    path_wp_pure p (eq v) ∧
    path_wp_pure q (eq v).
Proof. rewrite /alias_paths !path_wp_pure_eq; naive_solver. Qed.

Lemma alias_paths_symm p q :
  alias_paths p q ↔ alias_paths q p.
Proof. rewrite !alias_paths_sameres. naive_solver. Qed.
Lemma alias_paths_symm' p q :
  alias_paths p q → alias_paths q p.
Proof. apply alias_paths_symm. Qed.

Lemma alias_paths_trans p q r :
  alias_paths p q → alias_paths q r → alias_paths p r.
Proof.
  rewrite !alias_paths_sameres => -[v [Hpv Hqv]] [w [Hqw Hrw]].
  have Heq: v = w by exact: path_wp_pure_det. simplify_eq; eauto.
Qed.

Lemma alias_paths_samepwp_pure p q:
  alias_paths p q ↔
    (∃ u, path_wp_pure p (eq u)) ∧
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

Lemma alias_paths_elim_eq_pure Pv {p q}:
  alias_paths p q →
  path_wp_pure p Pv ↔ path_wp_pure q Pv.
Proof. move => /alias_paths_samepwp_pure [_]. apply. Qed.

From D.misc_unused Require Import lty.
Include OLty VlSorts dlang_inst.

From iris.bi Require Import fixpoint big_op.
(* From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre. *)
Set Default Proof Using "Type".
Import uPred.

Canonical Structure pathO := leibnizO path.

Section path_wp_pre.
  Context {Σ : gFunctors}.
  Implicit Types (φ : lty Σ).

  (** The definition of total weakest preconditions is very similar to the
  definition of normal (i.e. partial) weakest precondition, with the exception
  that there is no later modality. Hence, instead of taking a Banach's fixpoint,
  we take a least fixpoint. *)
  Definition ltyeq vp : lty Σ := Lty (λ v, ⌜ vp = v ⌝)%I.
  Definition path_wp_pre (path_wp : pathO → lty Σ → iProp Σ) p φ : iProp Σ :=
    match p with
    | pv vp => φ vp
    | pself p l => ∃ vp q, ⌜ vp @ l ↘ dvl q ⌝ ∧
        path_wp p (ltyeq vp) ∗ path_wp q φ
    end%I.
  (* Instance: (∀ p φ, Persistent (path_wp p φ)) → Persistent (path_wp_pre path_wp p φ).
  Proof. intros; destruct p; apply _. Qed. *)

  Lemma path_wp_pre_mono (wp1 wp2 : path → lty Σ → iProp Σ) :
    ((□ ∀ p Φ, wp1 p Φ -∗ wp2 p Φ) →
    ∀ p Φ, path_wp_pre wp1 p Φ -∗ path_wp_pre wp2 p Φ)%I.
  Proof.
    iIntros "#H"; iIntros (p1 Φ). rewrite /path_wp_pre /=.
    destruct (p1) as [v|]; first by iIntros.
    iDestruct 1 as (vp q Hlook) "[Hp Hq]".
    iExists vp, q. iFrame (Hlook).
    iSplitL "Hp"; by iApply "H".
  Qed.

  (* Uncurry [path_wp_pre] and equip its type with an OFE structure *)
  Definition path_wp_pre' :
    (prodO pathO (ltyO Σ) → iPropO Σ) →
    (prodO pathO (ltyO Σ) → iPropO Σ) := curry ∘ path_wp_pre ∘ uncurry.
End path_wp_pre.

Local Instance path_wp_pre_mono' {Σ}: BiMonoPred (@path_wp_pre' Σ).
Proof.
  constructor.
  - iIntros (wp1 wp2) "#H". iIntros ([p Φ]); iRevert (p Φ).
    iApply path_wp_pre_mono. iIntros "!>" (p Φ). iApply ("H" $! (p,Φ)).
  - intros wp Hwp n [p1 Φ1] [p2 Φ2] [?%leibniz_equiv Heq]; simplify_eq/=.
    rewrite /uncurry /path_wp_pre; repeat (apply Heq || f_equiv || done).
Qed.

Definition path_wp_def {Σ} p φ : iProp Σ := bi_least_fixpoint path_wp_pre' (p, φ).
Definition path_wp_aux {Σ} : seal (@path_wp_def Σ). by eexists. Qed.
Definition path_wp {Σ} := (@path_wp_aux Σ).(unseal).
Definition path_wp_eq {Σ} : path_wp = @path_wp_def Σ := path_wp_aux.(seal_eq).

Section path_wp.
  (** A simplified variant of weakest preconditions for path evaluation.
      The difference is that path evaluation is completely pure, and
      postconditions must hold now, not after updating resources.
      vp ("Value from Path") and vq range over results of evaluating paths.

      Path evaluation was initially more complex; now that we got to this
      version, I wonder whether we can just use the standard Iris WP, but I am
      not sure if that would work.
      *)
  Fixpoint path_wp p φ: iProp Σ :=
    match p with
    | pself p l => path_wp p (λ v, ∃ w, ⌜ v @ l ↘ dvl w ⌝ ∧ φ w)
    | pv vp => φ vp
    end%I.

  Global Instance path_wp_ne p : NonExpansive (path_wp p).
  Proof.
    elim: p => [w|p IHp l] n x y Heq /=. done.
    f_equiv => vp. f_equiv => vq. f_equiv. exact: Heq.
  Qed.

  Global Instance path_wp_persistent φ p:
    (∀ v, Persistent (φ v)) → Persistent (path_wp p φ).
  Proof. elim: p φ => *; apply _. Qed.

  Global Instance Proper_pwp: Proper ((=) ==> pointwise_relation _ (≡) ==> (≡)) path_wp.
  Proof.
    (* The induction works best in this shape, but this instance is best kept local. *)
    have Proper_pwp_2: ∀ p, Proper (pointwise_relation _ (≡) ==> (≡)) (path_wp p).
    elim; solve_proper.
    solve_proper.
  Qed.

  Lemma path_wp_pureable p Pv:
    path_wp p (λ v, ⌜Pv v⌝) ⊣⊢ ⌜path_wp_pure p Pv⌝.
  Proof.
    elim: p Pv => /= [//|p IHp l] Pv.
    by rewrite -{}IHp; f_equiv => v; iIntros "!% /=".
  Qed.

  Lemma path_wp_wand φ1 φ2 p:
    path_wp p φ1 -∗
    (∀ v, φ1 v -∗ φ2 v) -∗
    path_wp p φ2.
  Proof.
    elim: p φ1 φ2 => /= [v|p IHp l] ??; iIntros "H1 Hwand";
      first by iApply "Hwand".
    iApply (IHp with "H1").
    iIntros (v); iDestruct 1 as (vq Hl) "?".
    iExists vq; iFrame (Hl). by iApply "Hwand".
  Qed.

  Global Instance path_wp_pureableI p φ Pv :
    (∀ v, IntoPure (φ v) (Pv v)) →
    IntoPure (path_wp p φ)%I (path_wp_pure p Pv).
  Proof.
    rewrite /IntoPure -path_wp_pureable. iIntros (Hw) "Hp".
    iApply (path_wp_wand with "Hp"). iIntros (v). iApply Hw.
  Qed.
  Global Instance path_wp_pureableF p φ Pv b :
    (∀ v, FromPure b (φ v) (Pv v)) →
    FromPure false (path_wp p φ)%I (path_wp_pure p Pv).
  Proof.
    rewrite /FromPure/= -path_wp_pureable. iIntros (Hw) "Hp".
    iApply (path_wp_wand with "Hp"). iIntros (v Hpv). iApply Hw.
    by case: b {Hw} => /=; iIntros "!%".
  Qed.

  Lemma path_wp_det p v1 v2:
    path_wp p (λ w, ⌜ v1 = w ⌝) -∗
    path_wp p (λ w, ⌜ v2 = w ⌝) -∗
    ⌜ v1 = v2 ⌝: iProp Σ.
  Proof. iIntros "!%". exact: path_wp_pure_det. Qed.

  Lemma path_wp_swap p u :
    path_wp p (λ w, ⌜w = u⌝) ⊣⊢ path_wp p (λ w, ⌜u = w⌝).
  Proof. iIntros "!%". by rewrite /= path_wp_pure_swap. Qed.

  Lemma path_wp_eq p φ :
    path_wp p φ ⊣⊢ ∃ v, ⌜ path_wp_pure p (eq v) ⌝ ∧ φ v.
  Proof.
    elim: p φ => [ v | p IHp l ] φ /=; iSplit; iIntros "H".
    - auto.
    - by iDestruct "H" as (w <-) "H".
    - rewrite IHp.
      iDestruct "H" as (v Hp w Hl) "Hw".
      iExists w; iSplit; last by [].
      iIntros "!%". apply: path_wp_pure_wand; naive_solver.
    - setoid_rewrite IHp; setoid_rewrite path_wp_pure_eq.
      iDestruct "H" as (w [v Hp]) "Hw".
      iExists v; iSplit; naive_solver eauto.
  Qed.

  Lemma path_wp_later_swap p φ:
    path_wp p (λ v, ▷ φ v) ⊢ ▷ path_wp p (λ v, φ v).
  Proof.
    elim: p φ => [v // | p IHp l /=] φ.
    rewrite -IHp.
    iIntros "H"; iApply (path_wp_wand with "H").
    by iIntros (v) "H !>".
  Qed.

  Lemma path_wp_laterN_swap p φ i:
    path_wp p (λ v, ▷^i φ v) ⊢ ▷^i path_wp p (λ v, φ v).
  Proof.
    elim: i => [// | i /= <-].
    rewrite path_wp_later_swap. by [].
  Qed.

  Global Instance Plain_path_wp p φ (H : (∀ v, Plain (φ v))) :
    Plain (path_wp p φ).
  Proof.
    elim: p φ H => /= [//|p IHp l] φ H; rewrite path_wp_eq /Plain.
    iDestruct 1 as (v) "#[Heq H]"; iDestruct "H" as (w Hl) "#H".
    iModIntro. repeat (iExists _; iSplit => //).
  Qed.

  Lemma path_wp_exec p v :
    path_wp p (λ w, ⌜ v = w ⌝) ⊢@{iPropI Σ}
    ⌜ PureExec True (plength p) (path2tm p) (tv v) ⌝.
  Proof. iIntros "!%". apply path_wp_exec_pure. Qed.

  Lemma path_wp_pure_exec p φ :
    path_wp p φ ⊢ ∃ v, ⌜ PureExec True (plength p) (path2tm p) (tv v) ⌝ ∧ φ v.
  Proof.
    rewrite path_wp_eq. setoid_rewrite <-path_wp_exec.
    iDestruct 1 as (v Hcl) "H". eauto.
  Qed.

  Lemma path_wp_to_wp p φ :
    path_wp p (λ v, φ v) -∗
    WP (path2tm p) {{ v, φ v }}.
  Proof.
    rewrite path_wp_pure_exec; iDestruct 1 as (v Hex) "H".
    by rewrite -wp_pure_step_later // -wp_value.
  Qed.

  Global Instance path_wp_timeless p Pv: Timeless (path_wp p (λ v, ⌜Pv v⌝))%I.
  Proof. rewrite path_wp_pureable. apply _. Qed.

  Lemma path_wp_terminates p φ :
    path_wp p φ ⊢ ⌜ terminates (path2tm p) ⌝.
  Proof.
    rewrite path_wp_pure_exec; iDestruct 1 as (v Hp) "_"; iIntros "!%".
    exact: PureExec_to_terminates.
  Qed.
End path_wp.
