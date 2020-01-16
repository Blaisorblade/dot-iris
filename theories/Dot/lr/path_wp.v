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

(** * Pure path weakest precondition. *)
Fixpoint path_wp_pure p Pv : Prop :=
  match p with
  | pself p l => path_wp_pure p (λ v, ∃ w, v @ l ↘ dvl w ∧ Pv w)
  | pv vp => Pv vp
  end.

Global Instance Proper_pwp_pure: Proper ((=) ==> pointwise_relation _ iff ==> iff) path_wp_pure.
Proof.
  (* The induction works best in this shape, but this instance is best kept local. *)
  have Proper_pwp_2: ∀ p, Proper (pointwise_relation _ iff ==> iff) (path_wp_pure p).
  elim; solve_proper.
  solve_proper.
Qed.

Lemma path_wp_pure_wand {Pv1 Pv2 p}:
  path_wp_pure p Pv1 →
  (∀ v, Pv1 v → Pv2 v) →
  path_wp_pure p Pv2.
Proof.
  elim: p Pv1 Pv2 => /= [v|p IHp l] Pv1 Pv2 Hp Hwand;
    first by apply Hwand.
  apply: (IHp _ _ Hp) => {IHp Hp} v [vq [??]].
  eauto.
Qed.

Lemma path_wp_pure_eq p Pv :
  path_wp_pure p Pv ↔ ∃ v, path_wp_pure p (eq v) ∧ Pv v.
Proof.
  elim: p Pv => [ v | p IHp l ] Pv /=; split.
  - eauto.
  - by destruct 1 as (w & <- & ?).
  - rewrite IHp; intros (v & Hp & w & ?&?).
    eexists w; split; last by [].
    apply (path_wp_pure_wand Hp).
    intros v' ->; exists w; eauto.
  - setoid_rewrite IHp; intros; ev; subst; eauto.
Qed.

Lemma path_wp_pure_det {p v1 v2}:
  path_wp_pure p (eq v1) →
  path_wp_pure p (eq v2) →
  v1 = v2.
Proof.
  elim: p v1 v2 => [v /=| p /= IHp l //] v1 v2; first by intros <- <-.
  rewrite !path_wp_pure_eq; intros (w1 & Hp1 & ?) (w2 & Hp2 & ?);
    move: (IHp _ _ Hp1 Hp2) => ?; ev; simplify_eq.
  by objLookupDet.
Qed.

Lemma path_wp_pure_swap p w :
  path_wp_pure p (λ v, v = w) ↔
  path_wp_pure p (eq w).
Proof. split => Hp; exact: path_wp_pure_wand. Qed.

Lemma path_wp_exec_pure p v :
  path_wp_pure p (eq v) →
  ∃ n, PureExec True n (path2tm p) (tv v).
Proof.
  elim: p v => [w|p IHp l] v; rewrite /PureExec/=.
  by intros ->; eexists; constructor.
  rewrite path_wp_pure_eq; intros (vp & Hp & vq & Hlook & ->).
  move: (IHp _ Hp) => [n Hpure].
  exists (S n) => _.
  eapply nsteps_r.
  - by apply (pure_step_nsteps_ctx (fill_item (ProjCtx l))), Hpure.
  - apply nsteps_once_inv, pure_tproj, Hlook.
Qed.

Definition alias_paths p q :=
  path_wp_pure q (λ vp, path_wp_pure p (eq vp)).

Lemma alias_paths_pv_eq_1 p vr :
  alias_paths p (pv vr) ↔ path_wp_pure p (eq vr).
Proof. done. Qed.

Hint Extern 1 (path_wp_pure _ _) => by apply path_wp_pure_swap : core.

Lemma alias_paths_pv_eq_2 p vr :
  alias_paths (pv vr) p ↔ path_wp_pure p (eq vr).
Proof. by rewrite -path_wp_pure_swap. Qed.

Lemma alias_paths_self p v :
  alias_paths p (pv v) → alias_paths p p.
Proof.
  rewrite alias_paths_pv_eq_1 /alias_paths !path_wp_pure_eq; naive_solver.
Qed.

Lemma alias_paths_refl_vl v :
  alias_paths (pv v) (pv v).
Proof. done. Qed.

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

Section path_wp.
  Context {Σ : gFunctors}.
  Implicit Types (φ : vl -d> iPropO Σ).

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

  Lemma path_wp_exec p v :
    path_wp p (λ w, ⌜ v = w ⌝) ⊢@{iPropI Σ}
    ⌜ ∃ n, PureExec True n (path2tm p) (tv v) ⌝.
  Proof. iIntros "!%". apply path_wp_exec_pure. Qed.

  Lemma path_wp_pure_exec p φ :
    path_wp p φ ⊢ ∃ v, ⌜ ∃ n, PureExec True n (path2tm p) (tv v) ⌝ ∧ φ v.
  Proof.
    rewrite path_wp_eq. setoid_rewrite <-path_wp_exec.
    iDestruct 1 as (v Hcl) "H". eauto.
  Qed.

  Context {Hdlang : dlangG Σ}.
  Lemma path_wp_to_wp p φ :
    path_wp p (λ v, φ v) -∗
    WP (path2tm p) {{ v, φ v }}.
  Proof.
    rewrite path_wp_pure_exec; iDestruct 1 as (v [n Hex]) "H".
    by rewrite -wp_pure_step_later // -wp_value.
  Qed.

  Global Instance path_wp_timeless p Pv: Timeless (path_wp p (λ v, ⌜Pv v⌝))%I.
  Proof. rewrite path_wp_pureable. apply _. Qed.

  Lemma path_wp_terminates p φ :
    path_wp p φ ⊢ ⌜ terminates (path2tm p) ⌝.
  Proof.
    rewrite path_wp_pure_exec; iDestruct 1 as (v [n Hp]) "_"; iIntros "!%".
    exact: PureExec_to_terminates.
  Qed.
End path_wp.
