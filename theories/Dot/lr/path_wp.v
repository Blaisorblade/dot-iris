From iris.proofmode Require Import tactics.
From D Require Import iris_prelude.
From D.Dot Require Import dlang_inst rules.
From D.pure_program_logic Require Import lifting.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx) (ρ : env) (Pv : vl → Prop).

(* Auxiliary. *)
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

Section path_wp.
  Context `{HdlangG: dlangG Σ}.
  Implicit Types (φ : vl -d> iPropO Σ).
  Notation path_wp_purel p Pv := (⌜path_wp_pure p Pv⌝ : iProp Σ)%I.

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
    path_wp p (λ v, ⌜Pv v⌝) ⊣⊢ path_wp_purel p Pv.
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
  Instance: IntoPure
    (path_wp p (λ v0 : vl, ∃ w0 : vl_, ⌜v0 @ l ↘ dvl w0⌝ ∧ ⌜w = w0⌝))%I
    (path_wp_pure p (λ v0 : vl, ∃ w0 : vl_, v0 @ l ↘ dvl w0 ∧ w = w0)) := _.
  Instance: FromPure false
    (path_wp p (λ v0 : vl, ∃ w0 : vl_, ⌜v0 @ l ↘ dvl w0⌝ ∧ ⌜w = w0⌝))%I
    (path_wp_pure p (λ v0 : vl, ∃ w0 : vl_, v0 @ l ↘ dvl w0 ∧ w = w0)) := _.

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

  Lemma path_wp_exec_pure p v :
    path_wp_pure p (eq v)
    → PureExec True (plength p) (path2tm p) (tv v).
  Proof.
    elim: p v => [w|p IHp l] v; rewrite /PureExec/=.
    by intros -> _; constructor.
    rewrite path_wp_pure_eq; intros (vp & Hp & vq & Hlook & ->) _.
    move: (IHp _ Hp) => Hpure.
    eapply nsteps_r.
    - by apply (pure_step_nsteps_ctx (fill_item (ProjCtx l))), Hpure.
    - apply nsteps_once_inv, pure_tproj, Hlook.
  Qed.

  Lemma path_wp_exec p v :
    path_wp p (λ w, ⌜ v = w ⌝) ⊢@{iPropI Σ}
    ⌜ PureExec True (plength p) (path2tm p) (tv v) ⌝.
  Proof. iIntros "!%". apply path_wp_exec_pure. Qed.

  Lemma path_wp_adequacy p φ :
    path_wp p φ ⊢ (∃ v, ⌜ PureExec True (plength p) (path2tm p) (tv v) ⌝ ∧ φ v).
  Proof.
    rewrite path_wp_eq. setoid_rewrite <-path_wp_exec.
    iDestruct 1 as (v Hcl) "H". eauto.
  Qed.

  Lemma path_wp_to_wp p φ :
    path_wp p (λ v : vl, φ v) -∗
    WP (path2tm p) {{ v, φ v }}.
  Proof.
    rewrite path_wp_adequacy; iDestruct 1 as (v Hex) "H".
    by rewrite -wp_pure_step_later // -wp_value.
  Qed.

  Global Instance path_wp_timeless p Pv: Timeless (path_wp p (λ v, ⌜Pv v⌝))%I.
  Proof. rewrite path_wp_pureable. apply _. Qed.
End path_wp.
