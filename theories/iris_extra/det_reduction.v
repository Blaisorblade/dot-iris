From D Require Import prelude.
From iris.program_logic Require language ectx_language.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

Set Implicit Arguments.
Unset Strict Implicit.

Module L := language.
Module EL := ectx_language.
Import L EL.
Implicit Types (Λ : language).

Instance Proper_LanguageCtx Λ:
  Proper (pointwise_relation _ (=) ==> impl) (@LanguageCtx Λ).
Proof.
  intros K1 K2 Heq [???]; split; intros *; setoid_rewrite <-Heq => *; auto 2.
Qed.

Instance unit_pi: ProofIrrel ().
Proof. by intros [] []. Qed.

Class UniqueInhabited A := {
  unique_inhabited :> Inhabited A;
  unique_proof_irrel :> ProofIrrel A;
}.

Class LangDet Λ := {
  prim_step_PureExec (e1 e2 : L.expr Λ) σ1 κ σ2 efs :
    L.prim_step e1 σ1 κ e2 σ2 efs → PureExec True 1 e1 e2;
  lang_inh_state :> UniqueInhabited (L.state Λ)
}.

Class EctxLangDet (Λ : EL.ectxLanguage) := {
  head_step_PureExec (e1 e2 : L.expr Λ) σ1 κ σ2 efs :
    EL.head_step e1 σ1 κ e2 σ2 efs → L.PureExec True 1 e1 e2;
  ectx_inh_state :> UniqueInhabited (L.state Λ)
}.

Notation dummyState := (inhabitant (A := L.state _)).

Ltac uniqueState :=
  repeat match goal with
  | s : L.state _ |- _ => assert (s = dummyState) as -> by apply: proof_irrel
  end.

(** This defines, in fact, pure and deterministic termination. *)
Definition terminates {Λ} (e : L.expr Λ) :=
  ∃ v : L.val Λ, rtc pure_step e (L.of_val v).

Lemma PureExec_to_terminates {Λ : L.language} n φ e v :
  PureExec φ n e (L.of_val v) → φ → terminates (Λ := Λ) e.
Proof. intros HP Hφ. exists v. eapply nsteps_rtc, HP, Hφ. Qed.

Notation not_stuck e := (L.not_stuck e dummyState).

Definition safe_gen {Λ} (e : L.expr Λ) :=
  ∀ e' thp σ σ', rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
    L.not_stuck e' σ'.

Definition safe_simpl `{!LangDet Λ} (e : L.expr Λ) :=
  ∀ e', rtc pure_step e e' → not_stuck e'.

Hint Constructors rtc : core.

Section LangDet.

Context {Λ}.
Implicit Type (e t : L.expr Λ).

Lemma pure_to_prim e1 e2 σ:
  pure_step e1 e2 →
  L.prim_step e1 σ [] e2 σ [].
Proof.
  move => [/(_ σ) [? [? [? Hsafe]]] Hpure].
  edestruct Hpure; [exact: Hsafe|] => {Hpure}. naive_solver.
Qed.

Context `{!LangDet Λ}.
Lemma prim_step_pure {e1 e2 σ1 κ σ2 efs} :
  L.prim_step e1 σ1 κ e2 σ2 efs → pure_step e1 e2.
Proof. move => /prim_step_PureExec /(_ I). exact: nsteps_once_inv. Qed.

Lemma prim_step_pure_eq σ e1 e2 :
  L.prim_step e1 σ [] e2 σ [] ↔ pure_step e1 e2.
Proof.
  split; first exact: prim_step_pure.
  exact: pure_to_prim.
Qed.

Lemma prim_step_pure_eq' e1 e2 :
  L.prim_step e1 dummyState [] e2 dummyState [] ↔ pure_step e1 e2.
Proof. exact: prim_step_pure_eq. Qed.

Lemma pure_step_det' {e1 e2 e2' σ1 κ σ2 efs} :
  pure_step e1 e2 → L.prim_step e1 σ1 κ e2' σ2 efs →
  e2' = e2 ∧ κ = [] ∧ σ2 = σ1 ∧ efs = [].
Proof. intros Hpure ?; edestruct (pure_step_det _ _ Hpure); naive_solver. Qed.

Lemma prim_step_det e1 e2 e2' σ1 κ σ2 efs :
  L.prim_step e1 σ1 κ e2 σ2 efs →
  L.prim_step e1 σ1 κ e2' σ2 efs → e2 = e2'.
Proof.
  by move => /prim_step_pure + Hstep => /pure_step_det' /(_ Hstep) [? _].
Qed.

Lemma pure_step_det e1 e2 e2' :
  pure_step e1 e2 → pure_step e1 e2' → e2 = e2'.
Proof. rewrite -!prim_step_pure_eq'. exact: prim_step_det. Qed.

Lemma prim_step_inversion e1 σ1 κ e2 σ2 efs :
  L.prim_step e1 σ1 κ e2 σ2 efs →
  σ2 = σ1 ∧ κ = [] ∧ efs = [].
Proof.
  intros Hstep; have Hpure := prim_step_pure Hstep;
    have ? := pure_step_det' Hpure Hstep; naive_solver.
Qed.

Ltac prim_step_inversion H :=
  destruct (prim_step_inversion H); destruct_and!; simplify_eq/=.

Lemma prim_step_view e1 σ1 κ e2 σ2 efs
  (Hstep : L.prim_step e1 σ1 κ e2 σ2 efs) :
  L.prim_step e1 σ1 [] e2 σ2 [].
Proof. by prim_step_inversion Hstep. Qed.

Lemma prim_step_step e1 σ κ e2 σ' efs :
  L.prim_step e1 σ κ e2 σ' efs → L.step ([e1], σ) [] ([e2], σ').
Proof.
  move => /prim_step_view. by eapply step_atomic with (t1 := []) (t2 := []).
Qed.
Hint Immediate prim_step_step : core.

Lemma step_inversion e1 thp σ σ' κ :
  step ([e1], σ) κ (thp, σ') →
  ∃ e2, thp = [e2] ∧ κ = [] ∧ L.prim_step e1 σ [] e2 σ' [].
Proof.
  destruct 1 as [????? t0 ??? Hstep]; destruct t0 as [|?[]]; [| naive_solver..].
  prim_step_inversion Hstep; eauto.
Qed.

Lemma step_inversion' e1 e2 thp σ σ' κ :
  step ([e1], σ) κ (thp, σ') → e2 ∈ thp →
  thp = [e2] ∧ κ = [] ∧ L.prim_step e1 σ [] e2 σ' [].
Proof.
  move => /step_inversion [e2' [-> [->]]].
  rewrite elem_of_list_singleton. naive_solver.
Qed.

Definition erased_step' e1 e2 := erased_step ([e1], dummyState) ([e2], dummyState).

Lemma pure_step_erased e1 e2 :
  pure_step e1 e2 ↔ erased_step ([e1], dummyState) ([e2], dummyState).
Proof.
  split => Hsafe.
  - by eexists; eapply prim_step_step, prim_step_pure_eq.
  - destruct Hsafe as [l Hsafe%step_inversion].
    eapply prim_step_pure; naive_solver.
Qed.

Lemma erased_step_inversion t1 σ res :
  erased_step ([t1], σ) res →
  ∃ t2, res = ([t2], σ) ∧ L.prim_step t1 σ [] t2 σ [].
Proof. case: res => ?? [? /step_inversion H]; uniqueState. naive_solver. Qed.
(*
Lemma erased_step_inversion1 {t1 thp σ σ'} :
  erased_step ([t1], σ) (thp, σ') →
  ∃ t2, thp = [t2] ∧ L.prim_step t1 σ [] t2 σ' [].
Proof. move => /erased_step_inversion; naive_solver. Qed. *)

Lemma pure_steps_erased e1 e2 :
  rtc pure_step e1 e2 ↔ rtc erased_step' e1 e2.
Proof.
  by split; eapply rtc_congruence with (f := id) => ?? /pure_step_erased.
Qed.
End LangDet.

Hint Resolve ->pure_step_erased : core.
Hint Resolve <-pure_step_erased : core.

Lemma rtc_erased_step_inversion' `{!LangDet Λ} {t1 : L.expr Λ} {res σ}
  (Hs : rtc erased_step ([t1], σ) res) :
  ∃ t2, res = ([t2], σ).
Proof.
  move E: ([t1], σ) Hs => cfg Hs.
  elim: Hs t1 E; intros; first naive_solver.
  edestruct erased_step_inversion; naive_solver.
Qed.

(* Out of the section to workaround bugs with dependent induction. *)
Lemma pure_steps_erased' `{LangDet Λ} e1 e2 :
  rtc pure_step e1 e2 ↔ rtc erased_step ([e1], dummyState) ([e2], dummyState).
Proof.
  split; rewrite !pure_steps_erased /erased_step'.
  - induction 1; naive_solver.
  - move E1: ([e1], dummyState) => c1.
    move E2: ([e2], dummyState) => c2 Hs.
    elim: Hs e1 e2 E1 E2; intros; first naive_solver.
    edestruct erased_step_inversion; naive_solver.
Qed.

Section LangDet.
Context `{!LangDet Λ}.
Implicit Type (e t : L.expr Λ).

Theorem rtc_erased_step_inversion {t1 t2 σ σ' thp} :
  rtc erased_step ([t1], σ) (thp, σ') → t2 ∈ thp →
  rtc erased_step ([t1], σ) ([t2], σ').
Proof.
  move=> Hs; have [t2' ?] := rtc_erased_step_inversion' Hs; simplify_eq.
  by move /elem_of_list_singleton ->.
Qed.

Lemma safe_equiv e : safe_gen e ↔ safe_simpl e.
Proof.
  rewrite /safe_simpl /safe_gen; split; intros Hsafe ?*.
  - intros Hred%pure_steps_erased'.
    by eapply (Hsafe e'), elem_of_list_singleton.
  - move => + Hin => /rtc_erased_step_inversion /(_ Hin).
    uniqueState => /pure_steps_erased'. naive_solver.
Qed.
End LangDet.

Section EctxLangDet.
Context {Λ : ectxLanguage} `{EctxLangDet Λ}.

Global Instance EctxLangDet_LangDet : LangDet Λ.
Proof.
  split; [|by apply _] => e1 e2 σ1 κ σ2 efs.
  inversion 1; simplify_eq/=. by eapply pure_exec_fill, head_step_PureExec.
Qed.
End EctxLangDet.

Notation safe := safe_simpl.
