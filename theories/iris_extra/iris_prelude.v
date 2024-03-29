(** Prelude for Iris-based code.
This file adds or re-exports utilities that should always be available.
*)
From iris.proofmode Require Export proofmode.

From iris.base_logic Require Import base_logic.
Export uPred.

From D.pure_program_logic Require Export weakestpre.
From D Require Export prelude proofmode_extra.

(** * Notation for functions in the Iris scope. *)
Notation "'λI' x .. y , t" := (fun x => .. (fun y => t%I) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : function_scope.

Notation "'λneI' x .. y , t" := (λne x, .. (λne y, t%I) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : function_scope.

(** * Automation for Iris program logic. *)
(** Instances for [IntoVal], used e.g. by [wp_value]; copied from F_mu. *)
#[global] Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
#[global] Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=;
  solve [ eauto ] : typeclass_instances.


(** * Setoid rewriting *)

(** ** Enable rewriting from [f x] to [g x] with [f ≡ g]. *)

#[global] Instance equiv_ext_dfun2_pointwise {A B} :
  subrelation (≡@{A -d> B}) (pointwise_relation A (≡)).
Proof. done. Qed.

#[global] Instance dist_ext_dfun2_pointwise {A B n} :
  subrelation (dist n (A := A -d> B)) (pointwise_relation A (dist n)).
Proof. done. Qed.

#[global] Instance equiv_ext_dfun2_forall {A B} :
  subrelation (≡@{A -d> B}) (forall_relation (const (≡))).
Proof. done. Qed.
#[global] Instance dist_ext_dfun2_forall {A B n} :
  subrelation (dist n (A := A -d> B)) (forall_relation (const (dist n))).
Proof. done. Qed.

#[global] Instance equiv_ext_dfun3_forall {A B C} :
  subrelation (≡@{A -d> B -d> C})
    (forall_relation (const (forall_relation (const (≡))))).
Proof. done. Qed.
#[global] Instance dist_ext_dfun3_forall {A B C n} :
  subrelation (dist n (A := A -d> B -d> C))
    (forall_relation (const (forall_relation (const (dist n))))).
Proof. done. Qed.

(** * Tactics for manipulating and using Proper instances. *)

(** Specialized version of [f_equiv]. *)
Ltac properness :=
  repeat match goal with
  | |- (∃ _ : _, _)%I ≡ (∃ _ : _, _)%I => apply bi.exist_proper =>?
  | |- (∀ _ : _, _)%I ≡ (∀ _ : _, _)%I => apply bi.forall_proper =>?
  | |- (_ ∧ _)%I ≡ (_ ∧ _)%I => apply bi.and_proper
  | |- (_ ∨ _)%I ≡ (_ ∨ _)%I => apply bi.or_proper
  | |- (_ → _)%I ≡ (_ → _)%I => apply bi.impl_proper
  | |- (_ -∗ _)%I ≡ (_ -∗ _)%I => apply bi.wand_proper
  | |- (WP _ {{ _ }})%I ≡ (WP _ {{ _ }})%I => apply wp_proper =>?
  | |- (▷ _)%I ≡ (▷ _)%I => apply bi.later_proper
  | |- (▷^_ _)%I ≡ (▷^_ _)%I => apply bi.laterN_proper
  | |- (□ _)%I ≡ (□ _)%I => apply bi.intuitionistically_proper
  | |- (|==> _)%I ≡ (|==> _)%I => apply bupd_proper
  | |- (_ ∗ _)%I ≡ (_ ∗ _)%I => apply bi.sep_proper
  end.

(** ** Variants of [solve_proper] and [solve_contractive] that are more effective
for higher-order functions. *)

(** Prove [f x y z ≡ g x y z] from equalities of functions [f ≡ g].
Complements [f_equiv] for use in [solve_proper_ho].
This is _not_ just [assumption]. *)
Ltac hof_eq_app :=
  match goal with
  | H : _ ≡ _|- _ => apply: H
  | H : _ ≡{_}≡ _ |- _ => apply: H
  | H : dist_later _ _ _ |- _ => apply: H
  end.

(** ** Our best [solve_proper]/[solve_contractive] extension for higher-order
functions. *)
Ltac solve_proper_ho := solve_proper_core ltac:(fun _ => hof_eq_app || f_equiv).
Ltac solve_contractive_ho :=
  solve_proper_core ltac:(fun _ => hof_eq_app || f_contractive || f_equiv).

(** ** Other [solve_proper]/[solve_contractive] extensions for higher-order
functions, which might or might not be useful sometimes. *)

Ltac solve_proper_alt :=
  repeat intro; (simpl + idtac);
  by repeat match goal with H : _ ≡{_}≡ _|- _ => rewrite H end.

(** An ad-hoc variant of solve_proper that seems to work better when defining
proper higher-order functions. *)
(* In particular, using intro allows showing that
a lambda abstraction is proper if its body is proper. Its implementation can
also prove [f1 x ≡ f2 x] from [H : f1 ≡ f2]: neither f_equiv nor rewrite deal
with that, but [apply H] does. *)
Ltac solve_proper_ho_core tac :=
  solve [repeat intro; cbn; repeat tac (); cbn in *;
  repeat match goal with H : _ ≡{_}≡ _|- _ => apply H end].
Ltac solve_proper_ho_alt := solve_proper_ho_core ltac:(fun _ => f_equiv).
Ltac solve_contractive_ho_alt :=
  solve_proper_ho_core ltac:(fun _ => f_contractive || f_equiv).

Ltac deep_ho_f_equiv :=
  match goal with
  | H : _ ≡ _|- _ => apply: H || rewrite H //
  | H : _ ≡{_}≡ _ |- _ => apply: H || rewrite H //
  | H : dist_later _ _ _ |- _ => apply: H || rewrite H //
  end.

Ltac deep_solve_proper_ho :=
  solve_proper_core ltac:(fun _ => deep_ho_f_equiv || f_equiv).
Ltac deep_solve_contractive_ho :=
  solve_proper_core ltac:(fun _ => deep_ho_f_equiv || f_contractive || f_equiv).
