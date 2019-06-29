From D Require Export prelude proofmode_extra.
From iris.base_logic Require Import upred.
From D.pure_program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics.

(* From iris.base_logic Require Import invariants. *)

Export uPred.

Ltac properness :=
  repeat match goal with
  | |- (∃ _: _, _)%I ≡ (∃ _: _, _)%I => apply bi.exist_proper =>?
  | |- (∀ _: _, _)%I ≡ (∀ _: _, _)%I => apply bi.forall_proper =>?
  | |- (_ ∧ _)%I ≡ (_ ∧ _)%I => apply bi.and_proper
  | |- (_ ∨ _)%I ≡ (_ ∨ _)%I => apply bi.or_proper
  | |- (_ → _)%I ≡ (_ → _)%I => apply bi.impl_proper
  | |- (_ -∗ _)%I ≡ (_ -∗ _)%I => apply bi.wand_proper
  | |- (WP _ {{ _ }})%I ≡ (WP _ {{ _ }})%I => apply wp_proper =>?
  | |- (▷ _)%I ≡ (▷ _)%I => apply bi.later_proper
  | |- (□ _)%I ≡ (□ _)%I => apply bi.intuitionistically_proper
  | |- (_ ∗ _)%I ≡ (_ ∗ _)%I => apply bi.sep_proper
  (* | |- (inv _ _)%I ≡ (inv _ _)%I => apply (contractive_proper _) *)
  end.

Ltac solve_proper_alt :=
  repeat intro; (simpl + idtac);
  by repeat match goal with H : _ ≡{_}≡ _|- _ => rewrite H end.

(** An ad-hoc variant of solve_proper that seems to work better when defining
      proper higher-order functions. In particular, using intro allows showing that a
      lambda abstraction is proper if its body is proper.
      Its implementation can also prove [f1 x ≡ f2 x] from [H : f1 ≡ f2]:
      neither f_equiv nor rewrite deal with that, but [apply H] does. *)
Ltac solve_proper_ho_core tac :=
  solve [repeat intro; cbn; repeat tac (); cbn in *;
  repeat match goal with H : _ ≡{_}≡ _|- _ => apply H end].
Ltac solve_proper_ho := solve_proper_ho_core ltac:(fun _ => f_equiv).
Ltac solve_contractive_ho := solve_proper_ho_core ltac:(fun _ => f_contractive || f_equiv).
