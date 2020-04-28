From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_language.
From iris.base_logic Require Import upred.

From D.pure_program_logic Require Export weakestpre.
From D Require Export prelude proofmode_extra.

Export uPred.

Tactic Notation "smart_wp_bind" uconstr(ctx) ident(v) constr(Hv) uconstr(Hp) :=
  iApply (wp_bind (fill[ctx]));
  iApply (wp_wand with "[-]"); [iApply Hp; trivial|]; cbn;
  iIntros (v) Hv.

(* Instances for [IntoVal], used e.g. by [wp_value]; copied from F_mu. *)
Hint Extern 5 (IntoVal _ _) => eapply of_to_val; fast_done : typeclass_instances.
Hint Extern 10 (IntoVal _ _) =>
  rewrite /IntoVal; eapply of_to_val; rewrite /= !to_of_val /=; solve [ eauto ] : typeclass_instances.

(* Do not export iris.proofmode.tactics! *)
(* From iris.proofmode Require Export tactics. *)
(* As discussed in https://github.com/Blaisorblade/dot-iris/pull/2#discussion_r239389417, exporting that confuses Coq, who then
  prints [length] as [strings.length]. *)

(** Notation for functions in the Iris scope. *)
Notation "'λI' x .. y , t" := (fun x => .. (fun y => t%I) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : function_scope.

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
  | |- (▷^_ _)%I ≡ (▷^_ _)%I => apply bi.laterN_proper
  | |- (□ _)%I ≡ (□ _)%I => apply bi.intuitionistically_proper
  | |- (_ ∗ _)%I ≡ (_ ∗ _)%I => apply bi.sep_proper
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
Ltac solve_proper_ho_alt := solve_proper_ho_core ltac:(fun _ => f_equiv).
Ltac solve_contractive_ho_alt := solve_proper_ho_core ltac:(fun _ => f_contractive || f_equiv).

Ltac ho_f_equiv :=
  match goal with
  | H : _ ≡ _|- _ => apply: H || rewrite H //
  | H : _ ≡{_}≡ _ |- _ => apply: H || rewrite H //
  | H : dist_later _ _ _ |- _ => apply: H || rewrite H //
  end.

Ltac solve_proper_ho := solve_proper_core ltac:(fun _ => ho_f_equiv || f_equiv).
Ltac solve_contractive_ho := solve_proper_core ltac:(fun _ => ho_f_equiv || f_contractive || f_equiv).
