From iris.algebra Require Export base.
From iris.base_logic Require Import upred.
From iris.program_logic Require Import weakestpre.
From iris.base_logic Require Import invariants.
From Autosubst Require Export Autosubst.
Import uPred.

Canonical Structure varC := leibnizC var.

Section Autosubst_Lemmas.
  Context {term : Type} {Ids_term : Ids term}
          {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}.

  Lemma iter_up (m x : nat) (f : var → term) :
    upn m f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
  Proof.
    revert x; induction m as [|m IH]=> -[|x];
      repeat (case_match || asimpl || rewrite IH); auto with omega.
  Qed.

  Lemma upn_comp n m f: upn n (upn m f) = upn (n + m) f.
  Proof.
    revert m; induction n => m; first done.
    rewrite -fold_upn_up fold_up_upn; simpl.
    replace (S (n + m)) with (n + S m) by omega; auto.
  Qed.

End Autosubst_Lemmas.

Ltac properness :=
  repeat match goal with
  | |- (∃ _: _, _)%I ≡ (∃ _: _, _)%I => apply exist_proper =>?
  | |- (∀ _: _, _)%I ≡ (∀ _: _, _)%I => apply forall_proper =>?
  | |- (_ ∧ _)%I ≡ (_ ∧ _)%I => apply and_proper
  | |- (_ ∨ _)%I ≡ (_ ∨ _)%I => apply or_proper
  | |- (_ → _)%I ≡ (_ → _)%I => apply impl_proper
  | |- (_ -∗ _)%I ≡ (_ -∗ _)%I => apply wand_proper
  | |- (WP _ {{ _ }})%I ≡ (WP _ {{ _ }})%I => apply wp_proper =>?
  | |- (▷ _)%I ≡ (▷ _)%I => apply later_proper
  | |- (□ _)%I ≡ (□ _)%I => apply persistently_proper
  | |- (_ ∗ _)%I ≡ (_ ∗ _)%I => apply sep_proper
  | |- (inv _ _)%I ≡ (inv _ _)%I => apply (contractive_proper _)
  end.

Ltac solve_proper_alt :=
  repeat intro; (simpl + idtac);
  by repeat match goal with H : _ ≡{_}≡ _|- _ => rewrite H end.

(* Reserved Notation "⟦ τ ⟧" (at level 0, τ at level 70). *)
(* Reserved Notation "⟦ τ ⟧ₑ" (at level 0, τ at level 70). *)
(* Reserved Notation "⟦ Γ ⟧*" (at level 0, Γ at level 70). *)

Lemma list_cons_inv (A : Type) (x x' : A) (l l' : list A) :
  x :: l = x' :: l' → x = x' ∧ l = l'.
Proof. inversion 1; subst; tauto. Qed.

Lemma list_app_increasing_base (A : Type) (ll l lr : list A) :
  l = ll ++ l ++ lr → ll = [] ∧ lr = [].
Proof.
  revert ll lr.
  induction l => ll lr Heq; simpl in *.
  - by apply app_eq_nil.
  - destruct ll as [|b ll]; first destruct lr; first done; simpl in *.
    + apply list_cons_inv in Heq; destruct Heq as [_ Heq].
      by apply (IHl []) in Heq.
    + apply list_cons_inv in Heq; destruct Heq as [? Heq]; subst.
      change (b :: l ++ lr) with ([b] ++ l ++ lr) in Heq.
      rewrite app_assoc in Heq.
      apply IHl in Heq; destruct Heq as [Heq _].
      exfalso; eapply app_cons_not_nil; eauto.
Qed.

Lemma list_app_increasing (A : Type) (l1 l2 l1' l2' : list A) :
  l1 = l2 ++ l2' → l2 = l1 ++ l1' → l1 = l2.
Proof.
  intros Heq1 Heq2.
  pose proof Heq1 as Heq1'; rewrite Heq2 -assoc in Heq1'.
  apply (list_app_increasing_base _ []) in Heq1'; destruct Heq1' as [_ Heq1'].
  apply app_eq_nil in Heq1'; intuition subst; eauto using app_nil_r.
Qed.

Lemma list_app_increasing' (A : Type) (l1 l2 l1' l2' : list A) :
  l1 = l2' ++ l2 → l2 = l1' ++ l1 → l1 = l2.
Proof.
  intros Heq1 Heq2.
  pose proof Heq1 as Heq1';
    rewrite Heq2 assoc -(app_nil_r ((l2' ++ l1') ++ l1)) -assoc in Heq1'.
  eapply (list_app_increasing_base _ _ _ []) in Heq1'.
  destruct Heq1' as [Heq1' _].
  apply app_eq_nil in Heq1'; intuition subst; auto.
Qed.