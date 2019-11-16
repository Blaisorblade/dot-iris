(** Define "stamping" in a purely syntactic
    way, without involving Iris. *)
From stdpp Require Import gmap.
From D.DSub Require Import syn traversals.

Set Implicit Arguments.

Notation stys := (gmap stamp ty).
Class stampTable := getStampTable : stys.

Import Trav1.
Set Implicit Arguments.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx) (vs: vls) (g: stys) (n: nat).

Notation valid_stamp g g' n' vs s T' :=
  (g !! s = Some T' ∧ g' = g ∧ n' = length vs).

Definition is_unstamped_trav: Traversal unit :=
  {|
    upS := id;
    varP := λ s n, True;
    vtyP := λ s T, True;
    vstampP := λ ts vs s T' ts', False;
    pathP := λ s v, ∃ x, v = var_vl x;
  |}.

Definition is_stamped_trav: Traversal (nat * stys) :=
  {|
    upS := λ '(n, g), (S n, g);
    varP := λ '(n, g) i, i < n;
    vtyP := λ ts T, False;
    vstampP := λ '(n, g) vs s T' '(n', g'), valid_stamp g g' n' vs s T';
    pathP := λ ts v, True;
  |}.

Notation is_unstamped_tm := (forall_traversal_tm is_unstamped_trav ()).
Notation is_unstamped_vl := (forall_traversal_vl is_unstamped_trav ()).
Notation is_unstamped_ty := (forall_traversal_ty is_unstamped_trav ()).

Notation is_stamped_tm n g := (forall_traversal_tm is_stamped_trav (n, g)).
Notation is_stamped_vl n g := (forall_traversal_vl is_stamped_trav (n, g)).
Notation is_stamped_ty n g := (forall_traversal_ty is_stamped_trav (n, g)).

Notation is_stamped_σ n g σ := (Forall (is_stamped_vl n g) σ).

(** Next, we define "extraction", which is the core of stamping.
    Extraction (as defined by [extraction]) is a relation, stable under
    substitution, between a type and its extracted form.

    An extracted type is basically a stamp pointing into a table, where types
    are allocated. However, we cannot substitute into such opaque pointers
    directly, so how can we ensure stability under substitution?
    To this end, extracted types also contain an environment on which
    substitution can act.
    The function [extract] extracts types by allocating them into a table and
    creating an initial environment.
 *)
Definition extractedTy: Type := stamp * vls.
Definition extractionResult: Type := stys * extractedTy.

Implicit Types (sσ: extractedTy) (gsσ: extractionResult).

Notation gdom g := (dom (gset stamp) g).

Definition fresh_stamp {X} (g: gmap stamp X): stamp := fresh (dom (gset stamp) g).

Definition extract g n T: stys * extractedTy :=
  let s := fresh_stamp g
  in (<[s := T]> g, (s, idsσ n)).

Definition extraction n T : (stys * extractedTy) → Prop :=
  λ '(g, (s, σ)),
  ∃ T', g !! s = Some T' ∧ T'.|[to_subst σ] = T ∧
    Forall (is_stamped_vl n g) σ ∧ is_stamped_ty (length σ) g T'.
Notation "T ~[ n  ] gsσ" := (extraction n T gsσ) (at level 70).

Ltac with_is_unstamped tac :=
  match goal with
    | H: is_unstamped_ty   _ |- _ => tac H
    | H: is_unstamped_tm   _ |- _ => tac H
    | H: is_unstamped_vl   _ |- _ => tac H
  end.

Ltac with_is_stamped tac :=
  match goal with
    | H: is_stamped_ty _ _ _ |- _ => tac H
    | H: is_stamped_tm _ _ _ |- _ => tac H
    | H: is_stamped_vl _ _ _ |- _ => tac H
  end.

Lemma not_stamped_vty g n T:
  ¬ (is_stamped_vl n g (vty T)).
Proof. by inversion 1. Qed.

Lemma is_stamped_vty_mono g1 g2 n T:
  g1 ⊆ g2 →
  is_stamped_vl n g1 (vty T) →
  is_stamped_vl n g2 (vty T).
Proof. intros; exfalso. by eapply not_stamped_vty. Qed.

Lemma is_stamped_mono_tm g1 g2 n e__s:
  g1 ⊆ g2 →
  is_stamped_tm n g1 e__s →
  is_stamped_tm n g2 e__s
with is_stamped_mono_vl g1 g2 n v__s:
  g1 ⊆ g2 →
  is_stamped_vl n g1 v__s →
  is_stamped_vl n g2 v__s
with is_stamped_mono_ty g1 g2 n T__s:
  g1 ⊆ g2 →
  is_stamped_ty n g1 T__s →
  is_stamped_ty n g2 T__s.
Proof.
  all: intros Hleg Hst; dependent induction Hst.
  all: try solve [constructor;
    by [| exact: (is_stamped_mono_tm _ _ _ _ Hleg)
        | exact: (is_stamped_mono_vl _ _ _ _ Hleg)
        | exact: (is_stamped_mono_ty _ _ _ _ Hleg)]].

  - move: ts' H H0 H1 => /= [l g0] [Hgs [-> Heq]] HstT Hstvs.
    eapply @trav_vstamp with (T' := T') (ts' := (length vs, g2)) => //=.
    split_and!; by [|eapply map_subseteq_spec].
    subst l; exact: (is_stamped_mono_ty _ _ _ _ Hleg).
    (* Termination checking requires here a nested induction. *)
    elim: Hstvs {Heq} => [|v vs' Hv H IHHstvs]; constructor;
      by [| apply: (is_stamped_mono_vl _ _ _ _ Hleg Hv)].
Qed.

Lemma is_stamped_mono_σ g1 g2 n σ:
  g1 ⊆ g2 →
  is_stamped_σ n g1 σ →
  is_stamped_σ n g2 σ.
Proof. intros; decompose_Forall. exact: is_stamped_mono_vl. Qed.

Hint Extern 5 (is_stamped_ty _ _ _) => try_once is_stamped_mono_ty : core.
Hint Extern 5 (is_stamped_σ _ _ _) => try_once is_stamped_mono_σ : core.
