(** Define "stamping" in a purely syntactic
    way, without involving Iris. *)
From stdpp Require Import gmap.
From D.Dot Require Import syn traversals.

Set Implicit Arguments.

Notation stys := (gmap stamp ty).
Class stampTable := getStampTable : stys.

Import Trav1.
Set Implicit Arguments.

Implicit Types
         (T: ty) (v: vl) (e: tm) (p: path) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx) (g: stys) (n: nat).

Fixpoint path_root (p : path): vl :=
  match p with
  | pv v => v
  | pself p _ => path_root p
  end.

Notation valid_stamp g g' n' vs s T' :=
  (g !! s = Some T' ∧ g' = g ∧ n' = length vs).

Definition is_unstamped_trav: Traversal nat :=
  {|
    upS := S;
    varP := λ n i, i < n;
    dtysynP := λ _ T, True;
    dtysemP := λ _ vs s T' ts', False;
    tselP := λ s p, ∃ x, path_root p = var_vl x;
  |}.

Definition is_stamped_trav: Traversal (nat * stys) :=
  {|
    upS := λ '(n, g), (S n, g);
    varP := λ '(n, g) i, i < n;
    dtysynP := λ ts T, False;
    dtysemP := λ '(n, g) vs s T' '(n', g'), valid_stamp g g' n' vs s T';
    tselP := λ ts p, True;
  |}.

Notation is_unstamped_tm n := (forall_traversal_tm is_unstamped_trav n).
Notation is_unstamped_vl n := (forall_traversal_vl is_unstamped_trav n).
Notation is_unstamped_dm n := (forall_traversal_dm is_unstamped_trav n).
Notation is_unstamped_path n := (forall_traversal_path is_unstamped_trav n).
Notation is_unstamped_ty n := (forall_traversal_ty is_unstamped_trav n).

Notation is_unstamped_dms n ds := (forall_traversal_dms is_unstamped_trav n ds).
Notation is_unstamped_σ n σ := (Forall (is_unstamped_vl n) σ).

Notation is_stamped_tm n g := (forall_traversal_tm is_stamped_trav (n, g)).
Notation is_stamped_vl n g := (forall_traversal_vl is_stamped_trav (n, g)).
Notation is_stamped_dm n g := (forall_traversal_dm is_stamped_trav (n, g)).
Notation is_stamped_path n g := (forall_traversal_path is_stamped_trav (n, g)).
Notation is_stamped_ty n g := (forall_traversal_ty is_stamped_trav (n, g)).

Notation is_stamped_dms n g ds := (forall_traversal_dms is_stamped_trav (n, g) ds).
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
    | H: is_unstamped_ty   _ _ |- _ => tac H
    | H: is_unstamped_tm   _ _ |- _ => tac H
    | H: is_unstamped_dm   _ _ |- _ => tac H
    | H: is_unstamped_path _ _ |- _ => tac H
    | H: is_unstamped_vl   _ _ |- _ => tac H
  end.

Ltac with_is_stamped tac :=
  match goal with
    | H: is_stamped_ty _ _ _ |- _ => tac H
    | H: is_stamped_tm _ _ _ |- _ => tac H
    | H: is_stamped_vl _ _ _ |- _ => tac H
    | H: is_stamped_dm _ _ _ |- _ => tac H
    | H: is_stamped_path _ _ _ |- _ => tac H
  end.

(** * Stamping is monotone wrt stamp table extension. *)
Lemma not_stamped_dtysyn g n T:
  ¬ (is_stamped_dm n g (dtysyn T)).
Proof. by inversion 1. Qed.

Lemma is_stamped_dtysyn_mono g1 g2 n T:
  g1 ⊆ g2 →
  is_stamped_dm n g1 (dtysyn T) →
  is_stamped_dm n g2 (dtysyn T).
Proof. intros; exfalso. by eapply not_stamped_dtysyn. Qed.

Lemma is_stamped_mono_tm g1 g2 n e__s:
  g1 ⊆ g2 →
  is_stamped_tm n g1 e__s →
  is_stamped_tm n g2 e__s
with is_stamped_mono_vl g1 g2 n v__s:
  g1 ⊆ g2 →
  is_stamped_vl n g1 v__s →
  is_stamped_vl n g2 v__s
with is_stamped_mono_dm g1 g2 n d__s:
  g1 ⊆ g2 →
  is_stamped_dm n g1 d__s →
  is_stamped_dm n g2 d__s
with is_stamped_mono_path g1 g2 n p__s:
  g1 ⊆ g2 →
  is_stamped_path n g1 p__s →
  is_stamped_path n g2 p__s
with is_stamped_mono_ty g1 g2 n T__s:
  g1 ⊆ g2 →
  is_stamped_ty n g1 T__s →
  is_stamped_ty n g2 T__s.
Proof.
  all: intros Hleg Hst; dependent induction Hst.
  all: try solve [constructor;
    by [| exact: (is_stamped_mono_tm   _ _ _ _ Hleg)
        | exact: (is_stamped_mono_vl   _ _ _ _ Hleg)
        | exact: (is_stamped_mono_dm   _ _ _ _ Hleg)
        | exact: (is_stamped_mono_path _ _ _ _ Hleg)
        | exact: (is_stamped_mono_ty   _ _ _ _ Hleg)]].
  - constructor; elim: H => [|d ds' Hd H IH]; constructor;
     by [|exact: is_stamped_mono_dm].
  - move: ts' H H0 H1 => /= [l g0] [Hgs [-> Heq]] HstT Hstvs.
    eapply @trav_dtysem with (T' := T') (ts' := (length vs, g2)).
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
