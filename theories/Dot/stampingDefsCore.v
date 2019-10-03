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
Notation valid_stamp g vs s := (∃ T', g !! s = Some T' ∧ nclosed T' (length vs)).

Definition is_unstamped_trav: Traversal unit :=
  {|
    upS := id;
    varP := λ _ n, True;
    dtysynP := λ _ T, True;
    dtysemP := λ _ vs s, False;
    tselP := λ s p, ∃ x, path_root p = var_vl x;
  |}.

Definition is_stamped_trav: Traversal (nat * stys) :=
  {|
    upS := λ '(n, g), (S n, g);
    varP := λ '(n, g) i, i < n;
    dtysynP := λ ts T, False;
    dtysemP := λ '(n, g) vs s, valid_stamp g vs s;
    tselP := λ ts p, True;
  |}.

Notation is_unstamped_tm := (forall_traversal_tm is_unstamped_trav ()).
Notation is_unstamped_vl := (forall_traversal_vl is_unstamped_trav ()).
Notation is_unstamped_dm := (forall_traversal_dm is_unstamped_trav ()).
Notation is_unstamped_path := (forall_traversal_path is_unstamped_trav ()).
Notation is_unstamped_ty := (forall_traversal_ty is_unstamped_trav ()).

Notation is_stamped_tm n g := (forall_traversal_tm is_stamped_trav (n, g)).
Notation is_stamped_vl n g := (forall_traversal_vl is_stamped_trav (n, g)).
Notation is_stamped_dm n g := (forall_traversal_dm is_stamped_trav (n, g)).
Notation is_stamped_path n g := (forall_traversal_path is_stamped_trav (n, g)).
Notation is_stamped_ty n g := (forall_traversal_ty is_stamped_trav (n, g)).

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
  ∃ T', g !! s = Some T' ∧ T'.|[to_subst σ] = T ∧ nclosed_σ σ n ∧ nclosed T' (length σ).
Notation "T ~[ n  ] gsσ" := (extraction n T gsσ) (at level 70).
