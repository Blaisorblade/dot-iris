(** Define "stamping" in a purely syntactic
    way, without involving Iris. *)
From D.Dot Require Import syn traversals typing_aux_defs.
Export typing_aux_defs.

Set Implicit Arguments.

Import Trav1.

Implicit Types
         (T: ty) (v: vl) (e: tm) (p: path) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx) (n: nat).

(** Proposition [is_unstamped_path n OnlyVars p] implies that [p] is an
unstamped path in the strict sense defined in the paper; in particular, it's
also a stamped path.
Instead, [is_unstamped_path n AllowNonVars p] implies that [p] can be a
generic stable term. *)

Inductive AllowNonVars := OnlyVars | AlsoNonVars.

Definition is_unstamped_trav: Traversal (nat * AllowNonVars) :=
  {|
    upS := λ '(n, b), (n.+1, b);
    underPathElimS := λ '(n, _), (n, OnlyVars);
    varP := λ '(n, b) i, i < n;
    dtysynP := λ _ T, True;
    dtysemP := λ _ vs s T' ts', False;
    pathRootP := λ '(n, b) v, b = AlsoNonVars ∨
      (∃ x, v = vvar x) ∨ (∃ l, v = vlit l);
  |}.

Notation is_unstamped_tm   n b := (forall_traversal_tm is_unstamped_trav (n, b)).
Notation is_unstamped_vl   n b := (forall_traversal_vl is_unstamped_trav (n, b)).
Notation is_unstamped_dm   n b := (forall_traversal_dm is_unstamped_trav (n, b)).
Notation is_unstamped_path n b := (forall_traversal_path is_unstamped_trav (n, b)).
Notation is_unstamped_ty   n b := (forall_traversal_ty is_unstamped_trav (n, b)).

Notation is_unstamped_path' n := (is_unstamped_path n OnlyVars).
Notation is_unstamped_ty' n := (is_unstamped_ty n OnlyVars).

Ltac with_is_unstamped tac := with_forall_traversal is_unstamped_trav tac.
Ltac inverse_is_unstamped := inverse_forall_traversal is_unstamped_trav.

Lemma is_unstamped_path_root n p :
  is_unstamped_path n OnlyVars p →
  atomic_path_root p.
Proof. elim p => /= *; with_is_unstamped inverse; naive_solver. Qed.
