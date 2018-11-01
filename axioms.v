From mathcomp Require Import ssreflect.

(** ** Propositional extensionality *)

Axiom propositional_extensionality :
  forall (P Q : Prop), (P <-> Q) -> P = Q.

Lemma pext {P Q : Prop} : (P -> Q) -> (Q -> P) -> P = Q.
Proof. move=> h1 h2. exact: propositional_extensionality. Qed.

(** ** Functional extensionality *)

Axiom functional_extensionality : forall (A : Type) (B : A -> Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.

Definition fext {A : Type} {B : A -> Type} (f g : forall x, B x) :
    (forall x, f x = g x) -> f = g := functional_extensionality A B f g.

(** ** Extensionality for products *)

Lemma xi_ext {A} {B C : A -> Type} (p : forall x : A, B x = C x) :
  (forall x, B x) = (forall x, C x).
Proof. have: B = C by exact: fext. by move->. Qed.

Lemma xi_extP {A} {B C : A -> Prop} (p : forall x : A, B x = C x) :
  (forall x, B x) = (forall x, C x).
Proof. have: B = C by exact: fext. by move->. Qed.

Lemma xi_extS {A} {B C : A -> Set} (p : forall x : A, B x = C x) :
  (forall x, B x) = (forall x, C x).
Proof. have: B = C by exact: fext. by move->. Qed.

(** ** Extensionality Tactic *)

Require Import Program.Tactics.

Tactic Notation "nointr" tactic(t) := 
  let m := fresh "marker" in 
  pose (m := tt);
  t; revert_until m; clear m.

Ltac fext := nointr repeat (
  match goal with
    [ |- ?x = ?y ] =>
    (apply: fext ||
     apply: xi_extP ||
     apply: xi_extS ||
     apply: xi_ext); intro
  end).

(** ** Typeclass instance for Funext *)

Require Import Autosubst2.

Instance: Funext.
Proof. move=> A B f g h. fext. exact: h. Qed.
