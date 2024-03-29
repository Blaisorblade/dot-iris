(** * Utilities for setoids.
The implementation of [f_equiv] is stdpp's implementation, plus a few extra
cases of higher arity.
*)
From stdpp Require Import tactics.
From iris.algebra Require Import ofe.

Set Suggest Proof Using.
Set Default Proof Using "Type".

(** Create an [f_equiv] database, inspired by stdpp's [f_equal] database. We
don't restrict it to [(_ ≡ _)], because [f_equiv] can apply [Proper]
instances to any relation. Use with lots of care. *)
#[global] Hint Extern 998 => f_equiv : f_equiv.

Notation Proper1 f := (Proper ((≡) ==> (≡)) f).

Notation Proper2 f := (Proper ((≡) ==> (≡) ==> (≡)) f).

Notation NonExpansive3 f := (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n) f).
Notation Proper3 f := (Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) f).

Notation NonExpansive4 f := (∀ n, Proper (dist n ==> dist n ==> dist n ==> dist n ==> dist n) f).
Notation Proper4 f := (Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) f).

Lemma ne_proper_3 {A B C D : ofe} (f : A → B → C → D) `{Hf : !NonExpansive3 f} :
  Proper3 f.
Proof. unfold Proper, respectful; setoid_rewrite equiv_dist. intros. exact: Hf. Qed.

Lemma ne_proper_4 {A B C D E : ofe} (f : A → B → C → D → E) `{Hf : !NonExpansive4 f} :
  Proper4 f.
Proof. unfold Proper, respectful; setoid_rewrite equiv_dist. intros. exact: Hf. Qed.

(* Generalize [contractive_ne] to arbitrary arities. *)
Lemma contractive_ne_R {A : ofe} {B R}
    (f : A -> B) {Hf : ∀ n, Proper (dist_later n ==> R n) f} :
  ∀ n, Proper (dist n ==> R n) f.
Proof. intros n a1 a2 Ha. eapply Hf, dist_dist_later, Ha. Qed.

(* Override stdpp's [f_equiv], raising maximum arity from 5 up to 7. *)
Ltac f_equiv ::=
  match goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  (* We support matches on both sides, *if* they concern the same variable, or
     variables in some relation. *)
  | |- ?R (match ?x with _ => _ end) (match ?x with _ => _ end) =>
    destruct x
  | H : ?R ?x ?y |- ?R2 (match ?x with _ => _ end) (match ?y with _ => _ end) =>
     destruct H
  (* First assume that the arguments need the same relation as the result *)
  | |- ?R (?f _) _ => simple apply (_ : Proper (R ==> R) f)
  | |- ?R (?f _ _) _ => simple apply (_ : Proper (R ==> R ==> R) f)
  | |- ?R (?f _ _ _) _ => simple apply (_ : Proper (R ==> R ==> R ==> R) f)
  | |- ?R (?f _ _ _ _) _ => simple apply (_ : Proper (R ==> R ==> R ==> R ==> R) f)
  | |- ?R (?f _ _ _ _ _) _ => simple apply (_ : Proper (R ==> R ==> R ==> R ==> R ==> R) f)
  | |- ?R (?f _ _ _ _ _ _) _ => simple apply (_ : Proper (R ==> R ==> R ==> R ==> R ==> R ==> R) f)
  (* For the case in which R is polymorphic, or an operational type class,
  like equiv. *)
  | |- (?R _) (?f _) _ => simple apply (_ : Proper (R _ ==> _) f)
  | |- (?R _ _) (?f _) _ => simple apply (_ : Proper (R _ _ ==> _) f)
  | |- (?R _ _ _) (?f _) _ => simple apply (_ : Proper (R _ _ _ ==> _) f)
  | |- (?R _) (?f _ _) _ => simple apply (_ : Proper (R _ ==> R _ ==> _) f)
  | |- (?R _ _) (?f _ _) _ => simple apply (_ : Proper (R _ _ ==> R _ _ ==> _) f)
  | |- (?R _ _ _) (?f _ _) _ => simple apply (_ : Proper (R _ _ _ ==> R _ _ _ ==> _) f)
  | |- (?R _) (?f _ _ _) _ => simple apply (_ : Proper (R _ ==> R _ ==> R _ ==> _) f)
  | |- (?R _ _) (?f _ _ _) _ => simple apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> _) f)
  | |- (?R _ _ _) (?f _ _ _) _ => simple apply (_ : Proper (R _ _ _ ==> R _ _ _ R _ _ _ ==> _) f)
  | |- (?R _) (?f _ _ _ _) _ => simple apply (_ : Proper (R _ ==> R _ ==> R _ ==> R _ ==> _) f)
  | |- (?R _ _) (?f _ _ _ _) _ => simple apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> _) f)
  | |- (?R _ _ _) (?f _ _ _ _) _ => simple apply (_ : Proper (R _ _ _ ==> R _ _ _ R _ _ _ ==> R _ _ _ ==> _) f)
  | |- (?R _) (?f _ _ _ _ _) _ => simple apply
      (_ : Proper (R _ ==> R _ ==> R _ ==> R _ ==> R _ ==> _) f)
  | |- (?R _ _) (?f _ _ _ _ _) _ => simple apply
      (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> _) f)
  | |- (?R _ _ _) (?f _ _ _ _ _) _ => simple apply
      (_ : Proper (R _ _ _ ==> R _ _ _ R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> _) f)
  | |- (?R _) (?f _ _ _ _ _ _) _ => simple apply
      (_ : Proper (R _ ==> R _ ==> R _ ==> R _ ==> R _ ==> R _ ==> _) f)
  | |- (?R _ _) (?f _ _ _ _ _ _) _ => simple apply
      (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> _) f)
  | |- (?R _ _ _) (?f _ _ _ _ _ _) _ => simple apply
      (_ : Proper (R _ _ _ ==> R _ _ _ R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> _) f)
  (* Next, try to infer the relation. Unfortunately, very often, it will turn
     the goal into a Leibniz equality so we get stuck. *)
  | |- ?R (?f _) _ => simple apply (_ : Proper (_ ==> R) f)
  | |- ?R (?f _ _) _ => simple apply (_ : Proper (_ ==> _ ==> R) f)
  | |- ?R (?f _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> _ ==> _ ==> R) f)
  (* In case the function symbol differs, but the arguments are the same,
     maybe we have a pointwise_relation in our context. *)
  | H : pointwise_relation _ ?R ?f ?g |- ?R (?f ?x) (?g ?x) => simple apply H
  | H : pointwise_relation _ (pointwise_relation _ ?R) ?f ?g |- ?R (?f ?x ?y) (?g ?x ?y) => simple apply H
  end;
  try simple apply reflexivity.

Ltac no_eq_f_equiv := try f_equiv;
  match goal with
  | |- eq _ _ => fail 1
  | |- _ => idtac
  end.

(* These helpers allow "flipping" [Proper] instances, as needed when [f] is
an asymmetric relation. *)
(* We don't make these helpers into instances, as they can cause loops in
typeclass search. *)
Section flip_proper.
Context `{R1 : relation A} `{R2 : relation A2} `{R3 : relation A3}
  `{R4 : relation A4} `{R5 : relation A5} `{R6 : relation A6} `{R7 : relation A7}.

Lemma flip_proper_2 `(!Proper (R1 ==> R2) f) :
  Proper (flip R1 ==> flip R2) f.
Proof. solve_proper. Qed.

Lemma flip_proper_3 `(!Proper (R1 ==> R2 ==> R3) f) :
  Proper (flip R1 ==> flip R2 ==> flip R3) f.
Proof. solve_proper. Qed.

Lemma flip_proper_4 `(!Proper (R1 ==> R2 ==> R3 ==> R4) f) :
  Proper (flip R1 ==> flip R2 ==> flip R3 ==> flip R4) f.
Proof. solve_proper. Qed.

Lemma flip_proper_5 `(!Proper (R1 ==> R2 ==> R3 ==> R4 ==> R5) f) :
  Proper (flip R1 ==> flip R2 ==> flip R3 ==> flip R4 ==> flip R5) f.
Proof. solve_proper. Qed.

Lemma flip_proper_6
  `(!Proper (R1 ==> R2 ==> R3 ==> R4 ==> R5 ==> R6) f) :
  Proper (flip R1 ==> flip R2 ==> flip R3 ==> flip R4 ==> flip R5 ==>
    flip R6) f.
Proof. solve_proper. Qed.

Lemma flip_proper_7
  `(!Proper (R1 ==> R2 ==> R3 ==> R4 ==> R5 ==> R6 ==> R7) f) :
  Proper (flip R1 ==> flip R2 ==> flip R3 ==> flip R4 ==> flip R5 ==>
    flip R6 ==> flip R7) f.
Proof. solve_proper. Qed.
End flip_proper.

(** Potentially useful to speed up proofs. *)
Lemma eq_equiv `{Equiv A} `{!Equivalence (≡@{A})} (x y : A) : x = y → x ≡ y.
Proof. by intros ->. Qed.
