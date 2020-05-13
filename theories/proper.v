(** * Utilities for setoids. *)
From stdpp Require Import tactics.

Set Suggest Proof Using.
Set Default Proof Using "Type".

(** Create an [f_equiv] database, inspired by stdpp's [f_equal] database. We
don't restrict it to [(_ ≡ _)], because [f_equiv] can apply [Proper]
instances to any relation. Use with lots of care. *)
Hint Extern 998 => f_equiv : f_equiv.

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
  (* TODO: Can we exclude that instance? *)
  | |- ?R (?f _) _ => simple apply (_ : Proper (_ ==> R) f)
  | |- ?R (?f _ _) _ => simple apply (_ : Proper (_ ==> _ ==> R) f)
  | |- ?R (?f _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> _ ==> _ ==> R) f)
  (* In case the function symbol differs, but the arguments are the same,
     maybe we have a pointwise_relation in our context. *)
  (* TODO: If only some of the arguments are the same, we could also
     query for "pointwise_relation"'s. But that leads to a combinatorial
     explosion about which arguments are and which are not the same. *)
  | H : pointwise_relation _ ?R ?f ?g |- ?R (?f ?x) (?g ?x) => simple apply H
  | H : pointwise_relation _ (pointwise_relation _ ?R) ?f ?g |- ?R (?f ?x ?y) (?g ?x ?y) => simple apply H
  end;
  try simple apply reflexivity.
Tactic Notation "f_equiv" "/=" := csimpl in *; f_equiv.

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
