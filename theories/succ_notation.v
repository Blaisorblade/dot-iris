(** ssreflect postfix notation for the successor and predecessor functions.
SSreflect uses "pred" for the generic predicate type, and S as a local bound
variable.*)
Notation succn := Datatypes.S.
Notation predn := Peano.pred.

Notation "n .+1" := (succn n) (at level 2, left associativity,
  format "n .+1") : nat_scope.
Notation "n .+2" := n.+1.+1 (at level 2, left associativity,
  format "n .+2") : nat_scope.
Notation "n .+3" := n.+2.+1 (at level 2, left associativity,
  format "n .+3") : nat_scope.
Notation "n .+4" := n.+2.+2 (at level 2, left associativity,
  format "n .+4") : nat_scope.

Notation "n .-1" := (predn n) (at level 2, left associativity,
  format "n .-1") : nat_scope.
Notation "n .-2" := n.-1.-1 (at level 2, left associativity,
  format "n .-2") : nat_scope.
