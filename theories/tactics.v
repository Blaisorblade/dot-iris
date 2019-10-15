(* Remove Hints Bool.trans_eq_bool. *)

Ltac inverse H := (inversion H; subst).
Ltac int := intuition trivial.

Ltac ev := repeat match goal with
                    | H: exists _, _ |- _ => destruct H
                    | H: _ /\  _ |- _ => destruct H
                    | H : exists2 _, _ & _ |- _ => destruct H
                    | H : { _ | _ } |- _ => destruct H
                    | H : { _ | _ & _ } |- _ => destruct H
                    (* | H : { _ & _ } |- _ => destruct H *)
                    | H : { _ : _ & _ & _ } |- _ => destruct H
                    | p : _ * _ |- _ => destruct p
                  end.

(** Tactic to split a lemma proven by mutual induction into its pieces. *)
Ltac unmut_lemma H := destruct H; ev; eauto.

Hint Constructors option.
Hint Constructors list.

(** Support writing external hints for lemmas that must not be applied twice for a goal. *)
(* The usedLemma and un_usedLemma marker is taken from Crush.v (where they were called done and un_done). *)

(** Devious marker predicate to use for encoding state within proof goals *)
Definition usedLemma {T : Type} (x : T) := True.

(** After a round of application with the above, we will have a lot of junk [usedLemma] markers to clean up; hence this tactic. *)
Ltac un_usedLemma :=
  repeat match goal with
           | [ H : usedLemma _ |- _ ] => clear H
         end.
Ltac markUsed H := assert (usedLemma H) by constructor.

Ltac try_once lm :=
    match goal with
    | H : usedLemma lm |- _ => fail 1
    | _ => markUsed lm; eapply lm
    end.

Tactic Notation "try_once_tac" constr(T) tactic(tac) :=
  match goal with
  | H : usedLemma T |- _ => fail 1
  | _ => markUsed T; tac
  end.

(** Perform [tac], then fail if more than
    one goal is created. *)
Tactic Notation "nosplit" tactic3(tac) := tac; let n := numgoals in guard n = 1.

(* Example. *)
(* Definition injectHyps_marker := 0. *)
(* Hint Extern 5 => try_once_tac injectHyps_marker injectHyps. *)
