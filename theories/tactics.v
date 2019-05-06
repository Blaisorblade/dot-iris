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

(* Avoid case distinctions when we know the right case from the hypotheses.
   Otherwise, we end up with branches where the context says that ?x = A and ?x
   = B, with A and B incompatible, and must use discriminate to remove those
   branches. *)
Ltac better_case_match :=
  match goal with
  | H : context [ match ?x with _ => _ end ] , H1 : _ = ?x |- _ =>
    rewrite <- H1 in H
  | H : context [ match ?x with _ => _ end ] , H1 : ?x _ |- _ =>
    rewrite H1 in H
  | H : context [ match ?x with _ => _ end ] |- _ =>
    destruct x eqn:?

  | H1 : _ = ?x |- context [ match ?x with _ => _ end ] =>
    rewrite <- H1
  | H1 : ?x = _ |- context [ match ?x with _ => _ end ] =>
    rewrite H1
  | |- context [ match ?x with _ => _ end ] =>
    destruct x eqn:?
  end.

(* From Chlipala's tactics. *)
Ltac cinject H := injection H; clear H; intros; subst.

(* Apply automatically injection on hypotheses of form ?c args1 = ?c args2; if c
   is a constructor this will produce equalities args1_i = args2_i for all i.
   Since this tactic uses injection, it is more reliable than attempts based on
   inversion. *)
Ltac injectHyp :=
  match goal with
  | H : ?c _ _ _ _ _ _ = ?c _ _ _ _ _ _ |- _ => cinject H
  | H : ?c _ _ _ _ _ = ?c _ _ _ _ _ |- _ => cinject H
  | H : ?c _ _ _ _ = ?c _ _ _ _ |- _ => cinject H
  | H : ?c _ _ _ = ?c _ _ _ |- _ => cinject H
  | H : ?c _ _ = ?c _ _ |- _ => cinject H
  | H : ?c _ = ?c _ |- _ => cinject H
  | H : ?c = ?c |- _ => clear H
  end.
Ltac injectHyps := repeat injectHyp.

Ltac optFuncs_det :=
  match goal with
  | H1 : ?t = _, H2 : ?t = _ |- _ =>
    let H := fresh "H" in
    rewrite H2 in H1; injectHyps
  end.

(* To use with repeat fequalSafe in automation.
   Unlike f_equal, won't try to prove a = b = c + d by a = c and b = d --- such
   equalities are omega's job. *)
Ltac fequalSafe :=
  match goal with
  | [ |- Some _ = Some _ ] => f_equal
  | [ |- (_, _) = (_, _) ] => f_equal
  end.

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

Ltac better_case_match_ex := try better_case_match; injectHyps; try discriminate.

(* Example. *)
(* Definition injectHyps_marker := 0. *)
(* Hint Extern 5 => try_once_tac injectHyps_marker injectHyps. *)
