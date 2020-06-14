(** * "Prelude" with utilities available everywhere. *)
(* Base Coq settings (ssreflect and setup): *)
From Coq.Program Require Export Program.
From iris.algebra Require Export base.
From Autosubst Require Export Autosubst.
From D Require Export tactics.
From iris.program_logic Require Import language.

Set Suggest Proof Using.
Set Default Proof Using "Type".

(** Workaround https://github.com/coq/coq/issues/4230. Taken from Software Foundations. *)
Remove Hints Bool.trans_eq_bool : core.

(** https://github.com/math-comp/analysis/blob/bb4938c2dee89e91668f8d6a251e968d2f5a05ae/theories/posnum.v#L51-L52 *)
(** Enrico (Tassi?)'s trick for tc resolution in [have]. Doesn't conflict with infix [!!]. *)
Notation "!! x" := (ltac:(refine x)) (at level 100, only parsing).

Definition disable_tc_search {T : Type} (x : id T) : T := x.
Notation notc_hole := (disable_tc_search _).

(*
  If [prelude] and [Program] are imported after Iris modules,
  side effects from [iris.algebra.base] and [stdpp.base], including
  setting the obligation tactic, won't be re-run. So let's do it
  ourselves: *)
Obligation Tactic := idtac.

(** Autosubst extensions: notations *)
Notation shiftN n chi := chi.|[ren (+n)].
Notation shiftVN n v := v.[ren (+n)].

(* Define these afterwards, so they're used in preference when printing *)
Notation shift chi := (shiftN 1 chi).
Notation shiftV v := (shiftVN 1 v).

(** ** Miscellaneous utilities *)

(** Functorial action of the [A * _] functor. *)
Definition mapsnd {A} `(f : B → C) : A * B → A * C := λ '(a, b), (a, f b).

Definition stamp := positive.

(** Call [red] on each hypothesis at most once.
Not defined in [tactics.v] because it uses stdpp. *)
Ltac red_hyps_once :=
  repeat_on_hyps (fun H => try_once_tac H (red in H)); un_usedLemma.
