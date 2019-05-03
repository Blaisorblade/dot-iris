From Autosubst Require Import Autosubst.

Tactic Notation "locAsimpl'" uconstr(e1) :=
  remember (e1) as __e' eqn:__Heqe';
  progress asimpl in __Heqe'; subst __e'.

(* This retries multiple times; must lock patterns and ignore them *)
Ltac locAsimpl :=
  repeat match goal with
  | |- context [?a.[?s]] => locAsimpl' a.[s]
  | |- context [?a.|[?s]] => locAsimpl' (a.|[s])
  end.
