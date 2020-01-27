(**
Infrastructure for examples of DOT programs.
*)
From stdpp Require Import strings.
From D Require Import tactics.
From D.Dot Require Import syn syn.path_repl lr_syn_aux.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

(****************)
(** NOTATIONS  **)
(****************)

Coercion tv : vl_ >-> tm.
Coercion vlit : base_lit >-> vl_.
Coercion lnat : nat >-> base_lit.
Coercion lbool : bool >-> base_lit.

Module Import DBNotation.

(* Definition vnat' n := vnat n.
Coercion vnat' : nat >-> vl_. *)
(* XXX rename *)
Bind Scope expr_scope with tm.
Delimit Scope expr_scope with E.

Notation "()" := (vobj []) : expr_scope.
(* Notation "- e" := (tun MinusUnOp e%E) : expr_scope. *)

Notation "e1 + e2" := (tbin bplus e1%E e2%E) : expr_scope.
Notation "e1 - e2" := (tbin bminus e1%E e2%E) : expr_scope.
Notation "e1 * e2" := (tbin btimes e1%E e2%E) : expr_scope.
Notation "e1 `div` e2" := (tbin bdiv e1%E e2%E) : expr_scope.
(* Notation "e1 `rem` e2" := (tbin RemOp e1%E e2%E) : expr_scope. *)

Notation "e1 ≤ e2" := (tbin ble e1%E e2%E) : expr_scope.
Notation "e1 < e2" := (tbin blt e1%E e2%E) : expr_scope.
Notation "e1 = e2" := (tbin beq e1%E e2%E) : expr_scope.
Notation "e1 ≠ e2" := (tun unot (tbin beq e1%E e2%E)) : expr_scope.

Notation "~ e" := (tun unot e%E) (at level 75, right associativity) : expr_scope.

Notation "e1 > e2" := (e2%E < e1%E)%E : expr_scope.
Notation "e1 ≥ e2" := (e2%E ≤ e1%E)%E : expr_scope.

(** First, let's maybe start defining some nicer notation. I have little clue what I'm doing tho.
    *)

(* Beware that "Bind Scope" just presets the scope of arguments for *new* definitions. *)

(** Notation for object values. *)

Open Scope dms_scope.
Notation " {@ } " := (@nil (string * dm)) (format "{@ }") : dms_scope.
Notation " {@ x } " := ( x :: {@} ) (format "{@  x  }"): dms_scope.
Notation " {@ x ; y ; .. ; z } " :=
  (cons x (cons y .. (cons z nil) ..))
  (* (format "{@  x ;  y ;  .. ;  z  }") *)
  (format "'[v' {@  '[' x ']' ;  '/' y ;  '/' .. ;  '/' z } ']'")
  : dms_scope.

Close Scope dms_scope.
Arguments vobj _%dms_scope.

Notation "'ν' ds " := (vobj ds) (at level 60, ds at next level).
Notation "'val' l = v" := (l, dpt v) (at level 60, l at level 50).
Notation "'type' l = T  " := (l, dtysyn T) (at level 60, l at level 50).

(** Notation for object types. *)
Open Scope ty_scope.
Notation "⊤" := TTop : ty_scope.
Notation "⊥" := TBot : ty_scope.
(* Notation " {@ } " := TTop (format "{@ }") : ty_scope. *)
Notation " {@ T1 } " := ( TAnd T1 ⊤ ) (format "{@  T1  }"): ty_scope.
Notation " {@ T1 ; T2 ; .. ; Tn } " :=
  (TAnd T1 (TAnd T2 .. (TAnd Tn ⊤)..))
  (* (format "'[v' {@  '[' T1 ']'  ;   T2  ;   ..  ;   Tn } ']'") : ty_scope. *)
  (format "'[v' {@  '[' T1 ']'  ;  '/' T2  ;  '/' ..  ;  '/' Tn } ']'") : ty_scope.
(* Notation " {@ T1 ; .. ; T2 ; Tn } " := (TAnd (TAnd .. (TAnd {@} T1) .. T2) Tn) *)
(*                                          (format "{@  T1  ;  ..  ;  T2  ;  Tn  }"): ty_scope. *)
Close Scope ty_scope.

Notation "'𝐍'" := TNat : ty_scope.

Notation "▶:" := TLater : ty_scope.
(* Level taken from Iris. *)
Notation "▶: T" := (TLater T) (at level 49, right associativity) : ty_scope.

Notation "'∀:' T , U" := (TAll T U) (at level 48, T at level 98, U at level 98).
(* Do not use, too many conflicts. *)
Notation "'∀' T ',' U" := (TAll T U) (at level 49, only printing) : ty_scope.

Notation "'μ' Ts " := (TMu Ts) (at level 50, Ts at next level).
Notation "'type' l >: L <: U" := (TTMem l L U) (at level 60, l at level 50, L, U at level 70) : ty_scope.
Notation "'val' l : T" :=
  (TVMem l T)
  (at level 60, l, T at level 50, format "'[' 'val'  l  :  T  ']' '/'") : ty_scope.

Notation "S →: T" := (TAll S%ty (shift T%ty)) (at level 49, T at level 98, right associativity) : ty_scope.

(* Notation "v @ l1 @ .. @ l2 ; l" := (TSel (pself .. (pself (pv v) l1) .. l2) l) *)
(*                                      (format "v  @  l1  @  ..  @  l2  ;  l", at level 69, l1, l2 at level 60). *)

Notation "p @; l" := (TSel p l) (at level 48).
Notation "v @ l1 @ .. @ l2" := (pself .. (pself v l1) .. l2)
                                     (format "v  @  l1  @  ..  @  l2", at level 48, l1, l2 at level 40).
Notation "a @: b" := (tproj a b) (at level 59, b at next level).

Infix "$:" := tapp (at level 68, left associativity).

Notation tparam A := (type A >: ⊥ <: ⊤)%ty.
Definition typeEq l T : ty := type l >: T <: T.

Notation x0 := (var_vl 0).
Notation x1 := (var_vl 1).
Notation x2 := (var_vl 2).
Notation x3 := (var_vl 3).
Notation x4 := (var_vl 4).
Notation x5 := (var_vl 5).

Notation p0 := (pv x0).
Notation p1 := (pv x1).
Notation p2 := (pv x2).
Notation p3 := (pv x3).
Notation p4 := (pv x4).
Notation p5 := (pv x5).

Notation TUnit := (⊤%ty : ty).
Notation tUnit := (tv (vnat 0) : tm).

End DBNotation.

(****************)
(** AUTOMATION **)
(****************)

(* Deterministic crush. *)
Ltac dcrush := repeat constructor.
Ltac by_dcrush := by dcrush.

From D.Dot Require Import traversals.

Import Trav1.

Ltac stconstructor := match goal with
  | |- forall_traversal_tm   _ _ _ => constructor
  | |- forall_traversal_vl   _ _ _ => constructor
  | |- forall_traversal_dm   _ _ _ => constructor
  | |- forall_traversal_path _ _ _ => constructor
  | |- forall_traversal_ty   _ _ _ => constructor
  | |- Forall _ _ => constructor
  end.
Ltac stcrush := try ((progress repeat stconstructor); eauto).

Hint Extern 10 (_ ≤ _) => lia : core.

Hint Extern 0 (dms_hasnt _ _) => done : core.

Hint Resolve Nat.lt_0_succ : core.

Definition vabs' x := tv (vabs x).
Definition lett t u := tapp (vabs' u) t.
