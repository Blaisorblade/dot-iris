(** * Infrastructure for examples of DOT programs. *)
From stdpp Require Import strings.
From D Require Import tactics.
From D.Dot Require Import syn path_repl lr_syn_aux.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

(*******************)
(** * NOTATIONS  **)
(*******************)

Coercion tv : vl_ >-> tm.
Coercion pv : vl_ >-> path.
Coercion vlit : base_lit >-> vl_.
Coercion lint : Z >-> base_lit.
Coercion lbool : bool >-> base_lit.

Identity Coercion vl2vl_ : vl >-> vl_.
Coercion vl_2vl := id : vl_ -> vl.

Module Import DBNotation.

Bind Scope expr_scope with tm.
Delimit Scope expr_scope with E.

Notation "()" := (vobj []) : expr_scope.

Notation "e1 + e2" := (tbin bplus e1%E e2%E) : expr_scope.
Notation "e1 - e2" := (tbin bminus e1%E e2%E) : expr_scope.
Notation "e1 * e2" := (tbin btimes e1%E e2%E) : expr_scope.
Notation "e1 `div` e2" := (tbin bdiv e1%E e2%E) : expr_scope.

Notation "e1 ≤ e2" := (tbin ble e1%E e2%E) : expr_scope.
Notation "e1 < e2" := (tbin blt e1%E e2%E) : expr_scope.
Notation "e1 = e2" := (tbin beq e1%E e2%E) : expr_scope.
Notation "e1 ≠ e2" := (tun unot (tbin beq e1%E e2%E)) : expr_scope.

Notation "~ e" := (tun unot e%E) (at level 75, right associativity) : expr_scope.

Notation "e1 > e2" := (e2%E < e1%E)%E : expr_scope.
Notation "e1 ≥ e2" := (e2%E ≤ e1%E)%E : expr_scope.

(** ** Notation for object values. *)

Open Scope dms_scope.
Notation "{@ }" := (@nil (string * dm)) (format "{@ }") : dms_scope.
Notation "{@ x }" := ( x :: {@} ) (format "{@  x  }"): dms_scope.
Notation "{@ x ; y ; .. ; z }" :=
  (cons x (cons y .. (cons z nil) ..))
  (format "'[v' {@  '[' x ']' ;  '/' y ;  '/' .. ;  '/' z } ']'")
  : dms_scope.

Close Scope dms_scope.
Arguments vobj _%dms_scope.

Notation "'ν' ds" := (vobj ds) (at level 60, ds at next level).
Notation "'val' l = v" := (l, dpt v) (at level 60, l at level 50).
Notation "'type' l = T" := (l, dtysyn T) (at level 60, l at level 50).

(** Notation for object types. *)
#[global] Instance: Top ty := TTop.
#[global] Instance: Bottom ty := TBot.

Open Scope ty_scope.
Notation "{@ T1 }" := ( TAnd T1 ⊤ ) (format "{@  T1  }"): ty_scope.
Notation "{@ T1 ; T2 ; .. ; Tn }" :=
  (TAnd T1 (TAnd T2 .. (TAnd Tn ⊤)..))
  (format "'[v' {@  '[' T1 ']'  ;  '/' T2  ;  '/' ..  ;  '/' Tn } ']'") : ty_scope.
Close Scope ty_scope.

Notation "'𝐙'" := TInt : ty_scope.

Notation "▶:" := TLater : ty_scope.
(* Level taken from Iris. *)
Notation "▶: T" := (TLater T) (at level 49, right associativity) : ty_scope.

Notation "'∀:' T , U" := (TAll T U) (at level 48, T at level 98, U at level 98).

Notation "'μ' Ts" := (TMu Ts) (at level 50, Ts at next level).
Notation "'type' l >: L <: U" := (TTMemL l L U) (at level 60, l at level 50, L, U at level 70) : ty_scope.
Notation "'val' l : T" :=
  (TVMem l T)
  (at level 60, l, T at level 50, format "'[' 'val'  l  :  T  ']' '/'") : ty_scope.

Notation "S →: T" := (TAll S%ty (shift T%ty)) (at level 49, T at level 98, right associativity) : ty_scope.

Notation "p @; l" := (TSel p l) (at level 48).
Notation "v @ l1 @ .. @ l2" := (pself .. (pself v l1) .. l2)
                                     (format "v  @  l1  @  ..  @  l2", at level 48, l1, l2 at level 40).
Notation "a @: b" := (tproj a b) (at level 59, b at next level).

Infix "$:" := tapp (at level 68, left associativity).

Notation tparam A := (type A >: ⊥ <: ⊤)%ty.
Definition typeEq l T : ty := type l >: T <: T.

Notation x0 := (vvar 0).
Notation x1 := (vvar 1).
Notation x2 := (vvar 2).
Notation x3 := (vvar 3).
Notation x4 := (vvar 4).
Notation x5 := (vvar 5).

Notation TUnit := (⊤%ty : ty).
Notation tUnit := (tv (vint 0) : tm).

End DBNotation.

(******************)
(** * AUTOMATION **)
(******************)

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

Definition lett t u := tapp (vabs u) t.

(** Simplify substitution operations on concrete terms. *)
Ltac simplSubst := rewrite /= /up/= /ids/ids_vl/=.
