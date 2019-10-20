(**
Infrastructure for examples of DOT programs.
*)
From stdpp Require Import strings.
From D Require Import tactics.
From D.Dot Require Import syn.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

(****************)
(** NOTATIONS  **)
(****************)

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
Notation "'val' l = v" := (l, dvl v) (at level 60, l at level 50).
Notation "'type' l = ( σ ; s )" := (l, dtysem σ s) (at level 60, l at level 50).

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

Check {@ TNat ; TNat ; TNat } % ty.

Notation "'ℕ'" := TNat  (only parsing) : ty_scope.
Notation "'𝐍'" := TNat : ty_scope.

Notation "'▶'" := TLater : ty_scope.
(* Level taken from Iris. *)
Notation "'▶' T" := (TLater T) (at level 20, right associativity) : ty_scope.

(* Do not use, too many conflicts. *)
Notation "'∀' T ',' U" := (TAll T U) (at level 49, only printing) : ty_scope.
(* Notation "'∀' '(' T ')' U" := (TAll T U) (at level 60). *)
(* Notation "'∀' '(' T ')' U" := (TAll T U)
  (at level 30, format "'∀'  '(' T ')'   U") : ty_scope. *)

Notation "'μ' Ts " := (TMu Ts) (at level 50, Ts at next level).
Notation "'type' l >: L <: U" := (TTMem l L U) (at level 60, l at level 50, L, U at level 70) : ty_scope.
Notation "'val' l : T" :=
  (TVMem l T)
  (at level 60, l, T at level 50, format "'[' 'val'  l  :  T  ']' '/'") : ty_scope.

Definition typeEq l T := (type l >: T <: T) % ty.

Notation σ1 := ([] : vls).
Notation s1 := (1 % positive).

Notation σ2 := ([] : vls).
Notation s2 := (2 % positive).

Check ν {@ val "a" = vnat 0 }.

Check ν {@ type "A" = (σ1 ; s1) }.
Check ν {@ val "a" = vnat 0; type "A" = (σ1 ; s1) }.
Check μ {@ type "A" >: TNat <: TTop }.
Check μ {@ val "a" : TNat }.
Check μ {@ type "A" >: TNat <: TTop ; val "a" : TNat ; val "b" : TNat }.

Check vobj {@}.
Check ν {@ }.
Check ν {@ val "a" = vnat 0 }.
Check ν {@ val "a" = vnat 0 ; val "b" = vnat 1 }.
Check ν {@ val "a" = vnat 0 ; type "A" = (σ1 ; s1) }.

(* Notation "v @ l1 @ .. @ l2 ; l" := (TSel (pself .. (pself (pv v) l1) .. l2) l) *)
(*                                      (format "v  @  l1  @  ..  @  l2  ;  l", at level 69, l1, l2 at level 60). *)
(* Check (TSel (pself (pself p0 1) 2) 3). *)
(* Check (x0 @ 1 @ 2 ; 3). *)

Notation "v @ l1 @ .. @ l2" := (pself .. (pself (pv v) l1) .. l2)
                                     (format "v  @  l1  @  ..  @  l2", at level 69, l1, l2 at level 60).

Notation "p @; l" := (TSel p l) (at level 69).
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

Check (p0 @; "A").
Check (pself (pself p0 "A") "B" @; "C").
Check (x0 @ "A").
Check (x0 @ "A" @ "B" @; "C").

Notation TUnit := (⊤ % ty : ty).
Notation tUnit := (tv (vnat 0) : tm).

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
