(* A HOAS frontend for de Bruijn terms. *)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra.

(* Inspired by the "Unembedding DSLs" paper, but specialized.
I suspect equivalent to
https://web.archive.org/web/20130412082828/http://www.e-pig.org/epilogue/?p=773
but readable. *)
(* TODO? Check out:
  http://www.cs.uu.nl/research/techreps/repo/CS-2012/2012-009.pdf
*)
(* Binders in our language: λ, ν, ∀, μ. *)
Definition hterm sort := var → sort.

Notation htm   := (hterm tm).
Notation hvl   := (hterm vl).
Notation hdm   := (hterm dm).
Notation hpath := (hterm path).
Notation hty   := (hterm ty).

Notation hdms  := (list (label * hterm dm)).

Bind Scope ty_scope with hty.
Bind Scope dms_scope with hdms.

Instance ids_hvl : Ids hvl := λ x, (* [x]: input to the substitution. *)
  (* Resulting [vl]. *)
  λ i, ids (x + i).

(** Lift to the *)
Module Import hterm_lifting.
Section lifting.
Context {s1 s2 s3 s4: Type}.
Definition hclose : hterm s1 → s1 := (.$ 0).

Definition pureS : s1 → hterm s1 := const.
Definition apS : hterm (s1 → s2) → hterm s1 → hterm s2 := λ f a i, f i (a i).
Definition bindS : hterm s1 → (s1 → hterm s2) → hterm s2 := λ m f i, f (m i) i.

Definition liftA0 (con : s1) : hterm s1 := pureS con.
Definition liftA1 (con : s1 → s2) : hterm s1 → hterm s2 := λ a1 i,
  con (a1 i).

Definition liftA2 (con : s1 → s2 → s3) :
  hterm s1 → hterm s2 → hterm s3 := λ a1 a2 i,
  con (a1 i) (a2 i).
Definition liftA3 (con : s1 → s2 → s3 → s4) :
  hterm s1 → hterm s2 → hterm s3 → hterm s4 := λ a1 a2 a3 i,
  con (a1 i) (a2 i) (a3 i).

Definition liftBind (con : s1 → s2) (f : hterm vl → hterm s1) : hterm s2 := λ i,
  let i' := S i in
  let v := ren (λ j, j - i') in
  con (f v i').

Definition liftList : list (label * hterm dm) → hterm (list (label * dm)) := λ ds i, map (mapsnd (.$ i)) ds.

(* Ever used? Likely not. *)
(* Definition hshift : hterm s1 → hterm s1 := λ t i, t (S i). *)
End lifting.
End hterm_lifting.

Module Type liftSyn.
  Parameter htv : hvl → hterm tm.
  Parameter htapp : hterm tm → hterm tm → hterm tm.
  Parameter htproj : hterm tm → label → nat → tm.
  Parameter htskip : hterm tm → hterm tm.

  Parameter hvar_vl : var → hterm vl.
  Parameter hvnat : nat → hterm vl.
  Parameter hvabs : (hterm vl → hterm tm) → hterm vl.
  Parameter hvobj : (hterm vl → hdms) → hterm vl.

  Parameter hdtysyn : hterm ty → hterm dm.
  Parameter hdvl : hterm vl → hterm dm.

  Parameter hpv : hterm vl → hterm path.
  Parameter hpself : hterm path → label → nat → path.

  Parameter hTTop : hterm ty.
  Parameter hTBot : hterm ty.
  Parameter hTAnd : hterm ty → hterm ty → hterm ty.
  Parameter hTOr : hterm ty → hterm ty → hterm ty.
  Parameter hTLater : hterm ty → hterm ty.
  Parameter hTAll : hterm ty → (hterm vl → hterm ty) → hterm ty.
  Parameter hTMu : (hterm vl → hterm ty) → hterm ty.
  Parameter hTVMem : label → hterm ty → hterm ty.
  Parameter hTTMem : label → hterm ty → hterm ty → hterm ty.
  Parameter hTSel : hterm path → label → nat → ty.
  Parameter hTNat : hterm ty.
  Parameter hTSing : hterm path → hterm ty.
End liftSyn.

Module Import syn <: liftSyn.

Definition htv := liftA1 tv.
Definition htapp := liftA2 tapp.
Definition htproj t l := Eval cbv in liftA2 tproj t (pureS l).
Definition htskip := liftA1 tskip.


Definition hvar_vl : var → hterm vl := ids_hvl.
Goal hvar_vl = λ n i, var_vl (n + i). done. Abort.

Definition hvnat n := liftA1 vnat (pureS n).
Goal hvnat = λ n, liftA0 (vnat n). done. Abort.

Definition hvabs := liftBind vabs.

Definition hvobj (ds : hterm vl → list (label * hterm dm)) : hterm vl :=
  liftBind vobj (liftList ∘ ds).

Definition hdtysyn := liftA1 dtysyn.
(* Not sure about [hdtysem], and not needed. *)
Definition hdvl := liftA1 dvl.

Definition hpv := liftA1 pv.
Definition hpself p l := Eval cbv in liftA2 pself p (pureS l).

Definition hTTop := liftA0 TTop.
Definition hTBot := liftA0 TBot.
Definition hTAnd := liftA2 TAnd.
Definition hTOr := liftA2 TOr.
Definition hTLater := liftA1 TLater.

Definition hTAll (T : hterm ty) (U : hterm vl → hterm ty) : hterm ty := λ i,
  (* liftBind (liftA1 TAll T i) U i. *)
  liftBind (TAll (T i)) U i.

Eval cbv -[plus minus] in hTAll.
Goal hTAll = λ T U i, (TAll (T i) (U (λ x, var_vl (x - S i)) (S i)))%ty. done. Abort.
(* Goal hTAll = λ T U i, (∀ (T i), U (λ x, var_vl (x - S i)) (S i))%ty. done. Abort. *)

Definition hTMu := liftBind TMu.
Definition hTVMem l := liftA1 (TVMem l).
Definition hTTMem l := liftA2 (TTMem l).
Definition hTSel p l := Eval cbv in liftA2 TSel p (pureS l).
Definition hTNat := liftA0 TNat.
Definition hTSing := liftA1 TSing.

Arguments hvobj _%dms.
Arguments hTAll _%ty _%ty.
Arguments hTMu _%ty.
End syn.

Module tests1.
(** * First test *)
(* Definition ex := hclose $ hTAll (liftA0 TNat) (λ x, hTMu (λ y, pureS $ TAnd (TSing (pv x)) (TSing (pv y)))). *)
(* ∀ (x : TNat), μ y, x.type ∧ x.type *)
Definition ex := hclose $ hTAll hTNat (λ x, hTMu (λ y, hTAnd (hTSing (hpv x)) (hTSing (hpv y)))).
Eval cbv in ex.
End tests1.

Module Import hoasNotation.
(* Notations. *)
Open Scope dms_scope.
Notation " {@ } " := (@nil (string * hterm dm)) (format "{@ }") : dms_scope.
Notation " {@ x } " := ( x :: {@} ) (format "{@  x  }"): dms_scope.
Notation " {@ x ; y ; .. ; z } " :=
  (cons x (cons y .. (cons z nil) ..))
  (* (format "{@  x ;  y ;  .. ;  z  }") *)
  (format "'[v' {@  '[' x ']' ;  '/' y ;  '/' .. ;  '/' z } ']'")
  : dms_scope.

Close Scope dms_scope.
Arguments hvobj _%dms_scope.

Notation "'ν' ds " := (hvobj ds) (at level 60, ds at next level).
Notation "'val' l = v" := (l, hdvl v) (at level 60, l at level 50).
Notation "'type' l = T  " := (l, hdtysyn T) (at level 60, l at level 50).

(** Notation for object types. *)
Open Scope ty_scope.
Notation "⊤" := hTTop : ty_scope.
Notation "⊥" := hTBot : ty_scope.
Notation " {@ T1 } " := ( hTAnd T1 ⊤ ) (format "{@  T1  }"): ty_scope.
Notation " {@ T1 ; T2 ; .. ; Tn } " :=
  (hTAnd T1 (hTAnd T2 .. (hTAnd Tn ⊤)..))
  (* (format "'[v' {@  '[' T1 ']'  ;   T2  ;   ..  ;   Tn } ']'") : ty_scope. *)
  (format "'[v' {@  '[' T1 ']'  ;  '/' T2  ;  '/' ..  ;  '/' Tn } ']'") : ty_scope.
Close Scope ty_scope.

Notation "'𝐍'" := hTNat : ty_scope.

Notation "'▶'" := hTLater : ty_scope.
(* Level taken from Iris. *)
Notation "'▶' T" := (hTLater T) (at level 49, right associativity) : ty_scope.

(* Useful for writing functions whose body is in scope [%ty]. *)
Notation "'λT' x .. y , t" := (fun x => .. (fun y => t%ty) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' 'λT'  x  ..  y ']' ,  '/' t ']'") : ty_scope.

Notation "'∀:' x : T , U" := (hTAll T (λT x, U)) (at level 48, x, T at level 98, U at level 98).
Notation "'μ' Ts" := (hTMu Ts) (at level 50, Ts at next level).
Notation "'μ:' x , Ts" := (hTMu (λT x, Ts)) (at level 50, Ts at next level).
Notation "'type' l >: L <: U" := (hTTMem l L U) (at level 60, l at level 50, L, U at level 70) : ty_scope.
Notation "'val' l : T" := (hTVMem l T)
  (at level 60, l, T at level 50, format "'[' 'val'  l  :  T  ']' '/'") : ty_scope.

Notation "S →: T" := (hTAll S (λ _ , T)) (at level 49, T at level 98, right associativity) : ty_scope.

Notation "p @; l" := (hTSel p l) (at level 48).
Notation "v @ l1 @ .. @ l2" := (hpself .. (hpself v l1) .. l2)
                                     (format "v  @  l1  @  ..  @  l2", at level 48, l1, l2 at level 40).
Notation tparam A := (type A >: ⊥ <: ⊤)%ty.
Definition typeEq l T := (type l >: T <: T) % ty.

Notation hx := hvar_vl.
Notation hx0 := (hx 0).
Notation hx1 := (hx 1).
Notation hx2 := (hx 2).
Notation hx3 := (hx 3).
Notation hx4 := (hx 4).
Notation hx5 := (hx 5).
Notation hx6 := (hx 6).

End hoasNotation.


Module tests.
Eval cbv in hclose {@ hTNat ; hTNat ; hTNat } % ty.

Definition ex := hclose $ hTAll hTNat (λ x, hTMu (λ y, hTAnd (hTSing (hpv x)) (hTSing (hpv y)))).
(** * Second, real, test *)
Definition listTBodyGen bool sci L U : hterm ty := μ λT self, {@
  type "A" >: L <: U;
  val "isEmpty" : ⊤ →: hpv bool @; "Boolean"; (* bool.Boolean *)
  val "head" : ⊤ →: hpv self @; "A"; (* self.A *)
  val "tail" : ⊤ →: hTAnd (hpv sci @; "List") (type "A" >: ⊥ <: hpv self @; "A" )
}.

Definition consTResConcr bool sci U := listTBodyGen bool sci U U.

 (* : ty_scope. *)
Definition consTConcr bool sci : hterm ty :=
  ∀: x: tparam "T",
    hpv x @; "T" →:
      hTAnd (hpv sci @; "List") (type "A" >: ⊥ <: hpv x @; "T") →:
      (consTResConcr bool sci (hpv x @; "T")).

(* Notation "'∀:' T ',' U" := (hTAll T U) (at level 49, T at level 98, U at level 98).
Definition consTConcr bool sci : hterm ty :=
  ∀: tparam "T", (λT x,
    (hpv x @; "T" →:
      hTAnd (hpv sci @; "List") (type "A" >: ⊥ <: hpv x @; "T") →:
      (consTResConcr bool sci (hpv x @; "T")))). *)

Definition consTConcr' bool sci : hterm ty :=
  hTAll (tparam "T") (λT x,
    (hpv x @; "T" →:
      hTAnd (hpv sci @; "List") (type "A" >: ⊥ <: hpv x @; "T") →:
      (consTResConcr bool sci (hpv x @; "T"))))%ty.

Goal consTConcr' = consTConcr. done. Qed.

(* Notation "∀: x .. y , P" := (hTAll x, .. (hTAll y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∀:  x  ..  y ']' ,  '/' P ']'") : type_scope. *)


Eval cbv in hclose $ consTConcr hx1 hx0.

End tests.


