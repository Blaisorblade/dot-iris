(* A HOAS frontend for de Bruijn terms. *)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra.

(* Inspired by the "Unembedding DSLs" paper, but specialized.
The algorithm it uses is very different from McBride's Jigger.
https://web.archive.org/web/20130412082828/http://www.e-pig.org/epilogue/?p=773
It’s made possible exactly because our de Bruijn terms have a type indexed by the number of variables in scope.
*)
(* TODO? Check out:
  http://www.cs.uu.nl/research/techreps/repo/CS-2012/2012-009.pdf
*)
Definition hterm sort := var → sort.
Definition hclose {s1} : hterm s1 → s1 := (.$ 0).
Global Arguments hclose /.
Definition pureS {s1} : s1 → hterm s1 := λ x _, x.
Global Arguments pureS /.

(** Utilities to lift syntax to [hterm]s. *)
Module Import hterm_lifting.
Section lifting.
Context {s1 s2 s3 s4: Type}.

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

Global Arguments apS /.
Global Arguments bindS /.

Global Arguments liftA0 /.
Global Arguments liftA1 /.
Global Arguments liftA2 /.
Global Arguments liftA3 /.

Definition liftBind (con : s1 → s2) (f : hterm vl → hterm s1) : hterm s2 := λ i,
  let i' := S i in
  let v := ren (λ j, j - i') in
  con (f v i').

Definition liftList : list (label * hterm dm) → hterm (list (label * dm)) := λ ds i, map (mapsnd (.$ i)) ds.

(* Ever used? Likely not. *)
(* Definition hshift : hterm s1 → hterm s1 := λ t i, t (S i). *)
End lifting.
End hterm_lifting.

(* Binders in our language: λ, ν, ∀, μ. *)
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

Global Arguments ids_hvl /.

Module Import syn.

Definition htv : hvl → hterm tm := liftA1 tv.
Definition htapp : hterm tm → hterm tm → hterm tm := liftA2 tapp.
Definition htproj : hterm tm → label → nat → tm := Eval cbv in λ t l, liftA2 tproj t (pureS l).
Definition htskip : hterm tm → hterm tm := liftA1 tskip.

Definition hvar_vl : var → hterm vl := ids_hvl.
Goal hvar_vl = λ n i, var_vl (n + i). done. Abort.

Definition hvnat : nat → hterm vl := λ n, liftA1 vnat (pureS n).
Goal hvnat = λ n, liftA0 (vnat n). done. Abort.

Definition hvabs : (hterm vl → hterm tm) → hterm vl := liftBind vabs.

Definition hvobj : (hterm vl → hdms) → hterm vl := λ ds,
  liftBind vobj (liftList ∘ ds).

Definition hdtysyn : hterm ty → hterm dm := liftA1 dtysyn.
(* Not sure about [hdtysem], and not needed. *)
Definition hdvl : hterm vl → hterm dm := liftA1 dvl.

Definition hpv : hterm vl → hterm path := liftA1 pv.
Definition hpself : hterm path → label → nat → path := Eval cbv in λ p l, liftA2 pself p (pureS l).

Definition hTTop : hterm ty := liftA0 TTop.
Definition hTBot : hterm ty := liftA0 TBot.
Definition hTAnd : hterm ty → hterm ty → hterm ty := liftA2 TAnd.
Definition hTOr : hterm ty → hterm ty → hterm ty := liftA2 TOr.
Definition hTLater : hterm ty → hterm ty := liftA1 TLater.

Definition hTAll : hterm ty → (hterm vl → hterm ty) → hterm ty := λ T U i,
  (* liftBind (liftA1 TAll T i) U i. *)
  liftBind (TAll (T i)) U i.

Eval cbv -[plus minus] in hTAll.
Goal hTAll = λ T U i, (TAll (T i) (U (λ x, var_vl (x - S i)) (S i)))%ty. done. Abort.
(* Goal hTAll = λ T U i, (∀ (T i), U (λ x, var_vl (x - S i)) (S i))%ty. done. Abort. *)

Definition hTMu : (hterm vl → hterm ty) → hterm ty := liftBind TMu.
Definition hTVMem : label → hterm ty → hterm ty := λ l, liftA1 (TVMem l).
Definition hTTMem : label → hterm ty → hterm ty → hterm ty := λ l, liftA2 (TTMem l).
Definition hTSel : hterm path → label → nat → ty := Eval cbv in λ p l, liftA2 TSel p (pureS l).
Definition hTNat : hterm ty := liftA0 TNat.
Definition hTSing : hterm path → hterm ty := liftA1 TSing.

Arguments hvobj _%dms.
Arguments hTAll _%ty _%ty.
Arguments hTMu _%ty.

Arguments htv /.
Arguments htapp /.
Arguments htproj /.
Arguments htskip /.
Arguments hvar_vl /.
Arguments hvnat /.
Arguments hvabs /.
Arguments hvobj /.
Arguments hdtysyn /.
Arguments hdvl /.
Arguments hpv /.
Arguments hpself /.
Arguments hTTop /.
Arguments hTBot /.
Arguments hTAnd /.
Arguments hTOr /.
Arguments hTLater /.
Arguments hTAll /.
Arguments hTMu /.
Arguments hTVMem /.
Arguments hTTMem /.
Arguments hTSel /.
Arguments hTNat /.
Arguments hTSing /.

End syn.

Module tests1.
(** * First test *)
(* Definition ex := hclose $ hTAll (liftA0 TNat) (λ x, hTMu (λ y, pureS $ TAnd (TSing (pv x)) (TSing (pv y)))). *)
(* ∀ (x : TNat), μ y, x.type ∧ x.type *)
Definition ex := hclose $ hTAll hTNat (λ x, hTMu (λ y, hTAnd (hTSing (hpv x)) (hTSing (hpv y)))).
Eval cbv in ex.
End tests1.

Module Import hoasNotation.
Export syn.
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

(* Useful for writing functions whose body is in scope [%ty]. *)
Notation "'λT' x .. y , t" := (fun x => .. (fun y => t%ty) ..)
  (at level 200, x binder, y binder, right associativity, only parsing,
  format "'[  ' '[  ' 'λT'  x  ..  y ']' ,  '/' t ']'") : ty_scope.

(* Useful for writing functions whose body is in scope [%dms]. *)
Notation "'λD' x .. y , t" := (fun x => .. (fun y => t%dms) ..)
  (at level 200, x binder, y binder, right associativity, only parsing,
  format "'[  ' '[  ' 'λD'  x  ..  y ']' ,  '/' t ']'") : dms_scope.

Notation "'λ:' x , t" := (hvabs (fun x => t))
  (at level 200, right associativity,
  format "'[  ' '[  ' 'λ:'  x  ']' ,  '/' t ']'").

Notation "'λ::' x .. y , t" := (htv (hvabs (fun x => .. (htv (hvabs (fun y => t))) ..)))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' 'λ::'  x  ..  y ']' ,  '/' t ']'").

Notation "'ν' ds " := (hvobj ds) (at level 60, ds at next level).
Notation "'ν:' x , ds " := (hvobj (λD x, ds)) (at level 60, ds at next level).
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

Notation hpx n := (hpv (hx n)).
Notation hp0 := (hpx 0).
Notation hp1 := (hpx 1).
Notation hp2 := (hpx 2).
Notation hp3 := (hpx 3).
Notation hp4 := (hpx 4).
Notation hp5 := (hpx 5).
Notation hp6 := (hpx 6).

End hoasNotation.


Module tests.
Eval cbv in hclose {@ hTNat ; hTNat ; hTNat } % ty.

Definition ex := hclose $ hTAll hTNat (λ x, hTMu (λ y, hTAnd (hTSing (hpv x)) (hTSing (hpv y)))).

Definition ex2 := hclose (λ: f, htv f).
Eval cbv in ex2.
Goal ex2 = vabs (tv DBNotation.x0). done. Qed.
Definition ex3 := hclose (λ:: f x, htapp (htv f) (htv x)).
Eval cbv in ex3.
Goal ex3 = tv (vabs (tv (vabs (tapp (tv DBNotation.x1) (tv DBNotation.x0))))). done. Qed.

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
  ∀: x : tparam "T",
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


