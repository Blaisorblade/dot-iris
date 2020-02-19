(* A HOAS frontend for de Bruijn terms. *)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra.

Set Default Proof Using "Type".

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

Notation htm'   := (hterm tm).
Notation hvl'   := (hterm vl).
Notation hdm'   := (hterm dm).
Notation hpath' := (hterm path).
Notation hty'   := (hterm ty).
Notation hdms'  := (list (label * hdm')).

(** We can't set up coercions across [hterm A] and [hterm B], hence add
definitions and identity coercions via [SubClass]. *)
SubClass htm   := htm'.
SubClass hvl   := hvl'.
SubClass hdm   := hdm'.
SubClass hpath := hpath'.
SubClass hty   := hty'.
SubClass hdms  := hdms'.

Notation hstampTy := (preTyMem hvl).

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

Definition liftBind (con : s1 → s2) (f : hvl → hterm s1) : hterm s2 := λ i,
  let i' := S i in
  let v := ren (λ j, j - i') in
  con (f v i').

Definition liftList : list (label * hdm) → hterm (list (label * dm)) := λ ds i, map (mapsnd (.$ i)) ds.

Global Arguments apS /.
Global Arguments bindS /.

Global Arguments liftA0 /.
Global Arguments liftA1 /.
Global Arguments liftA2 /.
Global Arguments liftA3 /.
Global Arguments liftBind /.
Global Arguments liftList /.

(* Ever used? Likely not. *)
(* Definition hshift : hterm s1 → hterm s1 := λ t i, t (S i). *)
End lifting.
End hterm_lifting.

(* Binders in our language: λ, ν, ∀, μ. *)

(** We bind also to [hty'] to support well combinators like [hclose]. *)
Declare Scope hty_scope.
Bind Scope hty_scope with hty hty'.
Delimit Scope hty_scope with HT.

Declare Scope hdms_scope.
Bind Scope hdms_scope with hdms hdms'.
Delimit Scope hdms_scope with HD.

(* [htm'] here interferes: we can only bind one scope to [hterm]. Merge them!*)
Declare Scope hexpr_scope.
Bind Scope hexpr_scope with htm.
Delimit Scope hexpr_scope with HE.

Instance ids_hvl : Ids hvl := λ x, (* [x]: input to the substitution. *)
  (* Resulting [vl]. *)
  λ i, ids (x + i).

Global Arguments ids_hvl /.

Module Import syn.

Coercion htv := liftA1 tv : hvl → htm.
Definition htapp : htm → htm → htm := liftA2 tapp.
Definition htproj : htm → label → nat → tm := Eval cbv in λ t l, liftA2 tproj t (pureS l).
Definition htskip : htm → htm := liftA1 tskip.
Definition htif : htm → htm → htm → htm := liftA3 tif.
Definition htun : un_op → htm → htm := λ u, liftA1 (tun u).
Definition htbin : bin_op → htm → htm → htm := λ b, liftA2 (tbin b).

Definition hvar_vl : var → hvl := ids_hvl.

Coercion hvlit := (λ l, liftA1 vlit (pureS l)) : base_lit → hvl.
Notation hvnat n := (hvlit $ lnat n).

Definition hvabs : (hvl → htm) → hvl := liftBind vabs.

Definition hvobj : (hvl → hdms) → hvl := λ ds,
  liftBind vobj (liftList ∘ ds).

Definition hdtysyn : hty → hdm := liftA1 dtysyn.
Definition hdtysem (σ : list hvl) s : hdm := λ x, dtysem (map (.$ x) σ) s.
(* Not sure about [hdtysem], and not needed. *)
Definition hdpt : hpath → hdm := liftA1 dpt.

Coercion hpv := liftA1 pv : hvl → hpath.
Definition hpself : hpath → label → nat → path := Eval cbv in λ p l, liftA2 pself p (pureS l).

Definition hTTop : hty := liftA0 TTop.
Definition hTBot : hty := liftA0 TBot.
Definition hTAnd : hty → hty → hty := liftA2 TAnd.
Definition hTOr : hty → hty → hty := liftA2 TOr.
Definition hTLater : hty → hty := liftA1 TLater.

Definition hTAll : hty → (hvl → hty) → hty := λ T U i,
  (* liftBind (liftA1 TAll T i) U i. *)
  liftBind (TAll (T i)) U i.

Definition hTMu : (hvl → hty) → hty := liftBind TMu.
Definition hTVMem : label → hty → hty := λ l, liftA1 (TVMem l).
Definition hTTMem : label → hty → hty → hty := λ l, liftA2 (TTMem l).
Definition hTSel : hpath → label → nat → ty := Eval cbv in λ p l, liftA2 TSel p (pureS l).
Definition hTPrim b : hty := liftA0 (TPrim b).
Definition hTSing : hpath → hty := liftA1 TSing.

Definition hTNat : hty := liftA0 TNat.
Definition hTBool : hty := liftA0 TBool.

Arguments hvobj _%HD.
Arguments hTAll _%HT _%HT.
Arguments hTMu _%HT.

Arguments htv /.
Arguments htapp /.
Arguments htproj /.
Arguments htskip /.
Arguments htif /.
Arguments htun /.
Arguments htbin /.
Arguments hvar_vl /.
Arguments hvlit /.
Arguments hvabs /.
Arguments hvobj /.
Arguments hdtysyn /.
Arguments hdtysem /.
Arguments hdpt /.
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
Arguments hTPrim /.
Arguments hTSing /.

Arguments hTNat /.
Arguments hTBool /.

End syn.

Module Import hoasNotation.
Export syn.

(* Primitive operations. *)
Notation "e1 + e2" := (htbin bplus e1%HE e2%HE) : hexpr_scope.
Notation "e1 - e2" := (htbin bminus e1%HE e2%HE) : hexpr_scope.
Notation "e1 * e2" := (htbin btimes e1%HE e2%HE) : hexpr_scope.
Notation "e1 `div` e2" := (htbin bdiv e1%HE e2%HE) : hexpr_scope.
(* Notation "e1 `rem` e2" := (htbin RemOp e1%HE e2%HE) : hexpr_scope. *)

Notation "e1 ≤ e2" := (htbin ble e1%HE e2%HE) : hexpr_scope.
Notation "e1 < e2" := (htbin blt e1%HE e2%HE) : hexpr_scope.
Notation "e1 = e2" := (htbin beq e1%HE e2%HE) : hexpr_scope.
Notation "e1 ≠ e2" := (htun unot (htbin beq e1%HE e2%HE)) : hexpr_scope.

Notation "~ e" := (htun unot e%HE) (at level 75, right associativity) : hexpr_scope.

Notation "e1 > e2" := (e2%HE < e1%HE)%HE : hexpr_scope.
Notation "e1 ≥ e2" := (e2%HE ≤ e1%HE)%HE : hexpr_scope.

(* Notations. *)
Open Scope hdms_scope.
Notation " {@ } " := (@nil (string * hdm)) (format "{@ }") : hdms_scope.
Notation " {@ x } " := ( x :: {@} ) (format "{@  x  }"): hdms_scope.
Notation " {@ x ; y ; .. ; z } " :=
  (cons x (cons y .. (cons z nil) ..))
  (* (format "{@  x ;  y ;  .. ;  z  }") *)
  (format "'[v' {@  '[' x ']' ;  '/' y ;  '/' .. ;  '/' z } ']'")
  : hdms_scope.

Close Scope hdms_scope.

(* Useful for writing functions whose body is in scope [%HT]. *)
Notation "'λT' x .. y , t" := (fun x => .. (fun y => t%HT) ..)
  (at level 200, x binder, y binder, right associativity, only parsing,
  format "'[  ' '[  ' 'λT'  x  ..  y ']' ,  '/' t ']'") : hty_scope.

(* Useful for writing functions whose body is in scope [%HD]. *)
Notation "'λD' x .. y , t" := (fun x => .. (fun y => t%HD) ..)
  (at level 200, x binder, y binder, right associativity, only parsing,
  format "'[  ' '[  ' 'λD'  x  ..  y ']' ,  '/' t ']'") : hdms_scope.

(** Value lambda. Relies on inserting [htv] coercions in the output. *)
Notation "'λ:' x .. y , t" := (hvabs (fun x => .. (hvabs (fun y => t%HE)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' 'λ:'  x  ..  y ']' ,  '/' t ']'").

(** Term lambda. Does not rely on coercions, and is more annoying. *)
Notation "'λ::' x .. y , t" := (htv (hvabs (fun x => .. (htv (hvabs (fun y => t%HE))) ..)))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' 'λ::'  x  ..  y ']' ,  '/' t ']'").

Notation "'ν' ds " := (hvobj ds) (at level 60, ds at next level).
Notation "'ν:' x , ds " := (hvobj (λD x, ds)) (at level 60, ds at next level).
Notation "'val' l = v" := (l, hdpt v) (at level 60, l at level 50).
Notation "'type' l = T  " := (l, hdtysyn T) (at level 60, l at level 50).

Definition hdtysem' : hstampTy → hdm := λ '(MkTy s hσ _ _), hdtysem hσ s.
Arguments hdtysem' !_ /.

Notation "'type' l '=[' T ']'" := (l, hdtysem' T) (at level 60, l at level 50, T at level 200).

(** Notation for object types. *)
Global Instance: Top hty := hTTop.
Global Instance: Bottom hty := hTBot.
Open Scope hty_scope.
Notation " {@ T1 } " := ( hTAnd T1 ⊤ ) (format "{@  T1  }"): hty_scope.
Notation " {@ T1 ; T2 ; .. ; Tn } " :=
  (hTAnd T1 (hTAnd T2 .. (hTAnd Tn ⊤)..))
  (* (format "'[v' {@  '[' T1 ']'  ;   T2  ;   ..  ;   Tn } ']'") : hty_scope. *)
  (format "'[v' {@  '[' T1 ']'  ;  '/' T2  ;  '/' ..  ;  '/' Tn } ']'") : hty_scope.
Close Scope hty_scope.

Notation "'𝐍'" := hTNat : hty_scope.

Notation "▶:" := hTLater : hty_scope.
Notation "▶: T" := (hTLater T) (at level 49, right associativity) : hty_scope.

Notation "'∀:' x : T , U" := (hTAll T (λT x, U)) (at level 48, x, T at level 98, U at level 98).
Notation "'μ' Ts" := (hTMu Ts) (at level 50, Ts at next level).
Notation "'μ:' x , Ts" := (hTMu (λT x, Ts)) (at level 50, Ts at next level).
Notation "'type' l >: L <: U" := (hTTMem l L U) (at level 60, l at level 50, L, U at level 70) : hty_scope.
Notation "'val' l : T" := (hTVMem l T)
  (at level 60, l, T at level 50, format "'[' 'val'  l  :  T  ']' '/'") : hty_scope.

Notation "S →: T" := (hTAll S (λT _ , T)) (at level 49, T at level 98, right associativity) : hty_scope.

Notation "p @; l" := (hTSel p l) (at level 48).
Notation "v @ l1 @ .. @ l2" := (hpself .. (hpself v l1) .. l2)
                                     (format "v  @  l1  @  ..  @  l2", at level 48, l1, l2 at level 40).
Notation "a @: b" := (htproj a b) (at level 59, b at next level).

Infix "$:" := htapp (at level 68, left associativity).

Notation tparam A := (type A >: ⊥ <: ⊤)%HT.
Definition typeEq l T := (type l >: T <: T) %HT.

Notation hx := hvar_vl.

Notation hx0 := (hx 0).
Notation hx1 := (hx 1).
Notation hx2 := (hx 2).
Notation hx3 := (hx 3).
Notation hx4 := (hx 4).
Notation hx5 := (hx 5).
Notation hx6 := (hx 6).

(** Denote a variable by de Bruijn level. Needed in some scenarios, but not
recommended. *)
Definition hxm i : hvl := λ j, var_vl (j - i).

Notation hpx n := (hpv (hx n)).
Notation hp0 := (hpx 0).
Notation hp1 := (hpx 1).
Notation hp2 := (hpx 2).
Notation hp3 := (hpx 3).
Notation hp4 := (hpx 4).
Notation hp5 := (hpx 5).
Notation hp6 := (hpx 6).

(** Additional syntactic sugar, in HOAS version *)
Definition hvabs' x := htv (hvabs x).
Arguments hvabs' /.

Definition hlett t u := htapp (hvabs' u) t.
Arguments hlett /.
Notation "hlett: x := t in: u" := (htapp (λ:: x, u) t) (at level 80).

Definition hpackTV l T := ν: self, {@ type l = T }.
Definition htyApp t l T :=
  hlett: x := t in:
  hlett: a := htv (hpackTV l T) in:
    htv x $: htv a.

Definition hAnfBind t := hlett: x := t in: htv x.

(* Notation "∀: x .. y , P" := (hTAll x, .. (hTAll y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∀:  x  ..  y ']' ,  '/' P ']'") : type_scope. *)
End hoasNotation.
