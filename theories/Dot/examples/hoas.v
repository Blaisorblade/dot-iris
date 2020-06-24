(* A HOAS frontend to generate de Bruijn DOT terms for examples.

While some more examples could use this frontend (and they don't, due to
historical reasons), beware this frontend is not fully transparent, and in
particular is not suitable for robust typing lemmas.
*)

From D Require Import tactics.
From D.Dot Require Import syn ex_utils.

Set Default Proof Using "Type".

(*
The algorithm we use is very different from McBride's Jigger:
https://web.archive.org/web/20130412082828/http://www.e-pig.org/epilogue/?p=773

Jigger exploits type inference and well-scoped de Bruijn terms.
*)

(**
Our algorithm is inspired by Atkey's et al.'s
"Unembedding Domain-Specific Languages", Haskell'09,
https://doi.org/10.1145/1596638.1596644. *)

(* Our HOAS terms are functions from the number of free variables in scope
to an actual de Bruijn term. *)
(** Type of HOAS terms. *)
Definition hterm sort := var → sort.

(* We can convert a closed HOAS term to a de Bruijn one by apply the term to 0. *)
(** Convert a closed HOAS term to the corresponding de Bruijn term. *)
Definition hclose {s1} : hterm s1 → s1 := Eval cbv in (.$ 0).

(* Here in [hclose] and below, the point of [Eval cbv] is to improve the
results of simplification, by hiding all the abstractions used to define our
combinators on HOAS terms. *)
#[global] Arguments hclose /.
Definition pureS {s1} : s1 → hterm s1 := λ x _, x.
#[global] Arguments pureS /.

(** We can't set up coercions across [hterm A] and [hterm B], hence add
definitions and identity coercions via [SubClass]. *)
SubClass htm   := hterm tm.
SubClass hvl   := hterm vl.
SubClass hdm   := hterm dm.
SubClass hpath := hterm path.
SubClass hty   := hterm ty.
SubClass hdms  := list (label * hterm dm).

Coercion hclose_tm   := hclose : htm   → tm.
Coercion hclose_vl   := hclose : hvl   → vl.
Coercion hclose_dm   := hclose : hdm   → dm.
Coercion hclose_path := hclose : hpath → path.
Coercion hclose_ty   := hclose : hty   → ty.

Arguments hclose_tm   /.
Arguments hclose_vl   /.
Arguments hclose_dm   /.
Arguments hclose_path /.
Arguments hclose_ty   /.

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

Definition liftBind1 (con : s2 → s3) (f : hvl → hterm s2) : hterm s3 :=
  Eval cbv -[minus] in λ i,
  let i' := i.+1 in
  let v := ren (λ j, j - i') in
  con (f v i').

Definition liftBind2 (con : s1 → s2 → s3) (a1 : hterm s1) (a2 : hvl → hterm s2) : hterm s3 :=
  Eval unfold liftBind1 in
  λ i, liftBind1 (con (a1 i)) a2 i.

Definition liftList : list (label * hdm) → hterm (list (label * dm)) := λ ds i, map (mapsnd (.$ i)) ds.

#[global] Arguments apS /.
#[global] Arguments bindS /.

#[global] Arguments liftA0 /.
#[global] Arguments liftA1 /.
#[global] Arguments liftA2 /.
#[global] Arguments liftA3 /.
#[global] Arguments liftBind1 /.
#[global] Arguments liftBind2 /.
#[global] Arguments liftList /.

End lifting.
End hterm_lifting.

(* Binders in our language: λ, ν, ∀, μ. *)

(** We define a scope for term and type syntax.

We bind it to [hty], [htm], and also to [hterm], to get the right scopes for
combinators like [hclose].

We can only bind one scope to [hterm], and that is why we use a unique scope
for all this syntax.
*)
Declare Scope hsyn_scope.
Bind Scope hsyn_scope with hty htm hterm.
Delimit Scope hsyn_scope with HS.

Declare Scope hdms_scope.
Bind Scope hdms_scope with hdms.
Delimit Scope hdms_scope with HD.

Instance ids_hvl : Ids hvl := λ x, (* [x]: input to the substitution. *)
  (* Resulting [vl]. *)
  λ i, ids (x + i).

#[global] Arguments ids_hvl /.

Module Export syn.

Coercion htv := liftA1 tv : hvl → htm.
Definition htapp : htm → htm → htm := liftA2 tapp.
Definition htproj : htm → label → htm := Eval cbv in λ t l, liftA2 tproj t (pureS l).
Definition htskip : htm → htm := liftA1 tskip.
Definition htif : htm → htm → htm → htm := liftA3 tif.
Definition htun : un_op → htm → htm := λ u, liftA1 (tun u).
Definition htbin : bin_op → htm → htm → htm := λ b, liftA2 (tbin b).

Definition hvvar : var → hvl := ids_hvl.

Coercion hvlit := (λ l, liftA1 vlit (pureS l)) : base_lit → hvl.
Notation hvint n := (hvlit $ lint n).

Definition hvabs : (hvl → htm) → hvl := liftBind1 vabs.

Definition hvobj : (hvl → hdms) → hvl := λ ds,
  liftBind1 vobj (liftList ∘ ds).

Definition hdtysyn : hty → hdm := liftA1 dtysyn.
Definition hdtysem (σ : list hvl) s : hdm := λ x, dtysem (map (.$ x) σ) s.
Definition hdpt : hpath → hdm := liftA1 dpt.

Coercion hpv := liftA1 pv : hvl → hpath.
Definition hpself : hpath → label → hpath :=
  Eval unfold liftA2, pureS in λ p l, liftA2 pself p (pureS l).

Definition hTTop : hty := liftA0 TTop.
Definition hTBot : hty := liftA0 TBot.
Definition hTAnd : hty → hty → hty := liftA2 TAnd.
Definition hTOr : hty → hty → hty := liftA2 TOr.
Definition hTLater : hty → hty := liftA1 TLater.

(* Eta-expanded to get nicer argument names. *)
Definition hTAll : hty → (hvl → hty) → hty :=
  Eval unfold liftBind2 in λ S T, liftBind2 TAll S T.

Definition hTMu : (hvl → hty) → hty := liftBind1 TMu.
Definition hTVMem : label → hty → hty := λ l, liftA1 (TVMem l).
Definition hTTMem : label → hty → hty → hty := λ l, liftA2 (λ L U, TTMem l L U).
Definition hTTMemL : label → hty → hty → hty := λ l, liftA2 (TTMemL l).
Definition hTSel : hpath → label → hty := Eval cbv in λ p l, liftA2 TSel p (pureS l).
Definition hTPrim b : hty := liftA0 (TPrim b).
Definition hTSing : hpath → hty := liftA1 TSing.

Definition hTInt : hty := liftA0 TInt.
Definition hTBool : hty := liftA0 TBool.

Arguments hvobj _%HD.
Arguments hTAll _%HS _%HS.
Arguments hTMu _%HS.

Arguments htv /.
Arguments htapp /.
Arguments htproj /.
Arguments htskip /.
Arguments htif /.
Arguments htun /.
Arguments htbin /.
Arguments hvvar /.
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
Arguments hTTMemL /.
Arguments hTSel /.
Arguments hTPrim /.
Arguments hTSing /.

Arguments hTInt /.
Arguments hTBool /.

End syn.

Module Import hoasNotation.

(* Primitive operations. *)
Notation "e1 + e2" := (htbin bplus e1%HS e2%HS) : hsyn_scope.
Notation "e1 - e2" := (htbin bminus e1%HS e2%HS) : hsyn_scope.
Notation "e1 * e2" := (htbin btimes e1%HS e2%HS) : hsyn_scope.
Notation "e1 `div` e2" := (htbin bdiv e1%HS e2%HS) : hsyn_scope.

Notation "e1 ≤ e2" := (htbin ble e1%HS e2%HS) : hsyn_scope.
Notation "e1 < e2" := (htbin blt e1%HS e2%HS) : hsyn_scope.
Notation "e1 = e2" := (htbin beq e1%HS e2%HS) : hsyn_scope.
Notation "e1 ≠ e2" := (htun unot (htbin beq e1%HS e2%HS)) : hsyn_scope.

Notation "~ e" := (htun unot e%HS) (at level 75, right associativity) : hsyn_scope.

Notation "e1 > e2" := (e2%HS < e1%HS)%HS : hsyn_scope.
Notation "e1 ≥ e2" := (e2%HS ≤ e1%HS)%HS : hsyn_scope.

(* Notations. *)
Open Scope hdms_scope.
Notation "{@ }" := (@nil (string * hdm)) (format "{@ }") : hdms_scope.
Notation "{@ x }" := ( x :: {@} ) (format "{@  x  }"): hdms_scope.
Notation "{@ x ; y ; .. ; z }" :=
  (cons x (cons y .. (cons z nil) ..))
  (format "'[v' {@  '[' x ']' ;  '/' y ;  '/' .. ;  '/' z } ']'")
  : hdms_scope.

Close Scope hdms_scope.

(* Useful for writing functions whose body is in scope [%HS]. *)
Notation "'λT' x .. y , t" := (fun x => .. (fun y => t%HS) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : hsyn_scope.

(* Useful for writing functions whose body is in scope [%HD]. *)
Notation "'λD' x .. y , t" := (fun x => .. (fun y => t%HD) ..)
  (at level 200, x binder, y binder, right associativity,
  only parsing) : hdms_scope.

(** Value lambda. Relies on inserting [htv] coercions in the output. *)
Notation "'λ:' x .. y , t" := (hvabs (fun x => .. (hvabs (fun y => t%HS)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' 'λ:'  x  ..  y ']' ,  '/' t ']'").

Notation "'ν' ds" := (hvobj ds) (at level 60, ds at next level).
Notation "'ν:' x , ds" := (hvobj (λD x, ds)) (at level 60, ds at next level).
Notation "'val' l = v" := (l, hdpt v) (at level 60, l at level 50).
Notation "'type' l = T" := (l, hdtysyn T) (at level 60, l at level 50).
Notation "'type' l = ( σ ; s )" := (l, hdtysem σ s) (at level 60, l at level 50).

(** Notation for object types. *)
#[global] Instance: Top hty := hTTop.
#[global] Instance: Bottom hty := hTBot.
Open Scope hsyn_scope.
Notation "{@ T1 }" := ( hTAnd T1 ⊤ ) (format "{@  T1  }"): hsyn_scope.
Notation "{@ T1 ; T2 ; .. ; Tn }" :=
  (hTAnd T1 (hTAnd T2 .. (hTAnd Tn ⊤)..))
  (format "'[v' {@  '[' T1 ']'  ;  '/' T2  ;  '/' ..  ;  '/' Tn } ']'") : hsyn_scope.
Close Scope hsyn_scope.

Notation "'𝐙'" := hTInt : hsyn_scope.

Notation "▶:" := hTLater : hsyn_scope.
Notation "▶: T" := (hTLater T) (at level 49, right associativity) : hsyn_scope.

Notation "'∀:' x : T , U" := (hTAll T (λT x, U)) (at level 48, x, T at level 98, U at level 98).
Notation "'μ' Ts" := (hTMu Ts) (at level 50, Ts at next level).
Notation "'μ:' x , Ts" := (hTMu (λT x, Ts)) (at level 50, Ts at next level).
Notation "'type' l >: L <: U" := (hTTMemL l L U) (at level 60, l at level 50, L, U at level 70) : hsyn_scope.
Notation "'val' l : T" := (hTVMem l T)
  (at level 60, l, T at level 50, format "'[' 'val'  l  :  T  ']' '/'") : hsyn_scope.

Notation "S →: T" := (hTAll S (λT _ , T)) (at level 49, T at level 98, right associativity) : hsyn_scope.

Notation "p @; l" := (hTSel p l) (at level 48).
Notation "v @ l1 @ .. @ l2" := (hpself .. (hpself v l1) .. l2)
                                     (format "v  @  l1  @  ..  @  l2", at level 48, l1, l2 at level 40).
Notation "a @: b" := (htproj a b) (at level 59, b at next level).

Infix "$:" := htapp (at level 68, left associativity).

Notation tparam A := (type A >: ⊥ <: ⊤)%HS.
Definition typeEq l T := (type l >: T <: T) %HS.

Notation hx := hvvar.

Notation hx0 := (hx 0).
Notation hx1 := (hx 1).
Notation hx2 := (hx 2).
Notation hx3 := (hx 3).
Notation hx4 := (hx 4).
Notation hx5 := (hx 5).
Notation hx6 := (hx 6).

(** Denote a variable by de Bruijn level. Needed in some scenarios, but not
recommended. *)
Definition hxm i : hvl := λ j, vvar (j - i).

(** Additional syntactic sugar, in HOAS version *)
Definition hlett t u := htapp (hvabs u) t.
Arguments hlett /.
Notation "hlett: x := t in: u" := (htapp (λ: x, u) t) (at level 80).

Definition hpackTV l T := ν: self, {@ type l = T }.
Definition htyApp t l T :=
  hlett: x := t in:
  hlett: a := hpackTV l T in:
    x $: a.

Definition hAnfBind t := hlett: x := t in: x.

(* Notation "∀: x .. y , P" := (hTAll x, .. (hTAll y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∀:  x  ..  y ']' ,  '/' P ']'") : type_scope. *)
End hoasNotation.
