From stdpp Require Import strings.
From D.Dot Require Import syn exampleInfra hoas.
From D.Dot Require typingExInfra.

Module TestDB.
Import DBNotation.

Check {@ TNat ; TNat ; TNat }%ty.

(* Check (TSel (pself (pself p0 1) 2) 3). *)
(* Check (x0 @ 1 @ 2 ; 3). *)

Check ν {@ val "a" = pv (vnat 0) }.

Check μ {@ type "A" >: TNat <: TTop }.
Check μ {@ val "a" : TNat }.
Check μ {@ type "A" >: TNat <: TTop ; val "a" : TNat ; val "b" : TNat }.

Check vobj {@}.
Check ν {@ }.
Check ν {@ val "a" = pv (vnat 0) }.
Check ν {@ val "a" = pv (vnat 0) ; val "b" = pv (vnat 1) }.

Check (p0 @; "A").
Check (pself (pself p0 "A") "B" @; "C").
Check (p0 @ "A").
Check (p0 @ "A" @ "B" @; "C").
Check (val "symb" : p0 @ "symbols" @; "Symbol")%ty.

Definition ta v := (0 < v)%E.
Print ta.
Definition tb v : tm := (v > 0)%E.
Print tb.
Definition tc v := (0 ≥ (v ≥ 0))%E.

Module TestStamped.
Import typingExInfra.
Check ν {@ type "A" = (σ1 ; s1) }.
Check ν {@ val "a" = pv (vnat 0); type "A" = (σ1 ; s1) }.
Check ν {@ val "a" = pv (vnat 0) ; type "A" = (σ1 ; s1) }.
End TestStamped.
End TestDB.

Module hoasTests.

Import hoasNotation hterm_lifting.

Goal hvar_vl = λ n i, var_vl (n + i). done. Abort.
Goal ∀ n, hvnat n = liftA0 (vnat n). done. Abort.
Goal hxm = λ i, ren (λ j, j - i). done. Abort.

(** * First test *)

(* ∀ (x : TNat), μ y, x.type ∧ x.type *)
Definition ex0 := hclose $ hTAll hTNat (λ x, hTMu (λ y, hTAnd (hTSing (hpv x)) (hTSing (hpv y)))).
Eval cbv in ex0.

Eval cbv -[plus minus] in hTAll.
Goal hTAll = λ T U i, (TAll (T i) (U (λ x, var_vl (x - S i)) (S i))). done. Abort.
(* Goal hTAll = λ T U i, (∀ (T i), U (λ x, var_vl (x - S i)) (S i)). done. Abort. *)

Eval cbv in hclose {@ hTNat ; hTNat ; hTNat } %HT.

Definition ex := hclose $ ∀: x : hTNat, hTMu (λ y, hTAnd (hTSing (hpv x)) (hTSing (hpv y))).
Goal ex = ex0. done. Abort.

Definition ex2 := hclose (λ: f, htv f).
Eval cbv in ex2.
Goal ex2 = vabs (tv DBNotation.x0). done. Qed.
Definition ex3 := hclose (λ:: f x, htapp (htv f) (htv x)).
Eval cbv in ex3.
Goal ex3 = tv (vabs (tv (vabs (tapp (tv DBNotation.x1) (tv DBNotation.x0))))). done. Abort.
End hoasTests.
