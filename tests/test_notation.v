From stdpp Require Import strings.
From D.Dot Require Import syn exampleInfra hoas.
From D.Dot Require typingExInfra.

Module TestDB.
Import DBNotation.

Open Scope Z_scope.

Check {@ TInt ; TInt ; TInt }%ty.

(* Check (TSel (pself (pself p0 1) 2) 3). *)
(* Check (x0 @ 1 @ 2 ; 3). *)

Check ν {@ val "a" = pv (vint 0) }.

Check μ {@ type "A" >: TInt <: ⊤}.
Check μ {@ val "a" : TInt }.
Check μ {@ type "A" >: TInt <: ⊤ ; val "a" : TInt ; val "b" : TInt }.

Check vobj {@}.
Check ν {@ }.
Check ν {@ val "a" = pv (vint 0) }.
Check ν {@ val "a" = pv (vint 0) ; val "b" = pv (vint 1) }.

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
Check ν {@ val "a" = pv (vint 0); type "A" = (σ1 ; s1) }.
Check ν {@ val "a" = pv (vint 0) ; type "A" = (σ1 ; s1) }.
End TestStamped.
End TestDB.

Module hoasTests.

Import hoasNotation hterm_lifting.

Definition hanyToNothing : ty := hclose (⊤ →: ⊥).
Print hanyToNothing.
Definition hloopDefT : hty := val "loop" : ⊤ →: ⊥.
Print hloopDefT.

Definition lambda := λ: self, htv self @: "loop" $: htv self.
Definition curriedLambda := λ: self v, htv self @: "loop" $: htv v.

(* Confusing error message. It does make sense, but only once you figure it
out. *)
Implicit Type (v : vl).
Fail Definition curriedLambda' := λ: self v, htv self @: "loop" $: htv v.
Definition curriedLambda' := λ: self w, htv self @: "loop" $: htv w.


(* Bind Scope hexpr_scope with htm htm'. *)

Check (0 : htm).
Check (1 < 2)%HE.
Check (1 > 2)%HE.
Check (1 ≥ 2)%HE.
Check (1 > 0)%HE.

Goal hvar_vl = λ n i, var_vl (n + i). done. Abort.
Goal ∀ n, hvint n = liftA0 (vint n). done. Abort.
Goal hxm = λ i, ren (λ j, j - i). done. Abort.

(** * First test *)

(* ∀ (x : TInt), μ y, x.type ∧ x.type *)
Definition ex0 := hclose $ hTAll hTInt (λ x, hTMu (λ y, hTAnd (hTSing (hpv x)) (hTSing (hpv y)))).
Eval cbv in ex0.

Eval cbv -[plus minus] in hTAll.
Goal hTAll = λ T U i, (TAll (T i) (U (λ x, var_vl (x - S i)) (S i))). done. Abort.
(* Goal hTAll = λ T U i, (∀ (T i), U (λ x, var_vl (x - S i)) (S i)). done. Abort. *)

Eval cbv in hclose {@ hTInt ; hTInt ; hTInt } %HT.

Definition ex := hclose $ ∀: x : hTInt, hTMu (λ y, hTAnd (hTSing (hpv x)) (hTSing (hpv y))).
Goal ex = ex0. done. Abort.

Definition ex2 := hclose (λ: f, htv f).
Eval cbv in ex2.
Goal ex2 = vabs (tv DBNotation.x0). done. Qed.
Definition ex3 := hclose (λ:: f x, htapp (htv f) (htv x)).
Eval cbv in ex3.
Goal ex3 = tv (vabs (tv (vabs (tapp (tv DBNotation.x1) (tv DBNotation.x0))))). done. Abort.
End hoasTests.
