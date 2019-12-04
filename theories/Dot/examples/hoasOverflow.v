From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra.
From D.Dot Require Import examples.hoas.

Module Import try1.
(* Inspired by my HOAS frontend
encoding of HOAS in ilc-agda
*)

Definition ReaderS t := env → t.
Definition runReaderS {T}: ReaderS T → T := (.$ ids).
Definition pureS {T} : T → ReaderS T := const.

(* Using [return _] breaks type inference. *)
Unset Program Cases.

Fixpoint foldN R n : Type :=
  match n with
  | 0 => R
  | S n => vl → foldN R n
  end.
Definition bind2 {T} : (vl → ReaderS T) → ReaderS T :=
  λ bodyF s, bodyF (s 0) (s >> ren (+1)).
(* Nope. I think we're using "There and back again", so we need CPS. *)
Definition hTMu hT : ReaderS ty := TMu ∘ bind2 hT.
Definition hTAll S hT : ReaderS ty := TAll S ∘ bind2 hT.
Definition hvabs' bodyF : ReaderS tm := vabs' ∘ bind2 bodyF.

Definition bind {T} : ReaderS (vl → T) → ReaderS T :=
  λ bodyF s, bodyF (s >> ren (+1)) (s 0).

Program Fixpoint vabs'NGo n {struct n}: (ReaderS $ foldN tm n) → (ReaderS tm) :=
  (* match n as n0 return (ReaderS $ foldN tm n0) → (ReaderS tm) with *)
  match n with
  | 0 => λ body, body
  | S n' => λ bodyF s, vabs' ∘ vabs'NGo n' (bind bodyF) $ s
  (* λ bodyF s, vabs' ∘ vabs'NGo n' (bind bodyF) $ s *)
  end.
Definition vabs'N n (body : foldN tm n): tm := runReaderS $ vabs'NGo n (pureS body).

Module tests.
(* Apply := λ f x, f x. *)
Definition applyHoas := vabs'N 2 (λ x y, tapp (tv x) (tv y)).
Definition apply := vabs' (vabs' (tapp (tv x1) (tv x0))).

Goal applyHoas = apply. done. Qed.
Eval cbv in applyHoas.

(* Compose := λ f g x, f (g x). *)
Definition composeHoas := vabs'N 3 (λ f g x, tapp (tv f) (tapp (tv g) (tv x))).
Definition compose := vabs' (vabs' (vabs' (tapp (tv x2) (tapp (tv x1) (tv x0))))).
Goal composeHoas = compose. done. Qed.
Eval cbv in composeHoas.

(* ∀ x, μ y, x.type ∧ x.type *)
Definition ex := runReaderS $ hTAll TNat (λ x, hTMu (λ y, pureS $ TAnd (TSing (pv x)) (TSing (pv y)))).
Eval cbv in ex.
Goal True.
evar (T: Type).
have: T.
About hTAll.
About hTMu.
refine (hTAll TNat (λ x, hTMu (λ y, pureS $ TAnd (TSing (pv x)) (TSing (pv y))))).
done.
Qed.


End tests.
End try1.

(*
  Print ren.
  About ren.
  Eval cbv -[plus] in ren.
  Eval cbv [ren funcomp ids ids_vl] in @ren vl _.

  Eval cbv -[plus minus] in (λ i', ren (λ j, j - i') : hvl).
  Eval cbv -[plus minus] in (λ i', λ j, var_vl (j - i')). *)

Goal True.
let f := constr:(vabs'NGo 1) in let x := type of f in let y := eval cbv in x in idtac y.
Abort.

Definition liftBind {T} (con : T → T) : ReaderS (vl → T) → ReaderS T :=
  λ bodyF s, con (bodyF (s >> ren (+1)) (s 0)).
Goal ∀ {T} (bodyF : ReaderS (vl → T)), liftBind id bodyF = (λ s, bodyF (s >> ren (+1)) (s 0)). reflexivity. Qed.

Definition foldNA (R : Type) : nat → Type := nat_rect (λ _, Type) R (const $ λ r, vl → r).

Lemma foldNEquiv n R: foldN R n = foldNA R n.
Proof. by elim: n => [//|n /= ->]. Qed.

Fixpoint vabsNGo n {struct n}: (ReaderS $ foldN tm n) → tm :=
  match n with
  | 0 => λ body, body ids
  | S n' => λ bodyF, tv (vabs (vabsNGo n' (λ s, bodyF (s >> ren (+1)) (s 0))))
  end.

Definition vabsN n (body : foldN tm n): tm := vabsNGo n (λ _, body).
Eval cbn in λ n body, vabsNGo (1 + n) $ const body.
Eval cbv in vabsN 1.
Eval cbv in vabsN 2.

Module tests.
(* Apply := λ f x, f x. *)
Definition applyHoas := vabsN 2 (λ x y, tapp (tv x) (tv y)).
Definition apply := vabs' (vabs' (tapp (tv x1) (tv x0))).

Goal applyHoas = apply. done. Qed.
Eval cbv in applyHoas.

(* Compose := λ f g x, f (g x). *)
Definition composeHoas := vabsN 3 (λ f g x, tapp (tv f) (tapp (tv g) (tv x))).
Definition compose := vabs' (vabs' (vabs' (tapp (tv x2) (tapp (tv x1) (tv x0))))).
Goal composeHoas = compose. done. Qed.
Eval cbv in composeHoas.
End tests.

(* Definition foo : (vl → vl) → vl → vl := λ x y, x y.
Definition fooR0 y := vabsNS1 (λ s x, tapp (tv x) (tv y)).
Eval cbv in fooR0 x0.
Definition fooR1 (s : sub) y := vabsNS 1 (λ s x, tapp (tv x) (tv y)).
Eval cbv in fooR1 ids (ids 10).

Definition vabsN1 (body : vl → tm) : vl := vabs (body (ids 0)).
(* Program Definition fooR := vabsN1 (λ x, tapp (tv x) (tv (vnat 42))). *)

Definition vabsNS1 (body : sub → vl → tm) (s : sub): vl := vabs (body s (s 0)).

Fixpoint vabsN n : foldN n vl → vl :=
  match n as n0 return foldN n0 vl → vl with
  | 0 => λ body, body
  | S n' => λ bodyF, vabs (tv (vabsN n' (bodyF (ids 0))))
  end.
Eval cbv in vabsN 1.

Definition fooR y := shiftV (vabsN1 (λ x, tapp (tv x) (tv y))).

Program Fixpoint vabsN' n : (foldN n tm) → tm :=
  match n with
  | 0 => λ bodyF, bodyF
  | S n' => λ bodyF, vabsN' n' (bodyF (ids 0))
  (* _ vabs (vabsN' n' (bodyF (ids 0))) *)
  end.

Program Fixpoint vabsN' n : (vl → foldN n tm) → vl :=
  match n with
  | 0 => λ bodyF, vabs (bodyF (ids 0))
  | S n' => λ bodyF,
  _ (vabsN' n' (bodyF (ids 0)))
  (* _ vabs (vabsN' n' (bodyF (ids 0))) *)
  end. *)
