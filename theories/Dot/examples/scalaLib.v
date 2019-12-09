From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra unstampedness_binding hoas.
From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived.
Import DBNotation.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Module Export loop.
Import hoasNotation.
(** * Infinite loops *)
Definition hloopDefV : hvl := ν: self, {@
  val "loop" = λ: v, htv self @: "loop" $: htv v
  (* λ v, self.loop v. *)
}.
Definition hloopDefT : hty := val "loop" : ⊤ →: ⊥.
Definition hloopDefTConcr : hty := μ: _, {@ hloopDefT }.
Example loopDefTyp Γ : Γ u⊢ₜ hclose (htv hloopDefV) : hclose hloopDefT.
Proof.
  apply (Subs_typed_nocoerce (hclose hloopDefTConcr)).
  - tcrush; cbv.
    eapply App_typed; last var. tcrush.
    varsub; cbv. lThis.
  - apply Bind1; tcrush.
Qed.

Definition hloopTm : htm := htv hloopDefV @: "loop" $: htv (hvnat 0).
Example loopTyp Γ : Γ u⊢ₜ hclose hloopTm : ⊥.
Proof.
  pose proof loopDefTyp Γ.
  apply (App_typed (T1 := ⊤)); tcrush.
  apply (Subs_typed_nocoerce 𝐍); tcrush.
Qed.
End loop.

(** * Booleans, Church-encoded. *)
(** Sec. 5 of WadlerFest DOT.
IFTFun ≡ { if: ∀(x: {A: ⊥..⊤})∀(t: x.A)∀(f: x.A): x.A }
IFT ≡ { if: IFTFun }

let boolImpl =
ν (b: { Boolean: IFT..IFT } ∧ { true: IFT } ∧ { false: IFT })
{ Boolean = IFT } ∧
{ true = λ(x: {A: ⊥..⊤})λ(t: x.A)λ(f: x.A)t } ∧ { false = λ(x: {A: ⊥..⊤})λ(t: x.A)λ(f: x.A)f }

In fact, that code doesn't typecheck as given, and we fix it by setting.

IFT ≡ IFTFun
let bool = boolImpl : μ { Boolean: IFT..IFT; true : b.Boolean; false : b.Boolean }
 *)
Module Export hBool.
Import hoasNotation.
Definition hIFTBody x : hty := hpv x @; "A" →: hpv x @; "A" →: hpv x @; "A".
Definition IFTBody := hclose $ hIFTBody hx0.
Definition hIFT : hty :=
  ∀: x : tparam "A", hIFTBody x.
Definition IFT := hclose hIFT.

(* Definition hIFT : hty := {@ val "if" : hIFTFun }. *)

Definition hiftTrue : hvl := λ: x, λ:: t f, htv t.
Definition hiftFalse : hvl := λ: x, λ:: t f, htv f.
Definition iftTrue := hclose hiftTrue.
Definition iftFalse := hclose hiftFalse.
End hBool.

Example iftTrueTyp Γ : Γ u⊢ₜ tv iftTrue : IFT.
Proof. tcrush. var. Qed.
Example iftFalseTyp Γ : Γ u⊢ₜ tv iftFalse : IFT.
Proof. tcrush. var. Qed.

Definition boolImpl :=
  ν {@
    type "Boolean" = IFT;
    val "true" = iftTrue;
    val "false" = iftFalse
  }.

Definition boolImplTConcr : ty :=
  μ {@
    typeEq "Boolean" IFT;
    val "true" : IFT;
    val "false" : IFT
  }.

Definition p0Bool := p0 @; "Boolean".

(* This type makes "Boolean" nominal by abstracting it. *)
Definition boolImplT : ty :=
  μ {@
    type "Boolean" >: ⊥ <: IFT;
    val "true" : TLater p0Bool;
    val "false" : TLater p0Bool
  }.

Example SubIFT_P0Bool Γ : {@
    typeEq "Boolean" IFT;
    val "true" : IFT;
    val "false" : IFT
  }%ty :: Γ u⊢ₜ IFT, 0 <: p0Bool, 0.
Proof. eapply LSel_stp'; tcrush. varsub; tcrush. Qed.

Example SubIFT_LaterP0Bool' Γ : {@
    typeEq "Boolean" IFT;
    val "true" : IFT;
    val "false" : IFT
  }%ty :: Γ u⊢ₜ IFT, 0 <: ▶ p0Bool, 0.
Proof. ettrans; first exact: SubIFT_P0Bool. tcrush. Qed.

Example SubIFT_LaterP0Bool Γ : (▶ {@
    typeEq "Boolean" IFT;
    val "true" : ▶ p0Bool;
    val "false" : ▶ p0Bool
  })%ty :: Γ u⊢ₜ IFT, 0 <: ▶ p0Bool, 0.
Proof.
  asideLaters.
  ettrans; first (apply (AddI_stp _ _ 1); tcrush).
  eapply LSel_stp'; tcrush.
  varsub; tcrush.
Qed.

Example boolImplTypConcr Γ :
  Γ u⊢ₜ tv boolImpl : boolImplTConcr.
Proof. tcrush; by [apply (dty_typed IFT); tcrush | var]. Qed.

Example boolImplTyp Γ :
  Γ u⊢ₜ tv boolImpl : boolImplT.
Proof.
  apply (Subs_typed_nocoerce boolImplTConcr); first by apply boolImplTypConcr.
  tcrush; rewrite iterate_0.
  - lThis.
  - lNext.
    lThis.
    apply SubIFT_LaterP0Bool'.
  - do 2 lNext.
    lThis.
    apply SubIFT_LaterP0Bool'.
Qed.

(*
  Encoding Option. Beware I'm using raw Church-encoded booleans, simply
    because it's easier.
  type Option = {
    type T
    val isEmpty: Boolean
    val pmatch: [U] => U => (T => U) => U
  }
*)

Definition optionT : ty := μ {@ (* self => *)
  tparam "T";
  val "isEmpty" : IFT;
  val "pmatch" : TAll (tparam "U") (p0 @; "U" →: (p1 @; "T" →: p0 @; "U") →: p0 @; "U")
  (* ∀ x : {type U}, x.U → (self.T -> x.U) -> x.U *)
}.
(*
  type None = Option { type T = Nothing }
  def mkNone[T]: None = new {
    type T = Nothing
    val isEmpty = true
    val pmatch: [U] => U => (T => U) => U = [U] => (none: U) => (some: T => U) => none
  }
*)
Definition noneT0 := TAnd optionT ({@ typeEq "T" ⊥}).
Definition noneT : ty := μ {@ (* self => *)
  typeEq "T" ⊥;
  val "isEmpty" : IFT;
  val "pmatch" : TAll (tparam "U") (p0 @; "U" →: (p1 @; "T" →: p0 @; "U") →: p0 @; "U")
}.
Definition mkNone : vl := ν {@
  type "T" = ⊥;
  val "isEmpty" = iftTrue;
  val "pmatch" = vabs (vabs' (vabs' (tv x1)))
}.

Example noneTyp Γ :
  Γ u⊢ₜ tv mkNone : noneT.
Proof.
  (* apply VObj_typed; last stcrush.
  apply dcons_typed; [tcrush| |tcrush].
  apply dcons_typed; [eauto using iftTrueTyp| |tcrush]. *)
  tcrush; var.
Qed.

(*
  //type Some = Option & { self => val get: self.T }
  type Some = Option & { type T; val get: T }
  def mkSome[S](t: S): Some { type T = S } = new {
    type T = S
    val isEmpty = false
    val get = t
    val pmatch: [U] => U => (T => U) => U = [U] => (none: U) => (some: T => U) => some(get)
  }
*)

Definition someT T : ty := μ {@ (* self => *)
  typeEq "T" (shift T);
  val "isEmpty" : IFT;
  val "pmatch" : TAll (tparam "U") (p0 @; "U" →: (p1 @; "T" →: p0 @; "U") →: p0 @; "U");
  val "get" : ▶ p0 @; "T"
}.
Definition mkSomeT : ty := TAll (tparam "A") (p0 @; "A" →: someT (p0 @; "A")).
Definition mkSome : tm := vabs' $ vabs' $ tv $ ν {@
  type "T" = p2 @; "A";
  val "isEmpty" = iftFalse;
  val "pmatch" = vabs (vabs' (vabs' (tapp (tv x0) (tskip (tproj (tv x3) "get")))));
  val "get" = x1
}.

Example mkSomeTyp Γ :
  Γ u⊢ₜ mkSome : mkSomeT.
Proof.
  tcrush; first var; cbv; hideCtx.
  - eapply App_typed; first var.
    rewrite -(iterate_S tskip 0);
      apply (Subs_typed (T1 := (▶ (p3 @; "T"))%ty)); tcrush.
    varsub.
    repeat lNext.
  - varsub.
    ettrans; first (apply TAddLater_stp; tcrush).
    asideLaters.
    eapply LSel_stp'; tcrush.
    varsub; tcrush.
Qed.
