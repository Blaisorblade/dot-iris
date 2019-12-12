From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra hoas.
From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived.
Import DBNotation.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Notation HashableString := (μ {@ val "hashCode" : TUnit →: TNat }).

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
  apply (Subs_typed_nocoerce (hclose hloopDefTConcr)); mltcrush; cbv.
  eapply App_typed; last var.
  tcrush; varsub; lookup.
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

let boolImplV =
ν (b: { Boolean: IFT..IFT } ∧ { true: IFT } ∧ { false: IFT })
{ Boolean = IFT } ∧
{ true = λ(x: {A: ⊥..⊤})λ(t: x.A)λ(f: x.A)t } ∧ { false = λ(x: {A: ⊥..⊤})λ(t: x.A)λ(f: x.A)f }

In fact, that code doesn't typecheck as given, and we fix it by setting.

IFT ≡ IFTFun
let bool = boolImplV : μ { Boolean: IFT..IFT; true : b.Boolean; false : b.Boolean }
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

Definition boolImplV :=
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
  }%ty :: Γ u⊢ₜ IFT, 0 <: ▶: p0Bool, 0.
Proof. ettrans; first exact: SubIFT_P0Bool. tcrush. Qed.

Example SubIFT_LaterP0Bool Γ : (▶: {@
    typeEq "Boolean" IFT;
    val "true" : ▶: p0Bool;
    val "false" : ▶: p0Bool
  })%ty :: Γ u⊢ₜ IFT, 0 <: ▶: p0Bool, 0.
Proof.
  asideLaters.
  ettrans; first (apply (AddI_stp _ _ 1); tcrush).
  eapply LSel_stp'; tcrush.
  varsub; tcrush.
Qed.

Example boolImplTypConcr Γ :
  Γ u⊢ₜ tv boolImplV : boolImplTConcr.
Proof. tcrush; by [apply (dty_typed IFT); tcrush | var]. Qed.

Example boolImplTyp Γ :
  Γ u⊢ₜ tv boolImplV : boolImplT.
Proof.
  apply (Subs_typed_nocoerce boolImplTConcr); first by apply boolImplTypConcr.
  tcrush; rewrite iterate_0; ltcrush; apply SubIFT_LaterP0Bool'.
Qed.

Module Export hBoolSing.
Import hoasNotation.
Definition hIFTGenT hres : hty :=
  ∀: x : tparam "A", ∀: t : hpv x @; "A", ∀: f: hpv x @; "A", hres t f.

Definition hIFTFalseT : hty := hIFTGenT (λ t f, hTSing (hpv f)).
Definition hIFTTrueT : hty := hIFTGenT (λ t f, hTSing (hpv t)).

Example iftTrueSingTyp Γ : Γ u⊢ₜ tv iftTrue : hclose hIFTTrueT.
Proof.
  tcrush; cbv.
  eapply (Path_typed (p := pv _)), psingleton_refl_typed.
  typconstructor; var.
Qed.

Example iftFalseSingTyp Γ : Γ u⊢ₜ tv iftFalse : hclose hIFTFalseT.
Proof.
  tcrush; cbv.
  eapply (Path_typed (p := pv _)), psingleton_refl_typed.
  typconstructor; var.
Qed.

Lemma hIFTTrueTSub Γ : Γ u⊢ₜ hclose hIFTTrueT, 0 <: hclose hIFT, 0.
Proof. tcrush; varsub; tcrush. Qed.

Lemma hIFTFalseTSub Γ : Γ u⊢ₜ hclose hIFTFalseT, 0 <: hclose hIFT, 0.
Proof. tcrush; varsub; tcrush. Qed.

End hBoolSing.

Module Export option.
(*
  Encoding Option. Beware I'm using raw Church-encoded booleans, simply
    because it's easier.
  However, we do export Option as an abstract type.
  type Option = {
    type T
    val isEmpty: Boolean
    val pmatch: [U] => U => (T => U) => U
  }
*)

Import hoasNotation.

(* ∀ x : {type U}, x.U → (self.T -> x.U) -> x.U *)
Definition hpmatchT self := ∀: x : tparam "U", hpv x @; "U" →: (hpv self @; "T" →: hpv x @; "U") →: hpv x @; "U".
Definition hoptionTGen (L U : hty) := μ: self, {@
  type "T" >: L <: U;
  val "isEmpty" : hIFT;
  val "pmatch" : hpmatchT self
}.

Definition hoptionT := hoptionTGen ⊥ ⊤.
Definition optionT := hclose hoptionT.

(*
  type None = Option { type T = Nothing }
  val noneV: None = new {
    type T = Nothing
    val isEmpty = true
    val pmatch: [U] => U => (Nothing => U) => U = [U] => (none: U) => (some: T => U) => none
  }
*)
Definition hnoneT := hTAnd hoptionT {@ typeEq "T" ⊥}.
Definition hnoneTConcr := hoptionTGen ⊥ ⊥.
Definition noneT := hclose hnoneT.

Definition hnoneSingTBody self : hty := {@
  typeEq "T" ⊥;
  val "isEmpty" : hIFTTrueT;
  val "pmatch" : hpmatchT self
}.
Definition hnoneSingT := μ: self, hnoneSingTBody self.

Definition hnoneV := ν: _, {@
  type "T" = ⊥;
  val "isEmpty" = hiftTrue;
  val "pmatch" = λ: x, λ:: none some, htv none
}.
Definition noneV := hclose hnoneV.

Example noneTypStronger Γ :
  Γ u⊢ₜ tv noneV : hclose hnoneSingT.
Proof.
  have := iftTrueSingTyp (hclose (▶: hnoneSingTBody hx0) :: Γ) => /(dvl_typed "isEmpty") ?.
  (* apply VObj_typed; last stcrush.
  apply dcons_typed; [tcrush| |tcrush].
  apply dcons_typed; [eauto | |tcrush]. *)
  tcrush; var.
Qed.

Example hnoneSingTConcrSub Γ :
  Γ u⊢ₜ hclose hnoneSingT, 0 <: hclose hnoneTConcr, 0.
Proof.
  have ? := hIFTTrueTSub (hclose (hnoneSingTBody hx0) :: Γ).
  mltcrush.
Qed.

Example hnoneConcrTSub Γ :
  Γ u⊢ₜ hclose hnoneTConcr, 0 <: noneT, 0.
Proof. mltcrush. Qed.

Example hnoneSingTSub Γ :
  Γ u⊢ₜ hclose hnoneSingT, 0 <: noneT, 0.
Proof. ettrans; [apply hnoneSingTConcrSub | apply hnoneConcrTSub]. Qed.

Example noneTyp Γ :
  Γ u⊢ₜ tv noneV : noneT.
Proof.
  apply (Subs_typed_nocoerce (hclose hnoneSingT)), hnoneSingTSub.
  apply noneTypStronger.
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

Definition hsomeSingT hL hU : hty := μ: self, {@
  type "T" >: hL <: hU;
  val "isEmpty" : hIFTFalseT;
  val "pmatch" : hpmatchT self;
  val "get" : ▶: hpv self @; "T"
}.

Definition hsomeTConcr hL hU : hty := μ: self, {@
  type "T" >: hL <: hU;
  val "isEmpty" : hIFT;
  val "pmatch" : hpmatchT self;
  val "get" : ▶: hpv self @; "T"
}.

(** Behold here [(optionT & (μ self, val get: ▶: self @; "T")) & { type T = hT } ]. *)
Definition hsomeT hL hU : hty :=
  hTAnd (hTAnd hoptionT (μ: self, val "get" : ▶: hpv self @; "T"))
    (type "T" >: hL <: hU).

Definition hmkSomeTGen res : hty := ∀: x: tparam "A", (hpv x @; "A" →: res (hpv x @; "A") (hpv x @; "A")).
Definition hmkSomeTSing : hty := hmkSomeTGen hsomeSingT.
Definition hmkSomeTConcr : hty := hmkSomeTGen hsomeTConcr.
Definition hmkSomeT : hty := hmkSomeTGen hsomeT.

Definition hmkSome : hvl := λ: x, λ:: content, htv $ ν: self, {@
  type "T" = hpv x @; "A";
  val "isEmpty" = hiftFalse;
  val "pmatch" = λ: x, λ:: none some, htv some $: htskip (htv self @: "get");
  val "get" = content
}.
Definition mkSomeT := hclose hmkSomeT.
Definition mkSome := hclose hmkSome.

Example mkSomeTypStronger Γ :
  Γ u⊢ₜ tv mkSome : hclose hmkSomeTSing.
Proof.
  evar (Γ' : ctx).
  have := iftFalseSingTyp Γ' => /(dvl_typed "isEmpty"); rewrite /Γ' => Hf.
  tcrush; cbv.
  - eapply App_typed; first var.
    apply (Subs_typed (i := 1) (T1 := hclose (▶: (hp3 @; "T"))%HT)); tcrush.
    varsub; ltcrush.
  - varsub.
    ettrans; first (apply TAddLater_stp; tcrush).
    asideLaters.
    eapply LSel_stp'; tcrush.
    varsub; tcrush.
Qed.

Example hmkSomeSingTConcrSub Γ :
  Γ u⊢ₜ hclose hmkSomeTSing, 0 <: hclose hmkSomeTConcr, 0.
Proof.
  evar (Γ' : ctx); have := hIFTFalseTSub Γ'; rewrite /Γ' => Hf.
  tcrush; lNext; ltcrush.
Qed.

(** This involves multiple fixpoints on both sides, but goes through
without much effort. *)
Example hmkSomeConcrTSub Γ :
  Γ u⊢ₜ hclose hmkSomeTConcr, 0 <: mkSomeT, 0.
Proof. mltcrush. Qed.
Example hmkSomeSingTSub Γ :
  Γ u⊢ₜ hclose hmkSomeTSing, 0 <: mkSomeT, 0.
Proof. ettrans; [apply hmkSomeSingTConcrSub | apply hmkSomeConcrTSub]. Qed.

Example mkSomeTyp Γ :
  Γ u⊢ₜ tv mkSome : mkSomeT.
Proof.
  eapply Subs_typed_nocoerce, hmkSomeSingTSub.
  apply mkSomeTypStronger.
Qed.
Definition hoptionModV := ν: self, {@
  type "Option" = hoptionT;
  val "none" = hnoneV;
  val "mkSome" = hmkSome
}.

Definition hoptionModTConcrBody : hty := {@
  typeEq "Option" hoptionT;
  val "none" : hnoneT;
  val "mkSome" : hmkSomeT
}.

Definition hoptionModT := μ: self, {@
  type "Option" >: ⊥ <: hoptionT;
  val "none" : hnoneT;
  val "mkSome" : hmkSomeT
}.

Example optionModTyp Γ :
  Γ u⊢ₜ hclose (htv hoptionModV) : hclose hoptionModT.
Proof.
  set U := hclose (▶: hoptionModTConcrBody).
  have Hn := noneTyp (U :: Γ).
  (* Without the call to [dvl_typed], Coq would (smartly) default to [dvabs_typed] *)
  have := mkSomeTyp (U :: Γ) => /(dvl_typed "mkSome") Hs.
  apply (Subs_typed_nocoerce (hclose (μ: _, hoptionModTConcrBody))); mltcrush.
Qed.

End option.
