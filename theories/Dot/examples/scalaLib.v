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
  val "loop" = hpv (λ: w, self @: "loop" $: w)
  (* λ w, self.loop w. *)
}.
Definition hloopDefT : hty := val "loop" : ⊤ →: ⊥.
Definition hloopDefTConcr : hty := μ: _, {@ hloopDefT }.
Example loopDefTyp Γ : Γ u⊢ₜ hclose (htv hloopDefV) : hclose hloopDefT.
Proof.
  apply (iT_Sub_nocoerce (hclose hloopDefTConcr)); mltcrush; cbv.
  eapply iT_All_E; last var.
  tcrush; varsub; lookup.
Qed.

Definition hloopFunTm : htm := htv hloopDefV @: "loop".
Example loopFunTyp Γ : Γ u⊢ₜ hclose hloopFunTm : hclose ⊤ →: ⊥.
Proof. have ? := loopDefTyp Γ; tcrush. Qed.

Definition hloopTm : htm := hloopFunTm $: htv (hvnat 0).
Example loopTyp Γ : Γ u⊢ₜ hclose hloopTm : ⊥.
Proof.
  have ? := loopFunTyp Γ; apply (iT_All_E (T1 := ⊤)), (iT_Sub_nocoerce 𝐍);
    tcrush.
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
    val "true" = pv iftTrue;
    val "false" = pv iftFalse
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
Proof. eapply iSub_Sel''; tcrush. varsub; tcrush. Qed.

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
  ettrans; first (apply (iSub_AddI _ _ 1); tcrush).
  eapply iSub_Sel''; tcrush.
  varsub; tcrush.
Qed.

Example boolImplTypConcr Γ :
  Γ u⊢ₜ tv boolImplV : boolImplTConcr.
Proof. tcrush; by [apply (iD_Typ_Abs IFT); tcrush | var]. Qed.

Example boolImplTyp Γ :
  Γ u⊢ₜ tv boolImplV : boolImplT.
Proof.
  apply (iT_Sub_nocoerce boolImplTConcr); first by apply boolImplTypConcr.
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
  eapply (iT_Path (p := pv _)), iP_Sngl_Refl.
  typconstructor; var.
Qed.

Example iftFalseSingTyp Γ : Γ u⊢ₜ tv iftFalse : hclose hIFTFalseT.
Proof.
  tcrush; cbv.
  eapply (iT_Path (p := pv _)), iP_Sngl_Refl.
  typconstructor; var.
Qed.

Lemma hIFTTrueTSub Γ : Γ u⊢ₜ hclose hIFTTrueT, 0 <: hclose hIFT, 0.
Proof. tcrush; varsub; tcrush. Qed.

Lemma hIFTFalseTSub Γ : Γ u⊢ₜ hclose hIFTFalseT, 0 <: hclose hIFT, 0.
Proof. tcrush; varsub; tcrush. Qed.

Import DBNotation.

Module AssertPlain.
Definition assertBody e : tm :=
  tskip (tyApp e "A" (⊤ →: ⊤) $: tv x1 $: tv x0).

Import hoasNotation.

Definition hassertFun e :=
  hlett: hsucc := htv (λ: x, htv x) in:
  hlett: hfail := hloopFunTm in:
  pureS (assertBody e).

Definition hassert e :=
  hassertFun e $: htv (hvnat 0).

Lemma hassertBodyTyp Γ e T :
  T :: Γ u⊢ₜ e : hclose hIFT →
  T :: Γ u⊢ₜ tv x0 : ⊤ →: ⊤ →
  T :: Γ u⊢ₜ tv x1 : ⊤ →: ⊤ →
  T :: Γ u⊢ₜ assertBody e : ⊤ →: ⊤.
Proof.
  rewrite /assertBody => /= He Hx0 Hx1.
  have Hty: T :: Γ u⊢ₜ tyApp e "A" (⊤ →: ⊤) :
    hclose (⊤ →: ⊤) →: (⊤ →: ⊤) →: ▶: (⊤ →: ⊤).
  by eapply tyApp_typed; first apply He; intros; simpl; tcrush;
    [eapply iSub_Sel', (path_tp_delay (i := 0))..|
    eapply iSel_Sub, (path_tp_delay (i := 0))];
    try (typconstructor; var); wtcrush.
  move: Hty => /iT_All_Ex /(_ Hx1 _) /iT_All_Ex /(_ Hx0) /= Hty.
  eapply (iT_Sub (i := 1)), Hty; tcrush.
Qed.

Lemma hassertFunTyp Γ e
  (Hty : ((⊤ →: ⊤) :: (⊤ →: ⊤) :: Γ)%ty u⊢ₜ e : hclose hIFT) :
  Γ u⊢ₜ hclose (hassertFun e) : ⊤ →: ⊤.
Proof.
  apply iT_Let with (T := (⊤ →: ⊤)%ty); tcrush; first var.
  apply iT_Let with (T := (⊤ →: ⊤)%ty); stcrush.
  by eapply iT_Sub_nocoerce; first apply loopFunTyp; tcrush.
  by apply hassertBodyTyp; tcrush; var.
Qed.

Lemma hassertTyp Γ e
  (Ht : ((⊤ →: ⊤) :: (⊤ →: ⊤) :: Γ)%ty u⊢ₜ e : hclose hIFT):
  Γ u⊢ₜ hclose (hassert e) : ⊤.
Proof.
  eapply iT_All_E, iT_Sub_nocoerce; first exact: hassertFunTyp; tcrush.
Qed.
End AssertPlain.

Module AssertSingletons.

Definition assertBody e : tm :=
  tyApp e "A" ⊤ $: tv x1 $: tv x0.

Import hoasNotation.
Definition hassertFun e :=
  hlett: hsucc := htv (λ: x, htv x) in:
  hlett: hfail := hloopFunTm in:
  pureS (assertBody e).

Definition hassert e :=
  hassertFun e $: htv (hvnat 0).

Lemma hassertBodyFalseTyp Γ e T :
  T :: Γ u⊢ₜ e : hclose hIFTFalseT →
  T :: Γ u⊢ₜ tv x0 : ⊤ →
  T :: Γ u⊢ₜ tv x1 : ⊤ →
  T :: Γ u⊢ₜ assertBody e : TSing (pv x0).
Proof.
  move => /= He Hx0 Hx1.
  have Hty: T :: Γ u⊢ₜ tyApp e "A" ⊤ :
    hclose (∀: t : ⊤, ∀: f: ⊤, hTSing (hpv f)).
  by eapply tyApp_typed; first apply He; intros; tcrush;
    eapply iSub_Sel', (path_tp_delay (i := 0));
    try (typconstructor; var); wtcrush.
  rewrite /assertBody.
  move: Hty => /iT_All_Ex /(_ Hx1 _) /iT_All_Ex /(_ Hx0) /=.
  apply; tcrush.
Qed.

Lemma hassertBodyTrueTyp Γ e T U :
  T :: U :: Γ u⊢ₜ e : hclose hIFTTrueT →
  T :: U :: Γ u⊢ₜ tv x1 : ⊤ →
  T :: U :: Γ u⊢ₜ tv x0 : ⊤ →
  T :: U :: Γ u⊢ₜ assertBody e : TSing (pv x1).
Proof.
  move => /= He Hx1 Hx0.
  have Hty: T :: U :: Γ u⊢ₜ tyApp e "A" ⊤ :
    hclose (∀: t : ⊤, ∀: f: ⊤, hTSing (hpv t)).
  by eapply tyApp_typed; first apply He; intros; tcrush;
    eapply iSub_Sel', (path_tp_delay (i := 0));
    try (typconstructor; var); wtcrush.
  rewrite /assertBody.
  move: Hty => /iT_All_Ex /(_ Hx1 _) /iT_All_Ex /(_ Hx0) /=.
  apply; tcrush.
Qed.

Lemma hassertFunTrueTyp Γ e :
  (⊤ :: ⊤ :: Γ)%ty u⊢ₜ e : hclose hIFTTrueT →
  Γ u⊢ₜ hclose (hassertFun e) : ⊤.
Proof.
  move => /hassertBodyTrueTyp He.
  apply iT_Let with (T := ⊤%ty); stcrush. {
    apply (iT_Sub_nocoerce (⊤ →: ⊤)); tcrush; var.
  }
  apply iT_Let with (T := ⊤%ty); stcrush. {
    eapply iT_Sub_nocoerce; first apply loopFunTyp; tcrush.
  }
  eapply iT_Sub_nocoerce; first apply He; tcrush; var.
Qed.

Lemma hassertFunFalseTyp Γ e :
  (⊤ :: ⊤ :: Γ)%ty u⊢ₜ e : hclose hIFTFalseT →
  Γ u⊢ₜ hclose (hassertFun e) : ⊤.
Proof.
  move => /hassertBodyFalseTyp He.
  apply iT_Let with (T := ⊤%ty); stcrush. {
    apply (iT_Sub_nocoerce (⊤ →: ⊤)); tcrush; var.
  }
  apply iT_Let with (T := ⊤%ty); stcrush. {
    eapply iT_Sub_nocoerce; first apply loopFunTyp; tcrush.
  }
  eapply iT_Sub_nocoerce; first apply He; tcrush; var.
Qed.
End AssertSingletons.

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

(*
  type None = Option { type T = Nothing }
  val noneV: None = new {
    type T = Nothing
    val isEmpty = true
    val pmatch: [U] => U => (Nothing => U) => U = [U] => (none: U) => (some: T => U) => none
  }
*)
Definition hnoneSingTBody self : hty := {@
  typeEq "T" ⊥;
  val "isEmpty" : hIFTTrueT;
  val "pmatch" : hpmatchT self
}.
Definition hnoneSingT := μ: self, hnoneSingTBody self.

Definition hnoneV := ν: _, {@
  type "T" = ⊥;
  val "isEmpty" = hpv hiftTrue;
  val "pmatch" = hpv (λ: x, λ:: none some, htv none)
}.
Definition noneV := hclose hnoneV.

Example noneTypStronger Γ :
  Γ u⊢ₜ tv noneV : hclose hnoneSingT.
Proof.
  have := iftTrueSingTyp (hclose (▶: hnoneSingTBody hx0) :: Γ) =>
    /(iD_Val "isEmpty") ?.
  (* apply iT_Obj_I; last stcrush.
  apply iD_Cons; [tcrush| |tcrush].
  apply iD_Cons; [eauto | |tcrush]. *)
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

Definition hsomeSingT hL hU : hty := μ: self, {@
  type "T" >: hL <: hU;
  val "isEmpty" : hIFTFalseT;
  val "pmatch" : hpmatchT self;
  val "get" : ▶: hpv self @; "T"
}.

Definition hmkSomeTGen res : hty := ∀: x: tparam "A", (hpv x @; "A" →: res (hpv x @; "A") (hpv x @; "A")).

Definition hmkSomeTSing : hty := hmkSomeTGen hsomeSingT.

Definition hmkSome : hvl := λ: x, λ:: content, htv $ ν: self, {@
  type "T" = hpv x @; "A";
  val "isEmpty" = hpv hiftFalse;
  val "pmatch" = hpv (λ: x, λ:: none some, htv some $: htskip (htv self @: "get"));
  val "get" = hpv content
}.
Definition mkSome := hclose hmkSome.

Example mkSomeTypStronger Γ :
  Γ u⊢ₜ tv mkSome : hclose hmkSomeTSing.
Proof.
  evar (Γ' : ctx).
  have := iftFalseSingTyp Γ' => /(iD_Val "isEmpty"); rewrite /Γ' => Hf.
  tcrush; cbv.
  - eapply iT_All_E; first var.
    apply (iT_Sub (i := 1) (T1 := hclose (▶: (hp3 @; "T"))%HT)); tcrush.
    varsub; ltcrush.
  - varsub.
    ettrans; first (apply iSub_Add_Later; tcrush).
    asideLaters.
    eapply iSub_Sel''; tcrush.
    varsub; tcrush.
Qed.

Definition hoptionTSing := hTOr hnoneSingT (hsomeSingT ⊥ ⊤).

Definition hoptionModTConcrBody : hty := {@
  typeEq "Option" hoptionTSing;
  val "none" : hnoneSingT;
  val "mkSome" : hmkSomeTSing
}.

Definition hoptionModV := ν: self, {@
  type "Option" = hoptionTSing;
  val "none" = hpv hnoneV;
  val "mkSome" = hpv hmkSome
}.

(** Rather precise type for [hoptionModV]. *)
Example optionModConcrTyp Γ :
  Γ u⊢ₜ hclose (htv hoptionModV) : hclose (μ: _, hoptionModTConcrBody).
Proof.
  set U := hclose (▶: hoptionModTConcrBody).
  have := noneTypStronger (U :: Γ).
  have := mkSomeTypStronger (U :: Γ) => /(iD_Val "mkSome") Hs Hn.
  ltcrush.
Qed.

(** Define interface for [hoptionModV]. To rewrite to have abstraction. *)

Definition hoptionT := hoptionTGen ⊥ ⊤.
Definition optionT := hclose hoptionT.

Definition hnoneT self := hTAnd (hpv self @; "Option") {@ typeEq "T" ⊥}.

(** Behold here [(optionT & (μ self, val get: ▶: self @; "T")) & { type T = hT } ]. *)
Definition hsomeT self hL hU : hty :=
  hTAnd (hTAnd (hpv self @; "Option") (μ: self, val "get" : ▶: hpv self @; "T"))
    (type "T" >: hL <: hU).
Definition hmkSomeT self : hty := hmkSomeTGen (hsomeT self).

Definition hoptionModTInvBody self : hty := {@
  type "Option" >: ⊥ <: hoptionTSing;
  val "none" : hnoneT self;
  val "mkSome" : hmkSomeT self
}.

Example optionModInvTyp Γ :
  Γ u⊢ₜ hclose (htv hoptionModV) : hclose (μ: self, hoptionModTInvBody self).
Proof.
  eapply iT_Sub_nocoerce; first apply optionModConcrTyp.
  ltcrush; rewrite iterate_0.
  eapply iSub_Sel'; tcrush; varsub; ltcrush.
  all: try eapply iSub_Sel', (path_tp_delay (i := 0));
    try (typconstructor; varsub; ltcrush); wtcrush.
  all: try (ettrans; last eapply iSub_Or2); mltcrush.
Qed.

Definition hoptionModT := μ: self, {@
  type "Option" >: ⊥ <: hoptionT;
  val "none" : hnoneT self;
  val "mkSome" : hmkSomeT self
}.

Ltac prepare_lemma L H :=
  let Γ' := fresh "Γ" in
  evar (Γ' : ctx); have := L Γ'; rewrite {}/Γ' => H.

Example optionModTypSub Γ :
  Γ u⊢ₜ hclose (μ: self, hoptionModTInvBody self), 0 <: hclose hoptionModT, 0.
Proof. ltcrush; varsub; tcrush. Qed.

Example optionModTyp Γ :
  Γ u⊢ₜ hclose (htv hoptionModV) : hclose hoptionModT.
Proof. eapply iT_Sub_nocoerce, optionModTypSub; apply optionModInvTyp. Qed.

End option.
