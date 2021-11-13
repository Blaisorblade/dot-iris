
From D Require Import tactics.
From D.Dot Require Import syn ex_utils hoas_ex_utils.
From D.Dot Require Import old_unstamped_typing old_unstamped_typing_derived_rules.
Import DBNotation.

Implicit Types (L T U : ty) (v : vl) (e : tm) (d : dm) (ds : dms) (Γ : list ty).

Notation HashableString := (μ {@ val "hashCode" : TUnit →: TInt }).

(** ** Infinite loops; typed using old unstamped typing. *)
Module Export loop.
Export loopTms.
Import hoasNotation.

Example loopDefTyp Γ : Γ u⊢ₜ hloopDefV : hloopDefT.
Proof.
  apply (iT_ISub_nocoerce hloopDefTConcr); mltcrush; cbv.
  eapply iT_All_E; last var.
  tcrush; varsub; lookup.
Qed.

Example loopFunTyp Γ : Γ u⊢ₜ hloopFunTm : ⊤ →: ⊥.
Proof. have ? := loopDefTyp Γ; tcrush. Qed.

Example loopTyp Γ : Γ u⊢ₜ hloopTm : ⊥.
Proof.
  have ? := loopFunTyp Γ; apply (iT_All_E (T1 := ⊤)), (iT_ISub_nocoerce 𝐙);
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
Definition hIFTBody x : hty := x @; "A" →: x @; "A" →: x @; "A".
Definition IFTBody : ty := hIFTBody hx0.
Definition hIFT : hty :=
  ∀: x : tparam "A", hIFTBody x.
Definition IFT : ty := hIFT.

Definition hiftTrue : hvl := λ: x t f, t.
Definition hiftFalse : hvl := λ: x t f, f.
End hBool.

Example iftTrueTyp Γ : Γ u⊢ₜ hiftTrue : hIFT.
Proof. tcrush. var. Qed.
Example iftFalseTyp Γ : Γ u⊢ₜ hiftFalse : hIFT.
Proof. tcrush. var. Qed.

Definition boolImplV :=
  ν {@
    type "Boolean" = hIFT;
    val "true" = hiftTrue;
    val "false" = hiftFalse
  }.

Definition boolImplTConcr : ty :=
  μ {@
    typeEq "Boolean" hIFT;
    val "true" : hIFT;
    val "false" : hIFT
  }.

Definition p0Bool := x0 @; "Boolean".

(* This type makes "Boolean" nominal by abstracting it. *)
Definition boolImplT : ty :=
  μ {@
    type "Boolean" >: ⊥ <: hIFT;
    val "true" : TLater p0Bool;
    val "false" : TLater p0Bool
  }.

Example SubIFT_P0Bool Γ : {@
    typeEq "Boolean" hIFT;
    val "true" : hIFT;
    val "false" : hIFT
  }%ty :: Γ u⊢ₜ hIFT, 0 <: p0Bool, 0.
Proof. eapply iSub_Sel''; tcrush. varsub; tcrush. Qed.

Example SubIFT_LaterP0Bool' Γ : {@
    typeEq "Boolean" hIFT;
    val "true" : hIFT;
    val "false" : hIFT
  }%ty :: Γ u⊢ₜ hIFT, 0 <: ▶: p0Bool, 0.
Proof. ettrans; first exact: SubIFT_P0Bool. tcrush. Qed.

Example SubIFT_LaterP0Bool Γ : (▶: {@
    typeEq "Boolean" hIFT;
    val "true" : ▶: p0Bool;
    val "false" : ▶: p0Bool
  })%ty :: Γ u⊢ₜ hIFT, 0 <: ▶: p0Bool, 0.
Proof.
  asideLaters.
  ettrans; first (apply (iSub_AddI _ _ 1); tcrush).
  eapply iSub_Sel''; tcrush.
  varsub; tcrush.
Qed.

Example boolImplTypConcr Γ :
  Γ u⊢ₜ boolImplV : boolImplTConcr.
Proof. tcrush; by [apply (iD_Typ_Abs hIFT); tcrush | var]. Qed.

Example boolImplTyp Γ :
  Γ u⊢ₜ boolImplV : boolImplT.
Proof.
  apply (iT_ISub_nocoerce boolImplTConcr); first by apply boolImplTypConcr.
  tcrush; rewrite iterate_0; ltcrush; apply SubIFT_LaterP0Bool'.
Qed.

Module Export hBoolSing.
Import hoasNotation.
Definition hIFTGenT hres : hty :=
  ∀: x : tparam "A", ∀: t : x @; "A", ∀: f: x @; "A", hres t f.

Definition hIFTFalseT : hty := hIFTGenT (λ t f, hTSing f).
Definition hIFTTrueT : hty := hIFTGenT (λ t f, hTSing t).

Example iftTrueSingTyp Γ : Γ u⊢ₜ hiftTrue : hIFTTrueT.
Proof.
  tcrush; cbv.
  eapply iT_Path', iP_Sngl_Refl.
  typconstructor; var.
Qed.

Example iftFalseSingTyp Γ : Γ u⊢ₜ hiftFalse : hIFTFalseT.
Proof.
  tcrush; cbv.
  eapply iT_Path', iP_Sngl_Refl.
  typconstructor; var.
Qed.

Lemma hIFTTrueTSub Γ : Γ u⊢ₜ hIFTTrueT, 0 <: hIFT, 0.
Proof. tcrush; varsub; tcrush. Qed.

Lemma hIFTFalseTSub Γ : Γ u⊢ₜ hIFTFalseT, 0 <: hIFT, 0.
Proof. tcrush; varsub; tcrush. Qed.

Import DBNotation.

Module AssertPlain.
Definition assertBody e : tm :=
  tskip (tyApp e "A" (⊤ →: ⊤) $: x1 $: x0).

Import hoasNotation.

Definition hassertFun e :=
  hlett: hsucc := λ: x, x in:
  hlett: hfail := hloopFunTm in:
  pureS (assertBody e).

Definition hassert e :=
  hassertFun e $: hvint 0.

Lemma hassertBodyTyp Γ e T :
  T :: Γ u⊢ₜ e : hIFT →
  T :: Γ u⊢ₜ x0 : ⊤ →: ⊤ →
  T :: Γ u⊢ₜ x1 : ⊤ →: ⊤ →
  T :: Γ u⊢ₜ assertBody e : ⊤ →: ⊤.
Proof.
  rewrite /assertBody => /= He Hx0 Hx1.
  have Hty : T :: Γ u⊢ₜ tyApp e "A" (⊤ →: ⊤) :
    (⊤ →: ⊤) →: (⊤ →: ⊤) →: ▶: (⊤ →: ⊤).
  by eapply tyApp_typed; first apply He; intros; simpl; tcrush;
    [eapply iSub_Sel', (path_tp_delay (i := 0))..|
    eapply iSel_Sub, (path_tp_delay (i := 0))];
    try (typconstructor; var); wtcrush.
  move: Hty => /iT_All_Ex /(_ Hx1 _) /iT_All_Ex /(_ Hx0) /= Hty.
  eapply (iT_ISub (i := 1)), Hty; tcrush.
Qed.

Lemma hassertFunTyp Γ e
  (Hty : ((⊤ →: ⊤) :: (⊤ →: ⊤) :: Γ)%ty u⊢ₜ e : hIFT) :
  Γ u⊢ₜ hassertFun e : ⊤ →: ⊤.
Proof.
  apply iT_Let with (T := (⊤ →: ⊤)%ty); tcrush; first var.
  apply iT_Let with (T := (⊤ →: ⊤)%ty); stcrush.
  by eapply iT_ISub_nocoerce; first apply loopFunTyp; tcrush.
  by apply hassertBodyTyp; tcrush; var.
Qed.

Lemma hassertTyp Γ e
  (Ht : ((⊤ →: ⊤) :: (⊤ →: ⊤) :: Γ)%ty u⊢ₜ e : hIFT) :
  Γ u⊢ₜ hassert e : ⊤.
Proof.
  eapply iT_All_E, iT_ISub_nocoerce; first exact: hassertFunTyp; tcrush.
Qed.
End AssertPlain.

Module AssertSingletons.

Definition assertBody e : tm :=
  tyApp e "A" ⊤ $: x1 $: x0.

Import hoasNotation.
Definition hassertFun e :=
  hlett: hsucc := λ: x, x in:
  hlett: hfail := hloopFunTm in:
  pureS (assertBody e).

Definition hassert e :=
  hassertFun e $: hvint 0.

Lemma hassertBodyFalseTyp Γ e T :
  T :: Γ u⊢ₜ e : hIFTFalseT →
  T :: Γ u⊢ₜ x0 : ⊤ →
  T :: Γ u⊢ₜ x1 : ⊤ →
  T :: Γ u⊢ₜ assertBody e : TSing x0.
Proof.
  move => /= He Hx0 Hx1.
  have Hty : T :: Γ u⊢ₜ tyApp e "A" ⊤ :
    ∀: t : ⊤, ∀: f: ⊤, hTSing f.
  by eapply tyApp_typed; first apply He; intros; tcrush;
    eapply iSub_Sel', (path_tp_delay (i := 0));
    try (typconstructor; var); wtcrush.
  rewrite /assertBody.
  move: Hty => /iT_All_Ex /(_ Hx1 _) /iT_All_Ex /(_ Hx0) /=.
  apply; tcrush.
Qed.

Lemma hassertBodyTrueTyp Γ e T U :
  T :: U :: Γ u⊢ₜ e : hIFTTrueT →
  T :: U :: Γ u⊢ₜ x1 : ⊤ →
  T :: U :: Γ u⊢ₜ x0 : ⊤ →
  T :: U :: Γ u⊢ₜ assertBody e : TSing x1.
Proof.
  move => /= He Hx1 Hx0.
  have Hty : T :: U :: Γ u⊢ₜ tyApp e "A" ⊤ :
    ∀: t : ⊤, ∀: f: ⊤, hTSing t.
  by eapply tyApp_typed; first apply He; intros; tcrush;
    eapply iSub_Sel', (path_tp_delay (i := 0));
    try (typconstructor; var); wtcrush.
  rewrite /assertBody.
  move: Hty => /iT_All_Ex /(_ Hx1 _) /iT_All_Ex /(_ Hx0) /=.
  apply; tcrush.
Qed.

Lemma hassertFunTrueTyp Γ e :
  (⊤ :: ⊤ :: Γ)%ty u⊢ₜ e : hIFTTrueT →
  Γ u⊢ₜ hassertFun e : ⊤.
Proof.
  move => /hassertBodyTrueTyp He.
  apply iT_Let with (T := ⊤%ty); stcrush. {
    apply (iT_ISub_nocoerce (⊤ →: ⊤)); tcrush; var.
  }
  apply iT_Let with (T := ⊤%ty); stcrush. {
    eapply iT_ISub_nocoerce; first apply loopFunTyp; tcrush.
  }
  eapply iT_ISub_nocoerce; first apply He; tcrush; var.
Qed.

Lemma hassertFunFalseTyp Γ e :
  (⊤ :: ⊤ :: Γ)%ty u⊢ₜ e : hIFTFalseT →
  Γ u⊢ₜ hassertFun e : ⊤.
Proof.
  move => /hassertBodyFalseTyp He.
  apply iT_Let with (T := ⊤%ty); stcrush. {
    apply (iT_ISub_nocoerce (⊤ →: ⊤)); tcrush; var.
  }
  apply iT_Let with (T := ⊤%ty); stcrush. {
    eapply iT_ISub_nocoerce; first apply loopFunTyp; tcrush.
  }
  eapply iT_ISub_nocoerce; first apply He; tcrush; var.
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

(* ∀ x : {type U}, x.U → (self.T → x.U) → x.U *)
Definition hpmatchT self := ∀: x : tparam "U", x @; "U" →: (self @; "T" →: x @; "U") →: x @; "U".
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
  val "isEmpty" = hiftTrue;
  val "pmatch" = λ: x none some, none
}.

Example noneTypStronger Γ :
  Γ u⊢ₜ hnoneV : hnoneSingT.
Proof.
  have := iftTrueSingTyp ((▶: hnoneSingTBody hx0)%ty :: Γ) =>
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
  val "get" : ▶: self @; "T"
}.

Definition hmkSomeTGen res : hty := ∀: x: tparam "A", x @; "A" →: res (x @; "A") (x @; "A").

Definition hmkSomeTSing : hty := hmkSomeTGen hsomeSingT.

Definition hmkSome : hvl := λ: x content, ν: self, {@
  type "T" = x @; "A";
  val "isEmpty" = hiftFalse;
  val "pmatch" = λ: x none some, some $: htskip (self @: "get");
  val "get" = content
}.

Example mkSomeTypStronger Γ :
  Γ u⊢ₜ hmkSome : hmkSomeTSing.
Proof.
  evar (Γ' : ctx).
  have := iftFalseSingTyp Γ' => /(iD_Val "isEmpty"); rewrite /Γ' => Hf.
  tcrush; cbv.
  - eapply iT_All_E; first var.
    apply (iT_ISub (i := 1) (T1 := ▶: hx3 @; "T")); tcrush.
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
  val "none" = hnoneV;
  val "mkSome" = hmkSome
}.

(** Rather precise type for [hoptionModV]. *)
Example optionModConcrTyp Γ :
  Γ u⊢ₜ hoptionModV : (μ: _, hoptionModTConcrBody).
Proof.
  set U := (▶: hoptionModTConcrBody)%ty : ty.
  have := noneTypStronger (U :: Γ).
  have := mkSomeTypStronger (U :: Γ) => /(iD_Val "mkSome") Hs Hn.
  ltcrush.
Qed.

(** Define interface for [hoptionModV]. To rewrite to have abstraction. *)

Definition hoptionT := hoptionTGen ⊥ ⊤.

Definition hnoneT self := hTAnd (self @; "Option") {@ typeEq "T" ⊥}.

(** Behold here [(optionT & (μ self, val get: ▶: self @; "T")) & { type T = hT } ]. *)
Definition hsomeT self hL hU : hty :=
  hTAnd (hTAnd (self @; "Option") (μ: self, val "get" : ▶: self @; "T"))
    (type "T" >: hL <: hU).
Definition hmkSomeT self : hty := hmkSomeTGen (hsomeT self).

Definition hoptionModTInvBody self : hty := {@
  type "Option" >: ⊥ <: hoptionTSing;
  val "none" : hnoneT self;
  val "mkSome" : hmkSomeT self
}.

Example optionModInvTyp Γ :
  Γ u⊢ₜ hoptionModV : μ: self, hoptionModTInvBody self.
Proof.
  eapply iT_ISub_nocoerce; first apply optionModConcrTyp.
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

Definition optionModT : ty := hoptionModT.

Ltac prepare_lemma L H :=
  let Γ' := fresh "Γ" in
  evar (Γ' : ctx); have := L Γ'; rewrite {}/Γ' => H.

Example optionModTypSub Γ :
  Γ u⊢ₜ μ: self, hoptionModTInvBody self, 0 <: hoptionModT, 0.
Proof. ltcrush; varsub; tcrush. Qed.

Example optionModTyp Γ :
  Γ u⊢ₜ hoptionModV : hoptionModT.
Proof. eapply iT_ISub_nocoerce, optionModTypSub; apply optionModInvTyp. Qed.

End option.
