
From D Require Import tactics.
From D.Dot Require Import syn ex_utils hoas storeless_typing_ex_utils.
From D.Dot Require Import storeless_typing.

Import DBNotation.

Set Implicit Arguments.
Set Suggest Proof Using.
Set Default Proof Using "Type".

Module prim_boolean_option_mod.
Import hoasNotation.

(**
Encoding Option, using primitive booleans; we export Option as an abstract type.
**)

(*
  Source in pseudo-Scala.

  type Option = {
    type T
    val isEmpty: Boolean
    val pmatch: [U] => U => (T => U) => U
  }

  type None = Option { type T = Nothing }
  val noneV: None = new {
    type T = Nothing
    val isEmpty = true
    val pmatch: [U] => U => (Nothing => U) => U = [U] => (none: U) => (some: T => U) => none
  }

  //type Some = Option & { self => val get: self.T }
  type Some = Option & { type T; val get: T }
  def mkSome[S](t: S): Some { type T = S } = new {
    type T = S
    val isEmpty = false
    val get = t
    val pmatch: [U] => U => (T => U) => U = [U] => (none: U) => (some: T => U) => some(get)
  }
*)

(* ∀ x : {type U}, x.U → (self.T → x.U) → x.U *)
Definition hpmatchT self := ∀: x : tparam "U", x @; "U" →: (self @; "T" →: x @; "U") →: x @; "U".
Definition hoptionTGen (L U : hty) := μ: self, {@
  type "T" >: L <: U;
  val "isEmpty" : hTBool;
  val "pmatch" : hpmatchT self
}.

Definition hnoneConcrT : hty := μ: self, {@
  typeEq "T" ⊥;
  val "isEmpty" : hTSing true;
  val "pmatch" : hpmatchT self
}.

Definition hsomeConcrT hL hU : hty := μ: self, {@
  type "T" >: hL <: hU;
  val "isEmpty" : hTSing false;
  val "pmatch" : hpmatchT self;
  val "get" : ▶: self @; "T"
}.

Definition hmkSomeTGen res : hty := ∀: x: tparam "A", (x @; "A" →: res (x @; "A") (x @; "A")).
Definition hmkSomeConcrT : hty := hmkSomeTGen hsomeConcrT.


Definition hoptionTConcr := hTOr hnoneConcrT (hsomeConcrT ⊥ ⊤).

Definition hoptionModTConcrBody : hty := {@
  typeEq "Option" hoptionTConcr;
  val "none" : hnoneConcrT;
  val "mkSome" : hmkSomeConcrT
}.

(** Define interface for [hoptionModV]. To rewrite to have abstraction. *)

Definition hoptionT := hoptionTGen ⊥ ⊤.

Definition hnoneT self := hTAnd (self @; "Option") {@ typeEq "T" ⊥; val "isEmpty" : hTSing true }.

(** Behold here [(optionT & (μ self, val get: ▶: self @; "T")) & { type T = hT; val isEmpty; false.type } ]. *)
Definition hsomeT self hL hU : hty :=
  hTAnd (hTAnd (self @; "Option") (μ: self, val "get" : ▶: self @; "T"))
    {@ type "T" >: hL <: hU; val "isEmpty" : hTSing false }.

Definition hmkSomeT self : hty := hmkSomeTGen (hsomeT self).

Definition hoptionModTInvBody self : hty := {@
  type "Option" >: ⊥ <: hoptionTConcr;
  val "none" : hnoneT self;
  val "mkSome" : hmkSomeT self
}.

Definition hoptionModT := μ: self, {@
  type "Option" >: ⊥ <: hoptionT;
  val "none" : hnoneT self;
  val "mkSome" : hmkSomeT self
}.

Definition optionModT : ty := hoptionModT.

Definition hnoneV := ν: _, {@
  type "T" = ⊥ ;
  val "isEmpty" = true;
  val "pmatch" = λ: x none some, none
}.

Lemma boolSing Γ (b : bool) : Γ v⊢ₜ b : TSing b.
Proof.
  eapply iT_Path', (iP_Sngl_Refl (T := TBool)).
  tcrush.
Qed.

Example noneTypStronger Γ :
  Γ v⊢ₜ hnoneV : hnoneConcrT.
Proof. tcrush; [tcrush_nclosed | apply boolSing | var]. Qed.

Definition hmkSome : hvl := λ: x content, ν: self, {@
  type "T" = x @; "A";
  val "isEmpty" = false;
  val "pmatch" = λ: x none some, some $: htskip (self @: "get");
  val "get" = content
}.

Example mkSomeTypStronger Γ :
  Γ v⊢ₜ hmkSome : hmkSomeConcrT.
Proof.
  tcrush.
  - tcrush_nclosed.
  - apply boolSing.
  - eapply iT_All_E; first var.
    apply (iT_ISub (i := 1) (T1 := (▶: (hx3 @; "T"))%HS)); tcrush.
    varsub; ltcrush.
  - varsub.
    ettrans; first (apply iSub_Add_Later; tcrush).
    asideLaters.
    eapply iSub_Sel''; tcrush. varsub; tcrush.
Qed.


Definition hoptionModV := ν: self, {@
  type "Option" = hoptionTConcr;
  val "none" = hnoneV;
  val "mkSome" = hmkSome
}.

(** Rather precise type for [hoptionModV]. *)
Example optionModConcrTyp Γ :
  Γ v⊢ₜ hoptionModV : μ: _, hoptionModTConcrBody.
Proof.
  set U := (▶: hoptionModTConcrBody)%ty : ty.
  have := noneTypStronger (U :: Γ).
  have := mkSomeTypStronger (U :: Γ) => /(iD_Val "mkSome") Hs Hn.
  ltcrush.
  tcrush_nclosed.
Qed.

Example optionModInvTyp Γ :
  Γ v⊢ₜ hoptionModV : μ: self, hoptionModTInvBody self.
Proof.
  eapply iT_ISub_nocoerce; first apply optionModConcrTyp.
  ltcrush; rewrite iterate_0.
  eapply iSub_Sel'; tcrush; varsub; ltcrush.
  all: try eapply iSub_Sel', (path_tp_delay (i := 0));
    try (varsub; ltcrush); wtcrush.
  all: try (ettrans; last eapply iSub_Or2); mltcrush.
Qed.

Example optionModTypSub Γ :
  Γ v⊢ₜ μ: self, hoptionModTInvBody self, 0 <: hoptionModT, 0.
Proof. ltcrush; eapply (iP_ISub (i := 0)), iP_Bool_I; tcrush. Qed.

Example optionModTyp Γ :
  Γ v⊢ₜ hoptionModV : hoptionModT.
Proof. eapply iT_ISub_nocoerce, optionModTypSub; apply optionModInvTyp. Qed.

End prim_boolean_option_mod.
