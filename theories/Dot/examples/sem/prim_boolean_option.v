
From D Require Import tactics.
From D.Dot Require Import syn ex_utils hoas storeless_typing_ex_utils.
From D.Dot Require Import storeless_typing.

Import DBNotation.

Set Implicit Arguments.
Set Suggest Proof Using.
Set Default Proof Using "Type".

Definition mapfst {A B C} (f : A → C): A * B → (C * B) := λ '(a, b), (f a, b).

Module prim_boolean_option_mod.
Import hoasNotation.

Ltac tMember := apply iD_Typ; tcrush; by_extcrush.

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

Definition hnoneConcrTBody self : hty := {@
  typeEq "T" ⊥;
  val "isEmpty" : hTSing true;
  val "pmatch" : hpmatchT self
}.
Definition hnoneConcrT := μ: self, hnoneConcrTBody self.

Definition hsomeConcrT hL hU : hty := μ: self, {@
  type "T" >: hL <: hU;
  val "isEmpty" : hTSing false;
  val "pmatch" : hpmatchT self;
  val "get" : ▶: self @; "T"
}.

Definition hmkSomeTGen res : hty := ∀: x: tparam "A", (x @; "A" →: res (x @; "A") (x @; "A")).
Definition hmkSomeTSing : hty := hmkSomeTGen hsomeConcrT.


Definition hoptionTConcr := hTOr hnoneConcrT (hsomeConcrT ⊥ ⊤).

Definition hoptionModTConcrBody : hty := {@
  typeEq "Option" hoptionTConcr;
  val "none" : hnoneConcrT;
  val "mkSome" : hmkSomeTSing
}.

(** Define interface for [hoptionModV]. To rewrite to have abstraction. *)

Definition hoptionT := hoptionTGen ⊥ ⊤.

Definition hnoneT self := hTAnd (self @; "Option") {@ typeEq "T" ⊥}.

(** Behold here [(optionT & (μ self, val get: ▶: self @; "T")) & { type T = hT } ]. *)
Definition hsomeT self hL hU : hty :=
  hTAnd (hTAnd (self @; "Option") (μ: self, val "get" : ▶: self @; "T"))
    (type "T" >: hL <: hU).
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


(** Define the stamped map table we'll need. *)
Definition hpBot : hstampTy := MkTy 1 [] ⊥ 0.
Definition hpXA x : hstampTy := MkTy 2 [x] (hx0 @; "A") 1.
Definition hpOptionTConcr : hstampTy := MkTy 3 [] hoptionTConcr 0.

Definition primOptionG : stys := psAddStys ∅ [hpBot; hpXA hx0; hpOptionTConcr].

Lemma hpBotStamp : hTyMemStamp primOptionG hpBot. Proof. split; stcrush. Qed.
Lemma hpXAStamp : hTyMemStamp primOptionG (hpXA hx0). Proof. split; stcrush. Qed.
Lemma hpOptionTConcrStamp : hTyMemStamp primOptionG hpOptionTConcr. Proof. split; stcrush. Qed.

Lemma Hbot: styConforms primOptionG hpBot. Proof. done. Qed.
Lemma hpBotExt : hextractPreTyMem primOptionG hpBot. Proof. by_extcrush. Qed.

Lemma HxA : styConforms primOptionG (hpXA hx0). Proof. done. Qed.
Lemma hpXAExt : hextractPreTyMem primOptionG (hpXA hx0). Proof. by_extcrush. Qed.

Lemma HoptionTConcr : styConforms primOptionG hpOptionTConcr. Proof. done. Qed.
Lemma hpOptionTConcrExt : hextractPreTyMem primOptionG hpOptionTConcr. Proof. by_extcrush. Qed.

Opaque primOptionG.

Definition hnoneV := ν: _, {@
  type "T" =[ hpBot ];
  val "isEmpty" = true;
  val "pmatch" = λ: x none some, none
}.

Lemma boolSing g Γ (b : bool) : Γ v⊢ₜ[g] b : TSing b.
Proof.
  eapply iT_Path', (iP_Sngl_Refl (T := TBool)).
  tcrush.
Qed.

Example noneTypStronger Γ :
  Γ v⊢ₜ[ primOptionG ] hnoneV : hnoneConcrT.
Proof.
  tcrush; [tMember | apply boolSing | var].
Qed.

Definition hmkSome : hvl := λ: x content, ν: self, {@
  type "T" =[ hpXA x ];
  val "isEmpty" = false;
  val "pmatch" = λ: x none some, some $: htskip (self @: "get");
  val "get" = content
}.

Example mkSomeTypStronger Γ :
  Γ v⊢ₜ[ primOptionG ] hmkSome : hmkSomeTSing.
Proof.
  tcrush; cbv.
  - tMember.
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
  type "Option" =[ hpOptionTConcr ];
  val "none" = hnoneV;
  val "mkSome" = hmkSome
}.

(** Rather precise type for [hoptionModV]. *)
Example optionModConcrTyp Γ :
  Γ v⊢ₜ[ primOptionG ] hoptionModV : μ: _, hoptionModTConcrBody.
Proof.
  set U := (▶: hoptionModTConcrBody)%ty : ty.
  have := noneTypStronger (U :: Γ).
  have := mkSomeTypStronger (U :: Γ) => /(iD_Val "mkSome") Hs Hn.
  ltcrush.
  tMember.
Qed.

Example optionModInvTyp Γ :
  Γ v⊢ₜ[ primOptionG ] hoptionModV : μ: self, hoptionModTInvBody self.
Proof.
  eapply iT_ISub_nocoerce; first apply optionModConcrTyp.
  ltcrush; rewrite iterate_0.
  eapply iSub_Sel'; tcrush; varsub; ltcrush.
  all: try eapply iSub_Sel', (path_tp_delay (i := 0));
    try (varsub; ltcrush); wtcrush.
  all: try (ettrans; last eapply iSub_Or2); mltcrush.
Qed.

Example optionModTypSub Γ :
  Γ v⊢ₜ[ primOptionG ] μ: self, hoptionModTInvBody self, 0 <: hoptionModT, 0.
Proof. ltcrush; eapply (iP_ISub (i := 0)), iP_Bool_I; tcrush. Qed.

Example optionModTyp Γ :
  Γ v⊢ₜ[ primOptionG ] hoptionModV : hoptionModT.
Proof. eapply iT_ISub_nocoerce, optionModTypSub; apply optionModInvTyp. Qed.

End prim_boolean_option_mod.
