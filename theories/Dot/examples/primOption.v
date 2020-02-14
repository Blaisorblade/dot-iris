From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra hoas typingExInfra.
(* From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived. *)
From D.Dot.typing Require Import typing_storeless.
Import DBNotation.

Set Implicit Arguments.
Set Suggest Proof Using.
Set Default Proof Using "Type".

Implicit Types (g : stys).

Definition mapfst {A B C} (f : A → C): A * B → (C * B) := λ '(a, b), (f a, b).

Module primOption.
Import hoasNotation.

Section primOption'.
Context {g}.

(*
  Encoding Option, using actual booleans. However, we do export Option as an abstract type.
  type Option = {
    type T
    val isEmpty: Boolean
    val pmatch: [U] => U => (T => U) => U
  }
*)

(* ∀ x : {type U}, x.U → (self.T -> x.U) -> x.U *)
Definition hpmatchT self := ∀: x : tparam "U", hpv x @; "U" →: (hpv self @; "T" →: hpv x @; "U") →: hpv x @; "U".
Definition hoptionTGen (L U : hty) := μ: self, {@
  type "T" >: L <: U;
  val "isEmpty" : hTBool;
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
Definition hnoneConcrTBody self : hty := {@
  typeEq "T" ⊥;
  val "isEmpty" : hTBool;
  val "pmatch" : hpmatchT self
}.
Definition hnoneConcrT := μ: self, hnoneConcrTBody self.

Definition hpBot : hstampTy := MkTy 1 [] ⊥ 0.
Lemma hpBotStamp : hTyMemStamp g hpBot. Proof. split; stcrush. Qed.
Context (Hbot : styConforms g hpBot).
Lemma hpBotExt : hextractPreTyMem g hpBot. Proof using Hbot. by apply stampTyAgree, hpBotStamp. Qed.

Definition hpXA x : hstampTy := MkTy 2 [x] (hclose (hpv hx0 @; "A")) 1.
Lemma hpXAStamp : hTyMemStamp g (hpXA hx0). Proof. split; stcrush. Qed.
Context (HxA : styConforms g (hpXA hx0)).
Lemma hpXAExt : hextractPreTyMem g (hpXA hx0).
Proof using HxA. (* by_extcrush. *) by apply stampTyAgree, hpXAStamp. Qed.

Definition hnoneV := ν: _, {@
  type "T" =[ hpBot ];
  val "isEmpty" = true;
  val "pmatch" = λ: x none some, none
}.
Definition noneV := hclose hnoneV.

Example noneTypStronger Γ :
  Γ v⊢ₜ[ g ] tv noneV : hclose hnoneConcrT.
Proof using Hbot.
  tcrush; last var.
  apply (dty_typed ⊥); tcrush.
  by_extcrush.
  (* apply: extraction_weaken; first apply: hpBotExt; cbn; lia. *)
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

Definition hsomeConcrT hL hU : hty := μ: self, {@
  type "T" >: hL <: hU;
  val "isEmpty" : hTBool;
  val "pmatch" : hpmatchT self;
  val "get" : ▶: self @; "T"
}.

Definition hmkSomeTGen res : hty := ∀: x: tparam "A", (x @; "A" →: res (x @; "A") (x @; "A")).

Definition hmkSomeTSing : hty := hmkSomeTGen hsomeConcrT.

Definition hmkSome : hvl := λ: x content, ν: self, {@
  (* type "T" = hpv x @; "A"; *)
  type "T" =[ hpXA x ];
  val "isEmpty" = false;
  val "pmatch" = λ: x none some, some $: htskip (self @: "get");
  val "get" = content
}.
Definition mkSome := hclose hmkSome.

Example mkSomeTypStronger Γ :
  Γ v⊢ₜ[ g ] tv mkSome : hclose hmkSomeTSing.
Proof using HxA.
  tcrush; cbv.
  - apply (dty_typed (hclose $ hpv hx2 @; "A")); tcrush; by_extcrush.
  - eapply App_typed; first var.
    apply (Subs_typed (i := 1) (T1 := hclose (▶: (hp3 @; "T"))%HT)); tcrush.
    varsub; ltcrush.
  - varsub.
    ettrans; first (apply TAddLater_stp; tcrush).
    asideLaters.
    eapply LSel_stp''; tcrush. varsub; tcrush.
Qed.

Definition hoptionTConcr := hTOr hnoneConcrT (hsomeConcrT ⊥ ⊤).

Definition hoptionModTConcrBody : hty := {@
  typeEq "Option" hoptionTConcr;
  val "none" : hnoneConcrT;
  val "mkSome" : hmkSomeTSing
}.

Definition hpOptionTConcr : hstampTy := MkTy 3 [] (hclose hoptionTConcr) 0.
Lemma hpOptionTConcrStamp : hTyMemStamp g hpOptionTConcr. Proof. split; stcrush. Qed.
Context (HoptionTConcr : styConforms g hpOptionTConcr).
Lemma hpOptionTConcrExt : hextractPreTyMem g hpOptionTConcr. Proof using HoptionTConcr. by_extcrush. Qed.

Definition hoptionModV := ν: self, {@
  type "Option" =[ hpOptionTConcr ];
  val "none" = hnoneV;
  val "mkSome" = hmkSome
}.

Collection gHyps := Hbot HxA HoptionTConcr.

(** Rather precise type for [hoptionModV]. *)
Example optionModConcrTyp Γ :
  Γ v⊢ₜ[ g ] hclose hoptionModV : hclose (μ: _, hoptionModTConcrBody).
Proof using gHyps.
  set U := hclose (▶: hoptionModTConcrBody).
  have := noneTypStronger (U :: Γ).
  have := mkSomeTypStronger (U :: Γ) => /(dpt_pv_typed "mkSome") Hs Hn.
  ltcrush.
  apply (dty_typed (hclose hoptionTConcr)); tcrush. by_extcrush.
Qed.

(** Define interface for [hoptionModV]. To rewrite to have abstraction. *)

Definition hoptionT := hoptionTGen ⊥ ⊤.
Definition optionT := hclose hoptionT.

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

Example optionModInvTyp Γ :
  Γ v⊢ₜ[ g ] hclose hoptionModV : hclose (μ: self, hoptionModTInvBody self).
Proof using gHyps.
  eapply Subs_typed_nocoerce; first apply optionModConcrTyp.
  ltcrush; rewrite iterate_0.
  all: try (eapply LSel_stp'; tcrush; varsub; ltcrush).
  all: try (ettrans; last eapply TOr2_stp); mltcrush.
Qed.

Definition hoptionModT := μ: self, {@
  type "Option" >: ⊥ <: hoptionT;
  val "none" : hnoneT self;
  val "mkSome" : hmkSomeT self
}.

Example optionModTypSub Γ :
  Γ v⊢ₜ[ g ] hclose (μ: self, hoptionModTInvBody self), 0 <: hclose hoptionModT, 0.
Proof. ltcrush. Qed.

Example optionModTyp Γ :
  Γ v⊢ₜ[ g ] hclose (htv hoptionModV) : hclose hoptionModT.
Proof using gHyps. eapply Subs_typed_nocoerce, optionModTypSub; apply optionModInvTyp. Qed.

End primOption'.
End primOption.
