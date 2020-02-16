From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra hoas typingExInfra.
(* From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived. *)
From D.Dot.typing Require Import typing_storeless.
(* From D.Dot Require Import unary_lr
  lr_lemmas lr_lemmasTSel lr_lemmasNoBinding lr_lemmasDefs lr_lemmasPrim.
From D.Dot Require Import typeExtractionSem.
From D.Dot Require Import fundamental.
From D Require Import swap_later_impl. *)

Import DBNotation.

Set Implicit Arguments.
Set Suggest Proof Using.
Set Default Proof Using "Type".

Definition mapfst {A B C} (f : A → C): A * B → (C * B) := λ '(a, b), (f a, b).

Module primOption.
Import hoasNotation.

Ltac tMember := apply Dty_typed; tcrush; by_extcrush.

Section primOption'.

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

(* ∀ x : {type U}, x.U → (self.T -> x.U) -> x.U *)
Definition hpmatchT self := ∀: x : tparam "U", hpv x @; "U" →: (hpv self @; "T" →: hpv x @; "U") →: hpv x @; "U".
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

Definition hoptionModT := μ: self, {@
  type "Option" >: ⊥ <: hoptionT;
  val "none" : hnoneT self;
  val "mkSome" : hmkSomeT self
}.


(** Define the stamped map table we'll need. *)
Definition hpBot : hstampTy := MkTy 1 [] ⊥ 0.
Definition hpXA x : hstampTy := MkTy 2 [x] (hclose (hpv hx0 @; "A")) 1.
Definition hpOptionTConcr : hstampTy := MkTy 3 [] (hclose hoptionTConcr) 0.

Definition primOptionG : stys := psAddStys ∅ [hpBot; hpXA hx0; hpOptionTConcr].

Lemma hpBotStamp : hTyMemStamp primOptionG hpBot. Proof. split; stcrush. Qed.
Lemma hpXAStamp : hTyMemStamp primOptionG (hpXA hx0). Proof. split; stcrush. Qed.
Lemma hpOptionTConcrStamp : hTyMemStamp primOptionG hpOptionTConcr. Proof. split; stcrush. Qed.

Lemma Hbot: styConforms primOptionG hpBot. Proof. done. Qed.
Lemma hpBotExt : hextractPreTyMem primOptionG hpBot. Proof. by_extcrush. Qed.
(* Proof. apply /hstampTyAgree /hpBotStamp /Hbot. Qed. *)

Lemma HxA : styConforms primOptionG (hpXA hx0). Proof. done. Qed.
Lemma hpXAExt : hextractPreTyMem primOptionG (hpXA hx0). Proof. by_extcrush. Qed.
(* Proof. by apply /hstampTyAgree /hpXAStamp /HxA. Qed. *)

Lemma HoptionTConcr : styConforms primOptionG hpOptionTConcr. Proof. done. Qed.
Lemma hpOptionTConcrExt : hextractPreTyMem primOptionG hpOptionTConcr. Proof. by_extcrush. Qed.

Opaque primOptionG.

Definition hnoneV := ν: _, {@
  type "T" =[ hpBot ];
  val "isEmpty" = true;
  val "pmatch" = λ: x none some, none
}.
Definition noneV := hclose hnoneV.

Lemma boolSing g Γ (b : bool) : Γ v⊢ₜ[g] b : TSing b.
Proof.
  eapply (Path_typed (p := b)), (psingleton_refl_typed (T := TBool)).
  tcrush.
Qed.

Example noneTypStronger Γ :
  Γ v⊢ₜ[ primOptionG ] tv noneV : hclose hnoneConcrT.
Proof.
  tcrush; [tMember | apply boolSing | var].
Qed.

Definition hmkSome : hvl := λ: x content, ν: self, {@
  (* type "T" = hpv x @; "A"; *)
  type "T" =[ hpXA x ];
  val "isEmpty" = false;
  val "pmatch" = λ: x none some, some $: htskip (self @: "get");
  val "get" = content
}.
Definition mkSome := hclose hmkSome.

Example mkSomeTypStronger Γ :
  Γ v⊢ₜ[ primOptionG ] tv mkSome : hclose hmkSomeTSing.
Proof.
  tcrush; cbv.
  - tMember.
    (* apply (dty_typed (hclose $ hpv hx2 @; "A")); tcrush; by_extcrush. *)
  - apply boolSing.
  - eapply App_typed; first var.
    apply (Subs_typed (i := 1) (T1 := hclose (▶: (hp3 @; "T"))%HT)); tcrush.
    varsub; ltcrush.
  - varsub.
    ettrans; first (apply TAddLater_stp; tcrush).
    asideLaters.
    eapply LSel_stp''; tcrush. varsub; tcrush.
Qed.


Definition hoptionModV := ν: self, {@
  type "Option" =[ hpOptionTConcr ];
  val "none" = hnoneV;
  val "mkSome" = hmkSome
}.

(** Rather precise type for [hoptionModV]. *)
Example optionModConcrTyp Γ :
  Γ v⊢ₜ[ primOptionG ] hclose hoptionModV : hclose (μ: _, hoptionModTConcrBody).
Proof.
  set U := hclose (▶: hoptionModTConcrBody).
  have := noneTypStronger (U :: Γ).
  have := mkSomeTypStronger (U :: Γ) => /(dpt_pv_typed "mkSome") Hs Hn.
  ltcrush.
  tMember.
Qed.

Example optionModInvTyp Γ :
  Γ v⊢ₜ[ primOptionG ] hclose hoptionModV : hclose (μ: self, hoptionModTInvBody self).
Proof.
  eapply Subs_typed_nocoerce; first apply optionModConcrTyp.
  ltcrush; rewrite iterate_0.
  eapply LSel_stp'; tcrush; varsub; ltcrush.
  all: try eapply LSel_stp', (path_tp_delay (i := 0));
    try (typconstructor; varsub; ltcrush); wtcrush.
  all: try (ettrans; last eapply TOr2_stp); mltcrush.
Qed.

Example optionModTypSub Γ :
  Γ v⊢ₜ[ primOptionG ] hclose (μ: self, hoptionModTInvBody self), 0 <: hclose hoptionModT, 0.
Proof. ltcrush; eapply (Subs_typed (i := 0)), T_Bool_typed; tcrush. Qed.

Example optionModTyp Γ :
  Γ v⊢ₜ[ primOptionG ] hclose (htv hoptionModV) : hclose hoptionModT.
Proof. eapply Subs_typed_nocoerce, optionModTypSub; apply optionModInvTyp. Qed.

End primOption'.
End primOption.
