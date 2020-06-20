(**
Encoding Option, using primitive booleans; we export Option as an abstract type.
The core lemma is [optionModInvTyp].
**)

From D Require Import tactics.
From D.Dot Require Import syn ex_utils hoas storeless_typing_ex_utils.
From D.Dot Require Import storeless_typing.

Import DBNotation.

Set Implicit Arguments.
Set Suggest Proof Using.
Set Default Proof Using "Type".

Module prim_boolean_option_mod.
Import hoasNotation.

(*
  Approximated source, in pseudo-Scala.

  type Option = {
    type T
    val isEmpty: Boolean
    val pmatch: [U] => U => (T => U) => U
  }

  type None = Option & { type T = Nothing; val isEmpty: true.type }
  val noneV: None = new {
    type T = Nothing
    val isEmpty = true
    val pmatch: [U] => U => (Nothing => U) => U = [U] => (none: U) => (some: T => U) => none
  }

  type Some = Option & { type T; val get: this.T; val isEmpty: false.type }
  def mkSome[S](t: S): Some { type T = S } = new {
    type T = S
    val isEmpty = false
    val get = t
    val pmatch: [U] => U => (T => U) => U = [U] => (none: U) => (some: T => U) => some(get)
  }
*)

(** ** Define interface for [hoptionModV]. *)

(* ∀ x : {type U}, x.U → (self.T → x.U) → x.U *)
Definition hpmatchT self := ∀: x : tparam "U", x @; "U" →: (self @; "T" →: x @; "U") →: x @; "U".

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

(** *** The definition and upper bound for the ["Option"] abstract type. *)
Definition hoptionTConcr := hTOr hnoneConcrT (hsomeConcrT ⊥ ⊤).

(** *** The return types of the ["Option"] constructors. *)
Definition hnoneT self := hTAnd (self @; "Option") {@ typeEq "T" ⊥; val "isEmpty" : hTSing true }.

(** Behold here [(optionT & (μ self, val get: ▶: self @; "T")) & { type T = hT; val isEmpty; false.type } ]. *)
Definition hsomeT self hL hU : hty :=
  hTAnd (hTAnd (self @; "Option") (μ: self, val "get" : ▶: self @; "T"))
    {@ type "T" >: hL <: hU; val "isEmpty" : hTSing false }.

(** The full type of the ["mkSome"] constructor. *)
Local Definition hmkSomeTGen res : hty := ∀: x: tparam "A", (x @; "A" →: res (x @; "A") (x @; "A")).
Definition hmkSomeT self : hty := hmkSomeTGen (hsomeT self).

Definition hoptionModTInvBody self : hty := {@
  type "Option" >: ⊥ <: hoptionTConcr;
  val "none" : hnoneT self;
  val "mkSome" : hmkSomeT self
}.

(** ** Implement [hoptionModV]. *)
Definition hnoneV := ν: _, {@
  type "T" = ⊥;
  val "isEmpty" = true;
  val "pmatch" = λ: x none some, none
}.

Definition hmkSome : hvl := λ: x content, ν: self, {@
  type "T" = x @; "A";
  val "isEmpty" = false;
  val "pmatch" = λ: x none some, some $: htskip (self @: "get");
  val "get" = content
}.

Definition hoptionModV := ν: self, {@
  type "Option" = hoptionTConcr;
  val "none" = hnoneV;
  val "mkSome" = hmkSome
}.

(** *** Define concrete types for [hoptionModV], used only internally for derivation. *)
Local Definition hmkSomeConcrT : hty := hmkSomeTGen hsomeConcrT.

Local Definition hoptionModTConcrBody : hty := {@
  typeEq "Option" hoptionTConcr;
  val "none" : hnoneConcrT;
  val "mkSome" : hmkSomeConcrT
}.

(** *** Prove typing. *)
Lemma boolSing Γ (b : bool) : Γ v⊢ₜ b : TSing b.
Proof.
  eapply iT_Path', (iP_Sngl_Refl (T := TBool)).
  tcrush.
Qed.

Example noneTypStronger Γ :
  Γ v⊢ₜ hnoneV : hnoneConcrT.
Proof. tcrush; [tcrush_nclosed | apply boolSing | var]. Qed.

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


(** Type [hoptionModV] precisely, using [iT_Obj_I] directly. *)
Example optionModConcrTyp Γ :
  Γ v⊢ₜ hoptionModV : μ: _, hoptionModTConcrBody.
Proof.
  set U := (▶: hoptionModTConcrBody)%ty : ty.
  have := noneTypStronger (U :: Γ).
  have := mkSomeTypStronger (U :: Γ) => /(iD_Val "mkSome") Hs Hn.
  apply iT_Obj_I; tcrush.
  tcrush_nclosed.
Qed.

(** Use subsumption to upcast [hoptionModV] to the type representing its
public interface. *)
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

End prim_boolean_option_mod.

(** [hoptionModV] also satisfies a weaker interface, similar to the one
exported by [scala_lib.v]. *)

Module prim_boolean_option_mod_weaker_intf.
Import hoasNotation prim_boolean_option_mod.

Definition hoptionTGen (L U : hty) := μ: self, {@
  type "T" >: L <: U;
  val "isEmpty" : hTBool;
  val "pmatch" : hpmatchT self
}.
Definition hoptionT := hoptionTGen ⊥ ⊤.

Definition hoptionModT := μ: self, {@
  type "Option" >: ⊥ <: hoptionT;
  val "none" : hnoneT self;
  val "mkSome" : hmkSomeT self
}.

Example optionModTypSub Γ :
  Γ v⊢ₜ μ: self, hoptionModTInvBody self, 0 <: hoptionModT, 0.
Proof. ltcrush; eapply (iP_ISub (i := 0)), iP_Bool_I; tcrush. Qed.

Example optionModTyp Γ :
  Γ v⊢ₜ hoptionModV : hoptionModT.
Proof. eapply iT_ISub_nocoerce, optionModTypSub; apply optionModInvTyp. Qed.

End prim_boolean_option_mod_weaker_intf.
