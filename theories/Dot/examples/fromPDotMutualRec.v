(**
 *)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot.syn Require Import syn path_repl.
From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived.
From D.Dot Require Import exampleInfra hoas scalaLib.
Import DBNotation.

(** FromPDotPaper *)

Definition typeRefTBody : ty := {@
  val "symb" : x1 @ "symbols" @; "Symbol"
}.

Definition fromPDotPaperTypesTBody : ty := {@
  typeEq "Type" ⊤;
  typeEq "TypeTop" ⊤;
  val "newTypeTop" : ⊤ →: x0 @; "TypeTop";
  typeEq "TypeRef" $ TAnd (x0 @; "Type") typeRefTBody;
  val "newTypeRef" : x1 @ "symbols" @; "Symbol" →: x0 @; "TypeRef"
}.

Definition fromPDotPaperAbsTypesTBody : ty := {@
  type "Type" >: ⊥ <: TTop;
  type "TypeTop" >: ⊥ <: x0 @; "Type";
  val "newTypeTop" : ⊤ →: x0 @; "TypeTop";
  type "TypeRef" >: ⊥ <: TAnd (p0 @; "Type") typeRefTBody;
  val "newTypeRef" : x1 @ "symbols" @; "Symbol" →: x0 @; "TypeRef"
}.

Definition assert cond :=
  tif cond 0 hloopTm.
Definition seq (e1 e2 : tm) := lett e1 (shift e2).
Notation "t @:: l" := ((tskip t) @: l) (at level 59, l at next level).

Definition newTypeRefBody :=
  seq (assert (~ ((tskip x0) @:: "tpe" @:: "isEmpty")))
    (ν {@ val "symb" = x1 }).

(* Import AssertPlain.
From D.Dot Require Import hoas. *)
Definition fromPDotPaperTypesV : vl := ν {@
  type "Type" = TTop;
  type "TypeTop" = TTop;
  val "newTypeTop" = vabs (ν {@ });
  type "TypeRef" = TAnd (x0 @; "Type") typeRefTBody;
  val "newTypeRef" = vabs newTypeRefBody
}.

Definition fromPDotPaperSymbolsTBody : ty := {@
  typeEq "Symbol" $ {@
    val "tpe" : x1 @ "types" @; "Type";
    val "id" : TInt
  }%ty;
  val "newSymbol" : x1 @ "types" @; "Type" →: TInt →: x0 @; "Symbol"
}.

Definition fromPDotPaperAbsSymbolsTBody : ty := {@
  type "Symbol" >: ⊥ <: {@
    val "tpe" : x1 @ "types" @; "Type";
    val "id" : TInt
  };
  val "newSymbol" : x1 @ "types" @; "Type" →: TInt →: x0 @; "Symbol"
}.

Definition fromPDotPaperTBody : ty := {@
  val "types" : μ fromPDotPaperTypesTBody;
  val "symbols" : μ fromPDotPaperSymbolsTBody
}.

Definition fromPDotPaperAbsTBody : ty := {@
  val "types" : μ fromPDotPaperAbsTypesTBody;
  val "symbols" : μ fromPDotPaperAbsSymbolsTBody
}.

Definition fromPDotPaperSymbolsV : vl := ν {@
  type "Symbol" = {@
    val "tpe" : x1 @ "types" @; "Type";
    val "id" : TInt
  };
  val "newSymbol" = (vabs $ vabs $ ν {@
    val "tpe" = x2;
    val "id" = x1
  })
}.

Definition fromPDotPaper : vl := ν {@
  val "types" = fromPDotPaperTypesV;
  val "symbols" = fromPDotPaperSymbolsV
}.

Example fromPDotPaperTypesTyp :
  TLater fromPDotPaperAbsTBody :: [] u⊢ₜ
    fromPDotPaperTypesV : μ fromPDotPaperTypesTBody.
Proof.
  tcrush.
  - eapply (iT_Sub_nocoerce) => /=; hideCtx.
    + repeat first [var | typconstructor | tcrush].
    + apply (iSub_Trans (T2 := ⊤) (i2 := 0)); first tcrush.
      eapply iSub_Sel'; last (tcrush; varsub); ltcrush.
  - rewrite /newTypeRefBody.
    eapply (iT_Let _ _ _ TTop); tcrush.
    + eapply iT_Un; first constructor.
      tcrush.
      hideCtx.
      have Hx0: Γ u⊢ₜ x0 : x2 @ "symbols" @; "Symbol" by var.
      eapply (iT_Sub (i := 1) (T1 := ▶: val "isEmpty" : TBool)); tcrush.
      eapply (iT_Sub (i := 1)); first by apply iLater_Sub; stcrush.
      eapply (iT_Sub (i := 1)); first by apply iLater_Sub; stcrush.
      varsub.
      ettrans; first apply iSub_Add_Later; stcrush.
      eapply iSub_Trans, iSub_Later; stcrush.
      eapply iSub_Trans; first apply iLater_Sub; stcrush.
      eapply (iSel_Sub (L := ⊥)).
      (* Avoid [iP_Later]. *)
      eapply iP_Fld_E.
      tcrush. varsub.
      asideLaters.
      mltcrush.
      mltcrush.
      eapply (iSel_Sub (L := ⊥)).
      eapply iP_Fld_E.
      mltcrush.
      varsub.
      asideLaters.
      lThis.
      ettrans; last apply (iSub_AddIJ 1); stcrush.
      ltcrush.
      rewrite /fromPDotPaperAbsTypesTBody.
      mltcrush.
      eapply (iT_Path (p := x0)).
      eapply
      tcrush.
    1-3: admit.
    eapply (iT_Sub_nocoerce) => /=; hideCtx.
    + repeat first [var | typconstructor | tcrush].
    + ettrans; first last.
      eapply iSub_Sel'; first last.
      * constructor; varsub.
        ltcrush.
      * tcrush.
      * tcrush; last apply Bind1; tcrush.
        eapply (iSub_Trans (T2 := ⊤)); tcrush.
        eapply iSub_Sel'; tcrush.
        varsub; tcrush.

Qed.

Example fromPDotPaperTypesAbsTyp :
  TLater fromPDotPaperAbsTBody :: [] u⊢ₜ
    fromPDotPaperTypesV : μ fromPDotPaperAbsTypesTBody.
Proof.
  eapply iT_Sub_nocoerce; first exact: fromPDotPaperTypesTyp; ltcrush.
  eapply iSub_Sel', (path_tp_delay (i := 0)); wtcrush.
  varsub; tcrush.
Qed.

Example fromPDotPaperSymbolsTyp :
  TLater fromPDotPaperAbsTBody :: [] u⊢ₜ
    fromPDotPaperSymbolsV : μ fromPDotPaperSymbolsTBody.
Proof.
  tcrush.
  - eapply (iT_Sub_nocoerce) => /=; hideCtx.
    + repeat first [var | typconstructor | tcrush].
    + ettrans; first last.
      eapply iSub_Sel'; first last.
      * constructor; varsub; tcrush.
      * tcrush.
      * mltcrush.
Qed.

Example fromPDotPaperSymbolsAbsTyp :
  TLater fromPDotPaperAbsTBody :: [] u⊢ₜ
    fromPDotPaperSymbolsV : μ fromPDotPaperAbsSymbolsTBody.
Proof.
  eapply iT_Sub_nocoerce; first exact: fromPDotPaperSymbolsTyp; tcrush.
  lThis.
Qed.

Example fromPDotPaperTyp : [] u⊢ₜ fromPDotPaper : μ fromPDotPaperAbsTBody.
Proof.
  pose proof fromPDotPaperTypesAbsTyp.
  pose proof fromPDotPaperSymbolsAbsTyp.
  tcrush.
Qed.

Definition getAnyTypeT : ty :=
  TAll (μ fromPDotPaperAbsTBody) (⊤ →: p0 @ "types" @; "TypeTop").
Definition getAnyType : vl := vabs (tskip (tproj (tproj x0 "types") "newTypeTop")).

Ltac simplSubst := rewrite /= /up/= /ids/ids_vl/=.

Definition fromPDotPaperAbsTypesTBodySubst : ty := {@
  type "Type" >: ⊥ <: ⊤;
  type "TypeTop" >: ⊥ <: x0 @ "types" @; "Type";
  val "newTypeTop" : ⊤ →: x0 @ "types" @; "TypeTop";
  type "TypeRef" >: ⊥ <: TAnd (x0 @ "types" @; "Type") {@
    val "symb" : x0 @ "symbols" @; "Symbol"
  };
  val "newTypeRef" : x0 @ "symbols" @; "Symbol" →: x0 @ "types" @; "TypeRef"
}.

Lemma fromPDotPSubst: fromPDotPaperAbsTypesTBody .Tp[ (p0 @ "types") /]~ fromPDotPaperAbsTypesTBodySubst.
Proof. exact: psubst_ty_rtc_sufficient. Qed.

Example getAnyTypeFunTyp Γ : Γ u⊢ₜ getAnyType : getAnyTypeT.
Proof.
  rewrite /getAnyType -(iterate_S tskip 0); tcrush.
  eapply (iT_Sub (T1 := TLater (⊤ →: p0 @ "types" @; "TypeTop"))); tcrush.
  set Γ' := shift (μ fromPDotPaperAbsTBody) :: Γ.
  have Hpx: Γ' u⊢ₚ p0 @ "types" : μ fromPDotPaperAbsTypesTBody, 0
    by tcrush; eapply iT_Sub_nocoerce;
      [ by eapply iT_Mu_E; first var; stcrush | tcrush].
  have HpxSubst: Γ' u⊢ₚ p0 @ "types" : fromPDotPaperAbsTypesTBodySubst, 0.
  by eapply (iP_Mu_E (T := fromPDotPaperAbsTypesTBody)
    (p := p0 @ "types")), Hpx; tcrush.
  eapply (iT_Path (p := p0)), iP_Fld_I, (iP_Sub (i := 0)), HpxSubst.
  ltcrush.
Qed.

Example getAnyTypeTyp0 :
  [μ fromPDotPaperAbsTBody] u⊢ₜ
    getAnyType $: x0 $: () : p0 @ "types" @; "TypeTop".
Proof.
  eapply (iT_All_E (T1 := ⊤)), iT_Sub_nocoerce; tcrush.
  eapply iT_All_Ex'; [exact: getAnyTypeFunTyp|var|tcrush..].
Qed.

(*
lett (tv fromPDotPaper) (tapp (tv getAnyType) x0) : (pv fromPDotPaper @ "types" @; "Type").
Example getAnyTypeTyp : [] u⊢ₜ lett (tv fromPDotPaper) (tapp (tv getAnyType) x0) : (pv fromPDotPaper @ "types" @; "Type").
Proof.
  eapply (iT_All_Ex_p (pv _)); [| eapply getAnyTypeFunTyp|].

Example getAnyTypeTyp : [] u⊢ₜ tapp (tv getAnyType) (tv fromPDotPaper) : (pv fromPDotPaper @ "types" @; "Type").
Proof.
  eapply (iT_All_Ex_p (pv _)); [| eapply getAnyTypeFunTyp|].
iT_Let
  2: apply (iT_Path (pv fromPDotPaper)). fromPDotPaperTyp. ;
  (* Wanted: application of functions to paths;  *)
Abort. *)
