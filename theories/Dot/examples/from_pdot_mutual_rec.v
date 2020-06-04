(** * Motivating example, syntactic version.

This example is called in code [fromPDotPaper], because it is indeed inspired
by the pDOT paper.

Here, the main lemma is [fromPDotPaperTyp], saying that
[fromPDotPaper x0] has type [μ (fromPDotPaperAbsTBody x1)].
Moreover, [pCoreTyp] shows that
[lett hoptionModV (fromPDotPaper x0)] is well-typed.
*)

From D Require Import tactics.
From D.Dot Require Import syn path_repl.
From D.Dot.typing Require Import old_unstamped_typing old_unstamped_typing_derived_rules.
From D.Dot Require Import hoas ex_utils scala_lib.
Import DBNotation.

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
  type "TypeRef" >: ⊥ <: TAnd (x0 @; "Type") typeRefTBody;
  val "newTypeRef" : x1 @ "symbols" @; "Symbol" →: x0 @; "TypeRef"
}.

(* Import AssertPlain.
From D.Dot Require Import hoas. *)
Definition fromPDotPaperTypesV : vl := ν {@
  type "Type" = TTop;
  type "TypeTop" = TTop;
  val "newTypeTop" = vabs (ν {@ });
  type "TypeRef" = TAnd (x0 @; "Type") typeRefTBody;
  val "newTypeRef" = vabs (
    ν {@
      val "symb" = x1
    })
}.

Definition optionTy pOpt pCore :=
  TAnd (pOpt @; "Option") (type "T" >: ⊥ <: (pCore @ "types" @; "Type")).

Definition fromPDotPaperSymbolsTBody pOpt : ty := {@
  typeEq "Symbol" $ {@
    val "tpe" : optionTy pOpt x1;
    val "id" : TInt
  }%ty;
  val "newSymbol" : optionTy pOpt x1 →: TInt →: x0 @; "Symbol"
}.

Definition fromPDotPaperAbsSymbolsTBody pOpt : ty := {@
  type "Symbol" >: ⊥ <: {@
    val "tpe" : optionTy pOpt x1;
    val "id" : TInt
  };
  val "newSymbol" : optionTy pOpt x1 →: TInt →: x0 @; "Symbol"
}.

Definition fromPDotPaperTBody pOpt : ty := {@
  val "types" : μ fromPDotPaperTypesTBody;
  val "symbols" : μ (fromPDotPaperSymbolsTBody (shift pOpt))
}.

Definition fromPDotPaperAbsTBody pOpt : ty := {@
  val "types" : μ fromPDotPaperAbsTypesTBody;
  val "symbols" : μ (fromPDotPaperAbsSymbolsTBody (shift pOpt))
}.

Definition fromPDotPaperSymbolsV pOpt : vl := ν {@
  type "Symbol" = {@
    val "tpe" : optionTy (shift pOpt) x1;
    val "id" : TInt
  };
  val "newSymbol" = (vabs $ vabs $ ν {@
    val "tpe" = x2;
    val "id" = x1
  })
}.

Definition fromPDotPaper pOpt : vl := ν {@
  val "types" = fromPDotPaperTypesV;
  val "symbols" = fromPDotPaperSymbolsV (shift pOpt)
}.

Example fromPDotPaperTypesTyp :
  TLater (fromPDotPaperAbsTBody x1) :: optionModT :: [] u⊢ₜ
    fromPDotPaperTypesV : μ fromPDotPaperTypesTBody.
Proof.
  tcrush.
  - eapply (iT_ISub_nocoerce) => /=; hideCtx.
    + repeat first [var | typconstructor | tcrush].
    + apply (iSub_Trans (T2 := ⊤) (i2 := 0)); first tcrush.
      eapply iSub_Sel'; last (tcrush; varsub); ltcrush.
  - eapply (iT_ISub_nocoerce) => /=; hideCtx.
    + repeat first [var | typconstructor | tcrush].
    + ettrans; first last.
      eapply iSub_Sel'; first last.
      * typconstructor; varsub.
        ltcrush.
      * tcrush.
      * tcrush; last apply iSub_Bind_1; tcrush.
        eapply (iSub_Trans (T2 := ⊤)); tcrush.
        eapply iSub_Sel'; tcrush.
        varsub; tcrush.
Qed.

Example fromPDotPaperTypesAbsTyp :
  TLater (fromPDotPaperAbsTBody x1) :: optionModT :: [] u⊢ₜ
    fromPDotPaperTypesV : μ fromPDotPaperAbsTypesTBody.
Proof.
  eapply iT_ISub_nocoerce; first exact: fromPDotPaperTypesTyp; ltcrush.
  eapply iSub_Sel', (path_tp_delay (i := 0)); wtcrush.
  varsub; tcrush.
Qed.

Example fromPDotPaperSymbolsTyp :
  TLater (fromPDotPaperAbsTBody x1) :: optionModT :: [] u⊢ₜ
    fromPDotPaperSymbolsV x1 : μ (fromPDotPaperSymbolsTBody x2).
Proof.
  tcrush.
  - eapply (iT_ISub_nocoerce) => /=; hideCtx.
    + repeat first [var | typconstructor | tcrush].
    + ettrans; first last.
      eapply iSub_Sel'; first last.
      * typconstructor; varsub; tcrush.
      * tcrush.
      * mltcrush.
Qed.

Example fromPDotPaperSymbolsAbsTyp :
  TLater (fromPDotPaperAbsTBody x1) :: optionModT :: [] u⊢ₜ
    fromPDotPaperSymbolsV x1 : μ (fromPDotPaperAbsSymbolsTBody x2).
Proof.
  eapply iT_ISub_nocoerce; first exact: fromPDotPaperSymbolsTyp; tcrush.
  lThis.
Qed.

Example fromPDotPaperTyp : optionModT :: [] u⊢ₜ fromPDotPaper x0 : μ (fromPDotPaperAbsTBody x1).
Proof.
  pose proof fromPDotPaperTypesAbsTyp.
  pose proof fromPDotPaperSymbolsAbsTyp.
  tcrush.
Qed.

Example pCoreTyp : [] u⊢ₜ lett hoptionModV (fromPDotPaper x0) : ⊤.
Proof.
  eapply iT_All_E, optionModTyp; tcrush.
  eapply (iT_ISub (i := 0)), fromPDotPaperTyp; tcrush.
Qed.

Definition getAnyTypeT pOpt : ty :=
  TAll (μ (fromPDotPaperAbsTBody (shift pOpt))) (⊤ →: x0 @ "types" @; "TypeTop").
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

Lemma fromPDotPSubst: fromPDotPaperAbsTypesTBody .Tp[ (x0 @ "types") /]~ fromPDotPaperAbsTypesTBodySubst.
Proof. exact: psubst_ty_rtc_sufficient. Qed.

Example getAnyTypeFunTyp Γ T : T :: optionModT :: Γ u⊢ₜ getAnyType : getAnyTypeT x1.
Proof.
  rewrite /getAnyType -(iterate_S tskip 0); tcrush.
  eapply (iT_ISub (T1 := TLater (⊤ →: x0 @ "types" @; "TypeTop"))); tcrush.
  set Γ' := shift (μ fromPDotPaperAbsTBody (shiftV x1)) :: T :: optionModT :: Γ.
  have Hpx: Γ' u⊢ₚ x0 @ "types" : μ fromPDotPaperAbsTypesTBody, 0
    by tcrush; eapply iT_ISub_nocoerce;
      [ by eapply iT_Mu_E; first var; stcrush | tcrush].
  have HpxSubst: Γ' u⊢ₚ x0 @ "types" : fromPDotPaperAbsTypesTBodySubst, 0.
  by eapply (iP_Mu_E (T := fromPDotPaperAbsTypesTBody)
    (p := x0 @ "types")), Hpx; tcrush.
  eapply iT_Path', iP_Fld_I, (iP_ISub (i := 0)), HpxSubst.
  ltcrush.
Qed.

Example getAnyTypeTyp0 :
  [μ (fromPDotPaperAbsTBody x2); optionModT] u⊢ₜ
    getAnyType $: x0 $: () : x0 @ "types" @; "TypeTop".
Proof.
  eapply (iT_All_E (T1 := ⊤)), iT_ISub_nocoerce; tcrush.
  eapply iT_All_Ex'; [exact: getAnyTypeFunTyp|var|tcrush..].
Qed.
