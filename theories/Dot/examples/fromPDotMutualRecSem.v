(**
 *)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra.
From D.Dot Require Import hoas typingExInfra.
From D.Dot.typing Require Import typing_storeless.
From D.Dot Require Import primOption typingExamples.
(* From D.Dot Require Import scalaLib.
From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived. *)
Import DBNotation.

Set Implicit Arguments.
Set Suggest Proof Using.
Set Default Proof Using "Type".

Implicit Types (g : stys).

Section semExample.
(** FromPDotPaper *)
Context {g}.

Definition typeRefTBody : ty := {@
  val "symb" : x1 @ "symbols" @; "Symbol"
}.

Definition fromPDotPaperTypesTBody : ty := {@
  typeEq "Type" ⊤;
  typeEq "TypeTop" ⊤;
  val "newTypeTop" : ⊤ →: x0 @; "TypeTop";
  typeEq "TypeRef" $ TAnd (x0 @; "Type") typeRefTBody;
  val "AnyType" : ▶: (x0 @; "Type");
  val "newTypeRef" : x1 @ "symbols" @; "Symbol" →: x0 @; "TypeRef"
}.

Definition fromPDotPaperAbsTypesTBody : ty := {@
  type "Type" >: ⊥ <: TTop;
  type "TypeTop" >: ⊥ <: x0 @; "Type";
  val "newTypeTop" : ⊤ →: x0 @; "TypeTop";
  type "TypeRef" >: ⊥ <: TAnd (p0 @; "Type") typeRefTBody;
  val "AnyType" : ▶: (x0 @; "Type");
  val "newTypeRef" : x1 @ "symbols" @; "Symbol" →: x0 @; "TypeRef"
}.

Definition pTop : stampTy := MkTy 40 [] ⊤ 0.
Lemma pTopStamp : TyMemStamp g pTop. Proof. split; stcrush. Qed.
Context (Htop : styConforms g pTop).

Definition pTypeRef : stampTy := MkTy 50 [x0; x1] (TAnd (x0 @; "Type") typeRefTBody) 2.
Lemma pTypeRefStamp : TyMemStamp g pTypeRef. Proof. split; stcrush. Qed.
Context (HtypeRef : styConforms g pTypeRef).

Definition pSymbol : stampTy := MkTy 60 [x0; x1] {@
  val "tpe" : x1 @ "types" @; "Type";
  val "id" : TNat
} 2.
Lemma pSymbolStamp : TyMemStamp g pSymbol. Proof. split; stcrush. Qed.
Context (Hsymbol : styConforms g pSymbol).

(* Import AssertPlain.
From D.Dot Require Import hoas. *)
Definition fromPDotPaperTypesV : vl := ν {@
  type "Type" =[ pTop ];
  type "TypeTop" =[ pTop ];
  val "newTypeTop" = vabs (ν {@ });
  type "TypeRef" =[ pTypeRef ];
  val "AnyType" = ν {@ };
  val "newTypeRef" = vabs (
    ν {@
      val "symb" = x1
    })
}.

Definition fromPDotPaperSymbolsTBody : ty := {@
  typeEq "Symbol" $ {@
    val "tpe" : x1 @ "types" @; "Type";
    val "id" : TNat
  }%ty;
  val "newSymbol" : x1 @ "types" @; "Type" →: TNat →: x0 @; "Symbol"
}.

Definition fromPDotPaperAbsSymbolsTBody : ty := {@
  type "Symbol" >: ⊥ <: {@
    val "tpe" : x1 @ "types" @; "Type";
    val "id" : TNat
  };
  val "newSymbol" : x1 @ "types" @; "Type" →: TNat →: x0 @; "Symbol"
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
  type "Symbol" =[ pSymbol ];
  val "newSymbol" = (vabs $ vabs $ ν {@
    val "tpe" = x2;
    val "id" = x1
  })
}.

Definition fromPDotPaper : vl := ν {@
  val "types" = fromPDotPaperTypesV;
  val "symbols" = fromPDotPaperSymbolsV
}.

Ltac hideCtx := idtac.

Example fromPDotPaperTypesTyp :
  TLater fromPDotPaperAbsTBody :: [] v⊢ₜ[g]
    fromPDotPaperTypesV : μ fromPDotPaperTypesTBody.
Proof using Htop HtypeRef.
  tcrush; try by [eapply Dty_typed; tcrush; by_extcrush].
  - eapply (Subs_typed_nocoerce) => /=; hideCtx.
    + repeat first [var | typconstructor | tcrush].
    + apply (Trans_stp (T2 := ⊤) (i2 := 0)); first tcrush.
      eapply LSel_stp'; last (tcrush; varsub); ltcrush.
  - eapply (Subs_typed_nocoerce (TMu ⊤)); first tcrush.
    eapply (Trans_stp (T2 := ⊤) (i2 := 0)); tcrush.
    eapply (Trans_stp (i2 := 1)); [exact: AddI_stp | ].
    asideLaters.
    eapply (LSel_stp' _ ⊤); tcrush.
    varsub; apply Sub_later_shift; tcrush.
  - eapply (Subs_typed_nocoerce) => /=; hideCtx.
    + repeat first [var | typconstructor | tcrush].
    + ettrans; first last.
      eapply LSel_stp'; first last.
      * constructor; varsub.
        ltcrush.
      * tcrush.
      * tcrush.
        eapply (Trans_stp (T2 := ⊤)); tcrush.
        eapply LSel_stp'; tcrush.
        varsub; tcrush.
Qed.

Example fromPDotPaperTypesAbsTyp :
  TLater fromPDotPaperAbsTBody :: [] v⊢ₜ[g]
    fromPDotPaperTypesV : μ fromPDotPaperAbsTypesTBody.
Proof using Htop HtypeRef.
  eapply Subs_typed_nocoerce; first exact: fromPDotPaperTypesTyp; ltcrush.
  eapply LSel_stp'; tcrush.
  varsub; tcrush.
Qed.

Example fromPDotPaperSymbolsTyp :
  TLater fromPDotPaperAbsTBody :: [] v⊢ₜ[g]
    fromPDotPaperSymbolsV : μ fromPDotPaperSymbolsTBody.
Proof using Hsymbol.
  tcrush.
  - eapply Dty_typed; tcrush; by_extcrush.
  - eapply (Subs_typed_nocoerce) => /=; hideCtx.
    + repeat first [var | typconstructor | tcrush].
    + ettrans; first last.
      eapply LSel_stp'; first last.
      * constructor; varsub; tcrush.
      * tcrush.
      * mltcrush.
Qed.

Example fromPDotPaperSymbolsAbsTyp :
  TLater fromPDotPaperAbsTBody :: [] v⊢ₜ[g]
    fromPDotPaperSymbolsV : μ fromPDotPaperAbsSymbolsTBody.
Proof using Hsymbol.
  eapply Subs_typed_nocoerce; first exact: fromPDotPaperSymbolsTyp; tcrush.
  lThis.
Qed.

Example fromPDotPaperTyp : [] v⊢ₜ[g] fromPDotPaper : μ fromPDotPaperAbsTBody.
Proof using All.
  pose proof fromPDotPaperTypesAbsTyp.
  pose proof fromPDotPaperSymbolsAbsTyp.
  tcrush.
Qed.

Definition getAnyTypeT : ty :=
  TAll (μ fromPDotPaperAbsTBody) (p0 @ "types" @; "Type").
Definition getAnyType : vl := vabs (tskip (tproj (tproj x0 "types") "AnyType")).

Ltac simplSubst := rewrite /= /up/= /ids/ids_vl/=.
From D.Dot.syn Require Import path_repl.

Definition fromPDotPaperAbsTypesTBodySubst : ty := {@
  type "Type" >: ⊥ <: ⊤;
  type "TypeTop" >: ⊥ <: x0 @ "types" @; "Type";
  val "newTypeTop" : ⊤ →: x0 @ "types" @; "TypeTop";
  type "TypeRef" >: ⊥ <: TAnd (x0 @ "types" @; "Type") {@
    val "symb" : x0 @ "symbols" @; "Symbol"
  };
  val "AnyType" : ▶: (x0 @ "types" @; "Type");
  val "newTypeRef" : x0 @ "symbols" @; "Symbol" →: x0 @ "types" @; "TypeRef"
}.

Lemma fromPDotPSubst: fromPDotPaperAbsTypesTBody .Tp[ (p0 @ "types") /]~ fromPDotPaperAbsTypesTBodySubst.
Proof. exact: psubst_ty_rtc_sufficient. Qed.

Example getAnyTypeFunTyp Γ : Γ v⊢ₜ[g] getAnyType : getAnyTypeT.
Proof.
  rewrite /getAnyType -(iterate_S tskip 0); tcrush.
  eapply (Subs_typed (T1 := TLater (p0 @ "types" @; "Type"))); tcrush.
  set Γ' := shift (μ fromPDotPaperAbsTBody) :: Γ.
  have Hpx: Γ' v⊢ₚ[g] p0 @ "types" : μ fromPDotPaperAbsTypesTBody, 0
    by tcrush; eapply Subs_typed_nocoerce;
      [ by eapply TMuE_typed; first var; stcrush | tcrush].
  have HpxSubst: Γ' v⊢ₚ[g] p0 @ "types" : fromPDotPaperAbsTypesTBodySubst, 0.
  by eapply (p_mu_e_typed (T := fromPDotPaperAbsTypesTBody)
    (p := p0 @ "types")), Hpx; tcrush; exact: fromPDotPSubst.
  eapply (Path_typed (p := p0)), pself_inv_typed, (p_subs_typed (i := 0)), HpxSubst.
  repeat lNext.
Qed.

Example getAnyTypeTyp0 :
  [μ fromPDotPaperAbsTBody] v⊢ₜ[g]
    tapp getAnyType x0 : p0 @ "types" @; "Type".
Proof. eapply Appv_typed'; [exact: getAnyTypeFunTyp|var|tcrush..]. Qed.
(*
lett (tv fromPDotPaper) (tapp (tv getAnyType) x0) : (pv fromPDotPaper @ "types" @; "Type").
Example getAnyTypeTyp : [] u⊢ₜ lett (tv fromPDotPaper) (tapp (tv getAnyType) x0) : (pv fromPDotPaper @ "types" @; "Type").
Proof.
  eapply (App_path_typed (pv _)); [| eapply getAnyTypeFunTyp|].

Example getAnyTypeTyp : [] u⊢ₜ tapp (tv getAnyType) (tv fromPDotPaper) : (pv fromPDotPaper @ "types" @; "Type").
Proof.
  eapply (App_path_typed (pv _)); [| eapply getAnyTypeFunTyp|].
Let_typed
  2: apply (Path_typed (pv fromPDotPaper)). fromPDotPaperTyp. ;
  (* Wanted: application of functions to paths;  *)
Abort. *)
