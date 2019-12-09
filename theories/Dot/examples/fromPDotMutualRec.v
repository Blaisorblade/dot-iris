(**
 *)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra unstampedness_binding scalaLib.
From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived.
Import DBNotation.

(** FromPDotPaper *)

Definition fromPDotPaperTypesTBody : ty := {@
  typeEq "Type" TTop;
  typeEq "TypeRef" $ TAnd (p0 @; "Type") {@
    val "symb" : p1 @ "symbols" @; "Symbol"
  };
  val "AnyType" : TLater (p0 @; "Type");
  val "newTypeRef" : p1 @ "symbols" @; "Symbol" →: p0 @; "TypeRef"
}.

Definition fromPDotPaperAbsTypesTBody : ty := {@
  type "Type" >: TBot <: TTop;
  type "TypeRef" >: TBot <: TAnd (p0 @; "Type") {@
    val "symb" : p1 @ "symbols" @; "Symbol"
  };
  val "AnyType" : TLater (p0 @; "Type");
  val "newTypeRef" : p1 @ "symbols" @; "Symbol" →: p0 @; "TypeRef"
}.

Definition fromPDotPaperTypesV : vl := ν {@
  type "Type" = TTop;
  type "TypeRef" = TAnd (p0 @; "Type") {@
    val "symb" : p1 @ "symbols" @; "Symbol"
  };
  val "AnyType" = vnat 0 ; (* ν {@}; *)
  val "newTypeRef" = (vabs $ tv $ ν {@
    val "symb" = x1
  })
}.

Definition fromPDotPaperSymbolsTBody : ty := {@
  typeEq "Symbol" $ {@
    val "tpe" : p1 @ "types" @; "Type";
    val "name" : HashableString
  }%ty;
  val "newSymbol" : p1 @ "types" @; "Type" →: HashableString →: p0 @; "Symbol"
}.

Definition fromPDotPaperAbsSymbolsTBody : ty := {@
  type "Symbol" >: TBot <: {@
    val "tpe" : p1 @ "types" @; "Type";
    val "name" : HashableString
  };
  val "newSymbol" : p1 @ "types" @; "Type" →: HashableString →: p0 @; "Symbol"
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
    val "tpe" : p1 @ "types" @; "Type";
    val "name" : HashableString
  };
  val "newSymbol" = (vabs $ tv $ vabs $ tv $ ν {@
    val "tpe" = x2;
    val "name" = x1
  })
}.

Definition fromPDotPaper : vl := ν {@
  val "types" = fromPDotPaperTypesV;
  val "symbols" = fromPDotPaperSymbolsV
}.

Example fromPDotPaperTypesTyp :
  TLater fromPDotPaperAbsTBody :: [] u⊢ₜ
    tv fromPDotPaperTypesV : μ fromPDotPaperTypesTBody.
Proof.
  tcrush.
  - eapply (Subs_typed_nocoerce TNat); first tcrush.
    eapply (Trans_stp (T2 := TTop) (i2 := 0)); tcrush.
    eapply (Trans_stp (i2 := 1)); [exact: AddI_stp | ].
    asideLaters.
    eapply (LSel_stp' _ ⊤); tcrush.
    varsub; apply Sub_later_shift; tcrush.
  - eapply (Subs_typed_nocoerce) => /=; hideCtx.
    + repeat first [var | typconstructor | tcrush].
    + ettrans; first last.
      eapply LSel_stp'; first last.
      * constructor; varsub.
        lNext.
      * tcrush.
      * tcrush; last apply Bind1; tcrush.
        eapply (Trans_stp (T2 := ⊤)); tcrush.
        eapply LSel_stp'; tcrush.
        varsub; tcrush.
Qed.

Example fromPDotPaperTypesAbsTyp :
  TLater fromPDotPaperAbsTBody :: [] u⊢ₜ
    tv fromPDotPaperTypesV : μ fromPDotPaperAbsTypesTBody.
Proof.
  eapply Subs_typed_nocoerce; first exact: fromPDotPaperTypesTyp; tcrush.
  lThis.
  lNext; lThis.
  all: repeat lNext.
Qed.

Example fromPDotPaperSymbolsTyp :
  TLater fromPDotPaperAbsTBody :: [] u⊢ₜ
    tv fromPDotPaperSymbolsV : μ fromPDotPaperSymbolsTBody.
Proof.
  tcrush.
  - eapply (Subs_typed_nocoerce) => /=; hideCtx.
    + repeat first [var | typconstructor | tcrush].
    + ettrans; first last.
      eapply LSel_stp'; first last.
      * constructor; varsub; tcrush.
      * tcrush.
      * tcrush; apply Bind1; tcrush. repeat lNext.
Qed.

Example fromPDotPaperSymbolsAbsTyp :
  TLater fromPDotPaperAbsTBody :: [] u⊢ₜ
    tv fromPDotPaperSymbolsV : μ fromPDotPaperAbsSymbolsTBody.
Proof.
  eapply Subs_typed_nocoerce; first exact: fromPDotPaperSymbolsTyp; tcrush.
  lThis.
Qed.

Example fromPDotPaperTyp : [] u⊢ₜ tv fromPDotPaper : μ fromPDotPaperAbsTBody.
Proof.
  pose proof fromPDotPaperTypesAbsTyp.
  pose proof fromPDotPaperSymbolsAbsTyp.
  tcrush.
Qed.

Definition getAnyTypeT : ty :=
  TAll (μ fromPDotPaperAbsTBody) (p0 @ "types" @; "Type").
Definition getAnyType : vl := vabs (tskip (tproj (tproj (tv x0) "types") "AnyType")).

Ltac simplSubst := rewrite /= /up/= /ids/ids_vl/=.
From D.Dot.syn Require Import path_repl.

Definition fromPDotPaperAbsTypesTBodySubst : ty := {@
  type "Type" >: ⊥ <: ⊤;
  type "TypeRef" >: ⊥ <: TAnd (p0 @ "types" @; "Type") {@
    val "symb" : p0 @ "symbols" @; "Symbol"
  };
  val "AnyType" : TLater (p0 @ "types" @; "Type");
  val "newTypeRef" : p0 @ "symbols" @; "Symbol" →: p0 @ "types" @; "TypeRef"
}.

Lemma fromPDotPSubst: fromPDotPaperAbsTypesTBody .Tp[ (p0 @ "types") /]~ fromPDotPaperAbsTypesTBodySubst.
Proof. exact: psubst_ty_rtc_sufficient. Qed.

Example getAnyTypeFunTyp Γ : Γ u⊢ₜ tv getAnyType : getAnyTypeT.
Proof.
  rewrite /getAnyType -(iterate_S tskip 0); tcrush.
  eapply (Subs_typed (T1 := TLater (p0 @ "types" @; "Type"))); tcrush.
  set Γ' := shift (μ fromPDotPaperAbsTBody) :: Γ.
  have Hpx: Γ' u⊢ₚ p0 @ "types" : μ fromPDotPaperAbsTypesTBody, 0.
    by tcrush; eapply Subs_typed_nocoerce;
      [by eapply TMuE_typed, Var_typed' | tcrush].
  have HpxSubst: Γ' u⊢ₚ p0 @ "types" : fromPDotPaperAbsTypesTBodySubst, 0.
    by eapply p_mu_e_typed; [apply fromPDotPSubst|tcrush|].
  eapply (Path_typed (p := p0)), pself_inv_typed, (p_subs_typed (i := 0)), HpxSubst.
  repeat lNext.
Qed.

Example getAnyTypeTyp0 :
  [μ fromPDotPaperAbsTBody] u⊢ₜ
    tapp (tv getAnyType) (tv x0) : p0 @ "types" @; "Type".
Proof. eapply Appv_typed'; by [exact: getAnyTypeFunTyp|var|]. Qed.
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
