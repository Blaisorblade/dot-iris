(**
WIP examples constructing _unstamped_ syntactic typing derivations.
 *)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra unstampedness_binding scalaLib.
From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived.
Import DBNotation.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Example ex0 e Γ T:
  Γ u⊢ₜ e : T →
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ e : ⊤.
Proof. intros. apply (Subs_typed_nocoerce T TTop); tcrush. Qed.

Example ex1 Γ n T:
  Γ u⊢ₜ tv (ν {@ val "a" = vnat n}) : μ {@ val "a" : TNat }.
Proof.
  (* Help proof search: Avoid trying TMuI_typed, that's slow. *)
  apply VObj_typed; tcrush.
Qed.

Example ex2 Γ T :
  Γ u⊢ₜ tv (ν {@ type "A" = p0 @; "B" } ) : TMu (TAnd (TTMem "A" TBot TTop) TTop).
Proof. apply VObj_typed; tcrush. Qed.

(* Try out fixpoints. *)
Definition F3 T :=
  TMu (TAnd (TTMem "A" T T) TTop).

Example ex3 Γ T:
  Γ u⊢ₜ tv (ν {@ type "A" = F3 (p0 @; "A") } ) : F3 (F3 (TSel p0 "A")).
Proof. apply VObj_typed; tcrush. Qed.

Definition KeysT : ty := μ {@
  type "Key" >: ⊥ <: ⊤;
  val "key": HashableString →: p0 @; "Key"
}.
Definition hashKeys : vl := ν {@
  type "Key" = TNat;
  val "key" = vabs (tapp (tproj (tv x0) "hashCode") tUnit)
}.

Definition KeysT' := μ {@
  type "Key" >: TNat <: ⊤;
  val "key" : HashableString →: p0 @; "Key"
}.

(* IDEA for our work: use [(type "Key" >: TNat <: ⊤) ⩓ (type "Key" >: ⊥ <: ⊤)]. *)
Example hashKeys_typed Γ:
  Γ u⊢ₜ tv hashKeys : KeysT.
Proof.
  cut (Γ u⊢ₜ tv hashKeys : KeysT').
  { intros H.
    apply (Subs_typed_nocoerce KeysT'); first done.
    apply Mu_stp_mu; last stcrush.
    tcrush.
    lThis.
  }
  apply VObj_typed; tcrush.
  cbn; apply App_typed with (T1 := TUnit);
    last eapply (Subs_typed_nocoerce TNat); tcrush; cbn.

  pose (T0 := μ {@ val "hashCode" : ⊤ →: 𝐍 }).

  have Htp: ∀ Γ', T0 :: Γ' u⊢ₜ tv x0 : val "hashCode" : ⊤ →: TNat. {
    intros. eapply Subs_typed_nocoerce.
    eapply TMuE_typed'; by [var|].
    by apply TAnd1_stp; tcrush.
  }
  apply (Subs_typed_nocoerce (val "hashCode" : ⊤ →: 𝐍)). exact: Htp.
  tcrush.
  eapply LSel_stp'; tcrush.
  varsub; tcrush.
Qed.

(* FromPDotPaper *)

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

(* We can also use subtyping on the individual members to type this example. *)
Definition boolImplT0 : ty :=
  μ {@
    typeEq "Boolean" IFT;
    val "true" : TLater p0Bool;
    val "false" : TLater p0Bool
  }.

Example boolImplTypAlt Γ :
  Γ u⊢ₜ tv boolImplV : boolImplT.
Proof.
  apply (Subs_typed_nocoerce boolImplT0);
    last (tcrush; lThis).
  tcrush.
  - eapply Subs_typed_nocoerce; [apply iftTrueTyp|apply SubIFT_LaterP0Bool].
  - eapply Subs_typed_nocoerce; [apply iftFalseTyp|apply SubIFT_LaterP0Bool].
Qed.

(* Utilities needed for not. *)
Lemma subIFT i Γ T:
  is_unstamped_ty (length Γ) T.|[ren (+i)] →
  (typeEq "A" T.|[ren (+1+i)]) :: Γ u⊢ₜ IFTBody, 0 <:
    TAll T.|[ren (+1+i)] (TAll T.|[ren (+2+i)] (▶ T.|[ren (+3+i)])), 0.
Proof.
  rewrite /= -/IFTBody => HsT1.
  move: (HsT1) => /is_unstamped_ren1_ty HsT2; rewrite -hrenS in HsT2.
  move: (HsT2) => /is_unstamped_ren1_ty HsT3; rewrite -hrenS in HsT3.
  tcrush; rewrite ?iterate_S ?iterate_0 /=;
    first [apply: LSel_stp' | apply: SelU_stp]; tcrush; apply: Var_typed';
    rewrite ?hsubst_id //; by [| autosubst].
Qed.

Lemma tyAppIFT_typed Γ T t :
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ t : IFT →
  Γ u⊢ₜ tyApp "A" t T : T →: T →: ▶ T.
Proof.
  move => HsT1 Ht; move: (HsT1) => /is_unstamped_ren1_ty HsT2.
  intros; eapply tyApp_typed => //; last stcrush.
  intros; rewrite /= !(hren_upn_gen 1) !(hren_upn_gen 2) /up /=.
  exact: (subIFT 1).
Qed.

(** Adds a skip needed for booleans. *)
(* Beware: we could inline the [lett t], but then we'd need to use a weakening lemma
to prove [iftCoerce_typed]. *)
Definition iftCoerce t :=
  lett t (vabs' (vabs' (tskip (tapp (tapp (tv x2) (tv x1)) (tv x0))))).

Lemma iftCoerce_typed Γ t T :
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ t: T →: T →: ▶ T →
  Γ u⊢ₜ iftCoerce t : T →: T →: T.
Proof.
  move => HsT1 Ht.
  move: (HsT1) => /is_unstamped_ren1_ty HsT2.
  move: (HsT2) => /is_unstamped_ren1_ty; rewrite -hrenS => HsT3.
  move: (HsT3) => /is_unstamped_ren1_ty; rewrite -hrenS => HsT4.
  eapply Let_typed; [exact: Ht| |rewrite /= !(hren_upn 1); tcrush].
  rewrite /= !(hren_upn_gen 1) (hren_upn_gen 2) /=.
  tcrush; rewrite -!hrenS -(iterate_S tskip 0).
  eapply (Subs_typed (T1 := ▶T.|[_])); first tcrush.
  repeat (eapply App_typed; last var).
  apply: Var_typed' => //.
  rewrite /= !(hren_upn 1) (hren_upn_gen 1) (hren_upn_gen 2)
    !hsubst_comp !ren_ren_comp /=. done.
Qed.

Lemma iftCoerce_tyAppIFT_typed Γ T t :
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ t : IFT →
  Γ u⊢ₜ iftCoerce (tyApp "A" t T) : T →: T →: T.
Proof. intros. by apply /iftCoerce_typed /tyAppIFT_typed. Qed.

Lemma iftCoerce_tyAppIFT_typed_IFT Γ t :
  Γ u⊢ₜ t : IFT →
  Γ u⊢ₜ iftCoerce (tyApp "A" t IFT) : IFT →: IFT →: IFT.
Proof. intros. apply iftCoerce_tyAppIFT_typed; tcrush. Qed.

Definition iftNotBody t T true false :=
  tapp (tapp
      (iftCoerce (tyApp "A" t T))
    false)
  true.

(* XXX Beware that false and true are inlined here. *)
Lemma iftNotBodyTyp Γ t :
  Γ u⊢ₜ t : IFT →
  Γ u⊢ₜ iftNotBody t IFT (tv iftTrue) (tv iftFalse) : IFT.
Proof.
  intros.
  eapply App_typed; last exact: iftTrueTyp.
  eapply App_typed; last exact: iftFalseTyp.
  exact: iftCoerce_tyAppIFT_typed_IFT.
Qed.

(* We'd want NOT = λ a. a False True. *)
(* This is NOT0 = λ a. a (λ t f. f) (λ t f. t). *)
Definition iftNot0 := vabs' (iftNotBody (tv x0) IFT (tv iftTrue) (tv iftFalse)).
Lemma iftNotTyp Γ T :
  Γ u⊢ₜ iftNot0 : TAll IFT IFT.
Proof. apply Lam_typed; first stcrush. apply iftNotBodyTyp. var. Qed.

(* AND = λ a b. a b False. *)
Definition iftAndBody t1 t2 T false :=
  tapp (tapp
      (iftCoerce (tyApp "A" t1 T))
    t2)
  false.

Lemma iftAndBodyTyp Γ t1 t2 :
  Γ u⊢ₜ t1 : IFT →
  Γ u⊢ₜ t2 : IFT →
  Γ u⊢ₜ iftAndBody t1 t2 IFT (tv iftFalse) : IFT.
Proof.
  intros Ht1 Ht2.
  eapply App_typed; last exact: iftFalseTyp.
  eapply App_typed; last exact: Ht2.
  exact: iftCoerce_tyAppIFT_typed_IFT.
Qed.

Lemma iftAndTyp Γ T :
  Γ u⊢ₜ vabs' (vabs' (iftAndBody (tv x1) (tv x0) IFT (tv iftFalse))) : IFT →: IFT →: IFT.
Proof. tcrush. apply iftAndBodyTyp; var. Qed.

(*
let bool = boolImplV :
  μ { Boolean: IFT..IFT; true : b.Boolean; false : b.Boolean;
      and : p.Boolean →: p.Boolean →: p.Boolean }
*)

Definition IFTp0 : ty := p0Bool →: p0Bool →: p0Bool.

Lemma iftCoerce_tyAppIFT_typed_p0Boolean Γ T t :
  T :: Γ u⊢ₜ t : IFT →
  T :: Γ u⊢ₜ iftCoerce (tyApp "A" t p0Bool) : p0Bool →: p0Bool →: p0Bool.
Proof. intros. apply iftCoerce_tyAppIFT_typed; tcrush. Qed.
