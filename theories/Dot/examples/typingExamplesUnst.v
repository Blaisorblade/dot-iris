(**
WIP examples constructing _unstamped_ syntactic typing derivations.
 *)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra unstampedness_binding.
From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived.

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

Notation HashableString := (μ {@ val "hashCode" : TAll TUnit TNat }).
Definition KeysT : ty := μ {@
  type "Key" >: ⊥ <: ⊤;
  val "key": TAll HashableString (p1 @; "Key")
}.
Definition hashKeys : vl := ν {@
  type "Key" = TNat;
  val "key" = vabs (tapp (tproj (tv x0) "hashCode") tUnit)
}.

Definition KeysT' := μ {@
  type "Key" >: TNat <: ⊤;
  val "key": TAll HashableString (p1 @; "Key")
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
    eapply Trans_stp; first apply TAnd1_stp; tcrush.
  }
  apply VObj_typed; tcrush.
  cbn; apply App_typed with (T1 := TUnit);
    last eapply (Subs_typed_nocoerce TNat); tcrush; cbn.

  pose (T0 := μ {@ val "hashCode" : TAll ⊤ 𝐍 }).

  have Htp: ∀ Γ', T0 :: Γ' u⊢ₜ tv x0 : val "hashCode" : TAll ⊤ TNat. {
    intros. eapply Subs_typed_nocoerce.
    eapply TMuE_typed'; by [exact: Var_typed'|].
    by apply TAnd1_stp; tcrush.
  }
  apply (Subs_typed_nocoerce (val "hashCode" : TAll ⊤ 𝐍)). exact: Htp.
  tcrush.
  eapply LSel_stp'; tcrush.
  eapply Var_typed_sub; by [|tcrush].
Qed.

(* Note how we must weaken the type (or its environment) to account for the
   self-variable of the created object. *)
Definition packTV T := (ν {@ type "A" = T.|[ren (+1)] }).

Lemma packTV_typed' T n Γ :
  is_unstamped_ty n T →
  n <= length Γ →
  Γ u⊢ₜ tv (packTV T) : typeEq "A" T.
Proof.
  move => HsT1 Hle; move: (Hle) (HsT1) => /le_n_S Hles /is_unstamped_ren1_ty HsT2.
  apply (Subs_typed_nocoerce (μ {@ typeEq "A" T.|[ren (+1)] }));
    last (eapply Trans_stp; first apply (@Mu_stp _ ({@ typeEq "A" T })); tcrush).
  apply VObj_typed; tcrush.
Qed.

Lemma packTV_typed T Γ :
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ tv (packTV T) : typeEq "A" T.
Proof. intros; exact: packTV_typed'. Qed.

Definition tApp Γ t T :=
  lett t (lett (tv (packTV T)) (tapp (tv x1) (tv x0))).

Lemma typeApp_typed Γ T U V t :
  Γ u⊢ₜ t : TAll (type "A" >: ⊥ <: ⊤) U →
  (** This subtyping premise is needed to perform "avoidance", as in compilers
    for ML and Scala: that is, producing a type [V] that does not refer to
    variables bound by let in the expression. *)
  (∀ L, typeEq "A" T.|[ren (+2)] :: L :: Γ u⊢ₜ U.|[up (ren (+1))], 0 <: V.|[ren (+2)], 0) →
  is_unstamped_ty (length Γ) T →
  is_unstamped_ty (S (length Γ)) U →
  Γ u⊢ₜ tApp Γ t T.|[ren (+1)] : V.
Proof.
  move => Ht Hsub HsT1 HsU1; move: (HsT1) => /is_unstamped_ren1_ty HsT2.
  move: (HsT2) => /is_unstamped_ren1_ty HsT3.
  rewrite -hrenS in HsT3.
  eapply Let_typed; [exact: Ht| |tcrush].
  eapply Let_typed; [by apply packTV_typed| |tcrush].
  rewrite /= -!hrenS -/(typeEq _ _).

  apply /Subs_typed_nocoerce /Hsub.

  eapply Appv_typed'; first exact: Var_typed'.
  apply: Var_typed_sub; repeat tcrush; rewrite /= hsubst_id //.
  rewrite !hsubst_comp; f_equal. autosubst.
Qed.

Lemma Mu_stp' {Γ T T' i}:
  T' = T.|[ren (+1)] →
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ TMu T', i <: T, i.
Proof. intros; subst. auto. Qed.

Ltac hideCtx :=
  match goal with
  |- ?Γ' u⊢ₜ _, _ <: _, _ => set Γ := Γ'
  end.

(* FromPDotPaper *)

Definition fromPDotPaperTypesTBody : ty := {@
  typeEq "Type" TTop;
  typeEq "TypeRef" $ TAnd (p0 @; "Type") {@
    val "symb" : p1 @ "symbols" @; "Symbol"
  };
  val "AnyType" : TLater (p0 @; "Type");
  val "newTypeRef" : TAll (p1 @ "symbols" @; "Symbol") (p1 @; "TypeRef")
}.

Definition fromPDotPaperAbsTypesTBody : ty := {@
  type "Type" >: TBot <: TTop;
  type "TypeRef" >: TBot <: TAnd (p0 @; "Type") {@
    val "symb" : p1 @ "symbols" @; "Symbol"
  };
  val "AnyType" : TLater (p0 @; "Type");
  val "newTypeRef" : TAll (p1 @ "symbols" @; "Symbol") (p1 @; "TypeRef")
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
  val "newSymbol" : TAll (p1 @ "types" @; "Type") (TAll HashableString (p2 @; "Symbol"))
}.

Definition fromPDotPaperAbsSymbolsTBody : ty := {@
  type "Symbol" >: TBot <: {@
    val "tpe" : p1 @ "types" @; "Type";
    val "name" : HashableString
  };
  val "newSymbol" : TAll (p1 @ "types" @; "Type") (TAll HashableString (p2 @; "Symbol"))
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
    eapply Trans_stp; last (apply TLaterR_stp; tcrush).
    eapply (LSel_stp' _ ⊤); tcrush.
    eapply Var_typed_sub; [ done | apply Sub_later_shift; cbn; tcrush].
  - eapply (Subs_typed_nocoerce) => /=.
    + repeat first [exact: Var_typed' | typconstructor | tcrush].
    + hideCtx.
      eapply Trans_stp; first last.
      eapply LSel_stp'; first last.
      * constructor; eapply Var_typed_sub => //=.
        eapply Trans_stp; first apply TAnd2_stp; tcrush.
      * tcrush.
      * tcrush; last apply Bind1; tcrush.
        eapply (Trans_stp (T2 := ⊤)); tcrush.
        eapply LSel_stp'; tcrush.
        apply: Var_typed_sub; [ tcrush .. ].
Qed.

Example fromPDotPaperTypesAbsTyp :
  TLater fromPDotPaperAbsTBody :: [] u⊢ₜ
    tv fromPDotPaperTypesV : μ fromPDotPaperAbsTypesTBody.
Proof.
  eapply Subs_typed_nocoerce; first exact: fromPDotPaperTypesTyp; tcrush.
  - eapply Trans_stp; first apply TAnd1_stp; tcrush.
  - eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd1_stp; tcrush.
  - eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd2_stp; tcrush.
  - eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd2_stp; tcrush.
Qed.

Example fromPDotPaperSymbolsTyp :
  TLater fromPDotPaperAbsTBody :: [] u⊢ₜ
    tv fromPDotPaperSymbolsV : μ fromPDotPaperSymbolsTBody.
Proof.
  tcrush.
  - eapply (Subs_typed_nocoerce) => /=.
    + repeat first [exact: Var_typed' | typconstructor | tcrush].
    + hideCtx.
      eapply Trans_stp; first last.
      eapply LSel_stp'; first last.
      * constructor; eapply Var_typed_sub => //=.
        tcrush.
      * tcrush.
      * tcrush; apply Bind1; tcrush.
        eapply Trans_stp; first apply TAnd2_stp; tcrush.
Qed.

Example fromPDotPaperSymbolsAbsTyp :
  TLater fromPDotPaperAbsTBody :: [] u⊢ₜ
    tv fromPDotPaperSymbolsV : μ fromPDotPaperAbsSymbolsTBody.
Proof.
  eapply Subs_typed_nocoerce; first exact: fromPDotPaperSymbolsTyp; tcrush.
  eapply Trans_stp; first apply TAnd1_stp; tcrush.
Qed.

Example fromPDotPaperTyp : [] u⊢ₜ tv fromPDotPaper : μ fromPDotPaperAbsTBody.
Proof.
  pose proof fromPDotPaperTypesAbsTyp.
  pose proof fromPDotPaperSymbolsAbsTyp.
  repeat first [done | typconstructor | stcrush].
Qed.

Definition getAnyTypeT : ty :=
  TAll (μ fromPDotPaperAbsTBody) (p0 @ "types" @; "Type").
Definition getAnyType : vl := vabs (tskip (tproj (tproj (tv x0) "types") "AnyType")).

Ltac simplSubst := rewrite /= /up/= /ids/ids_vl/=.
From D.Dot.syn Require Import path_repl.
From D.Dot.lr Require Import path_wp.

Definition fromPDotPaperAbsTypesTBodySubst : ty := {@
  type "Type" >: TBot <: TTop;
  type "TypeRef" >: TBot <: TAnd (p0 @ "types" @; "Type") {@
    val "symb" : p0 @ "symbols" @; "Symbol"
  };
  val "AnyType" : TLater (p0 @ "types" @; "Type");
  val "newTypeRef" : TAll (p0 @ "symbols" @; "Symbol") (p1 @ "types" @; "TypeRef")
}.

Lemma fromPDotPSubst: fromPDotPaperAbsTypesTBody .Tp[ (p0 @ "types") /]~ fromPDotPaperAbsTypesTBodySubst.
Proof.
  apply psubst_ty_rtc_sufficient.
  by rewrite /= !(decide_True _ _ (eq_refl _)) !decide_False.
Qed.

Example getAnyTypeFunTyp Γ : Γ u⊢ₜ tv getAnyType : getAnyTypeT.
Proof.
  rewrite /getAnyType -(iterate_S tskip 0); tcrush.
  eapply (Subs_typed (T1 := TLater (p0 @ "types" @; "Type"))); tcrush.
  set Γ' := (μ fromPDotPaperAbsTBody).|[ren (+1)] :: Γ.
  have Hpx: Γ' u⊢ₚ p0 @ "types" : μ fromPDotPaperAbsTypesTBody, 0.
    by tcrush; eapply Subs_typed_nocoerce;
      [by eapply TMuE_typed, Var_typed' | tcrush].
  have HpxSubst: Γ' u⊢ₚ p0 @ "types" : fromPDotPaperAbsTypesTBodySubst, 0.
    by eapply p_mu_e_typed; [apply fromPDotPSubst|tcrush|].
  eapply (Path_typed (p := p0)), pself_inv_typed, (p_subs_typed (i := 0)), HpxSubst.
  eapply Trans_stp; first apply TAnd2_stp; tcrush.
  eapply Trans_stp; first apply TAnd2_stp; tcrush.
Qed.

Example getAnyTypeTyp0 :
  [μ fromPDotPaperAbsTBody] u⊢ₜ
    tapp (tv getAnyType) (tv x0) : p0 @ "types" @; "Type".
Proof. eapply Appv_typed'; by [exact: getAnyTypeFunTyp|exact: Var_typed'|]. Qed.
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

(* Sec. 5 of WadlerFest DOT.
IFTFun ≡ { if: ∀(x: {A: ⊥..⊤})∀(t: x.A)∀(f: x.A): x.A }
IFT ≡ { if: IFTFun }

let boolImpl =
ν (b: { Boolean: IFT..IFT } ∧ { true: IFT } ∧ { false: IFT })
{ Boolean = IFT } ∧
{ true = λ(x: {A: ⊥..⊤})λ(t: x.A)λ(f: x.A)t } ∧ { false = λ(x: {A: ⊥..⊤})λ(t: x.A)λ(f: x.A)f }

In fact, that code doesn't typecheck as given, and we fix it by setting.

IFT ≡ IFTFun
let bool = boolImpl : μ { Boolean: IFT..IFT; true : b.Boolean; false : b.Boolean }
 *)
Definition IFTBody := (TAll (p0 @; "A") (TAll (p1 @; "A") (p2 @; "A"))).
Definition IFT : ty :=
  TAll (type "A" >: ⊥ <: ⊤) IFTBody.

(* Definition IFT : ty := {@ val "if" : IFTFun }. *)

Definition iftTrue := vabs (vabs' (vabs' (tv x1))).
Definition iftFalse := vabs (vabs' (vabs' (tv x0))).

Example iftTrueTyp Γ : Γ u⊢ₜ tv iftTrue : IFT.
Proof. tcrush. exact: Var_typed'. Qed.
Example iftFalseTyp Γ : Γ u⊢ₜ tv iftFalse : IFT.
Proof. tcrush. exact: Var_typed'. Qed.

Definition p0Bool := p0 @; "Boolean".

Definition boolImpl :=
  ν {@
    type "Boolean" = IFT;
    val "true" = iftTrue;
    val "false" = iftFalse
  }.

Definition boolImplTConcr : ty :=
  μ {@
    typeEq "Boolean" IFT;
    val "true" : IFT;
    val "false" : IFT
  }.

(* This type makes "Boolean" nominal by abstracting it. *)
Definition boolImplT : ty :=
  μ {@
    type "Boolean" >: ⊥ <: IFT;
    val "true" : TLater p0Bool;
    val "false" : TLater p0Bool
  }.

Example SubIFT_LaterP0Bool Γ : TLater {@
    typeEq "Boolean" IFT;
    val "true" : TLater p0Bool;
    val "false" : TLater p0Bool
  } :: Γ u⊢ₜ IFT, 0 <: ▶ p0Bool, 0.
Proof.
  eapply Trans_stp; first (apply (AddI_stp _ _ 2); tcrush).
  eapply Trans_stp; first (apply TLaterR_stp; tcrush).
  eapply Trans_stp; last (apply TLaterR_stp; tcrush).
  eapply LSel_stp. tcrush.
  eapply Var_typed_sub; by [|tcrush].
Qed.

Example SubIFT_LaterP0Bool' Γ : {@
    typeEq "Boolean" IFT;
    val "true" : IFT;
    val "false" : IFT
  }%ty :: Γ u⊢ₜ IFT, 0 <: ▶ p0Bool, 0.
Proof.
  eapply Trans_stp; last (apply TLaterR_stp; tcrush).
  eapply Trans_stp; first (apply (AddI_stp _ _ 2); tcrush).
  eapply Trans_stp; first (apply TLaterR_stp; tcrush).
  eapply LSel_stp. tcrush.
  eapply Var_typed_sub. by [|tcrush].
  eapply Trans_stp; last apply TAddLater_stp; tcrush.
Qed.

Example boolImplTypConcr Γ :
  Γ u⊢ₜ tv boolImpl : boolImplTConcr.
Proof. tcrush; by [apply (dty_typed IFT); tcrush | exact: Var_typed']. Qed.

Example boolImplTyp Γ :
  Γ u⊢ₜ tv boolImpl : boolImplT.
Proof.
  apply (Subs_typed_nocoerce boolImplTConcr); first by apply boolImplTypConcr.
  tcrush; rewrite iterate_0.
  - eapply Trans_stp; first apply TAnd1_stp; tcrush.
  - eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd1_stp; tcrush.
    apply SubIFT_LaterP0Bool'.
  - eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd1_stp; tcrush.
    apply SubIFT_LaterP0Bool'.
Qed.

(* We can also use subtyping on the individual members to type this example. *)
Definition boolImplT0 : ty :=
  μ {@
    typeEq "Boolean" IFT;
    val "true" : TLater p0Bool;
    val "false" : TLater p0Bool
  }.

Lemma dvabs_sub_typed {Γ} V T1 T2 e l L:
  T1.|[ren (+1)] :: V :: Γ u⊢ₜ e : T2 →
  TLater V :: Γ u⊢ₜ TAll T1 T2, 0 <: L, 0 →
  is_unstamped_ty (S (length Γ)) T1 →
  Γ |d V u⊢{ l := dvl (vabs e) } : TVMem l L.
Proof.
  intros He Hsub Hs.
  eapply dvl_sub_typed; first apply Hsub.
  tcrush.
Qed.

Example boolImplTypAlt Γ :
  Γ u⊢ₜ tv boolImpl : boolImplT.
Proof.
  apply (Subs_typed_nocoerce boolImplT0);
    last (tcrush; eapply Trans_stp; first apply TAnd1_stp; tcrush).
  tcrush.
  - eapply Subs_typed_nocoerce; [apply iftTrueTyp|apply SubIFT_LaterP0Bool].
  - eapply Subs_typed_nocoerce; [apply iftFalseTyp|apply SubIFT_LaterP0Bool].
Qed.

(* AND = λ a b. a b False. *)
Definition packBoolean := packTV IFT.
Lemma packBooleanTyp0 Γ :
  Γ u⊢ₜ tv packBoolean : typeEq "A" IFT.
Proof. eapply (packTV_typed' IFT); eauto 1. tcrush. Qed.

Lemma packBooleanTyp Γ :
  Γ u⊢ₜ tv packBoolean : type "A" >: ⊥ <: ⊤.
Proof.
  apply (Subs_typed_nocoerce (typeEq "A" IFT)); last tcrush.
  exact: packBooleanTyp0.
Qed.

Lemma packBooleanLB Γ i :
  typeEq "A" IFT :: Γ u⊢ₜ ▶ IFT, i <: p0 @; "A", i.
Proof. apply /val_LB. exact: Var_typed'. Qed.

Lemma packBooleanUB Γ i :
  typeEq "A" IFT :: Γ u⊢ₜ p0 @; "A", i <: ▶ IFT, i.
Proof. apply /val_UB. exact: Var_typed'. Qed.

(*
let bool = boolImpl :
  μ { Boolean: IFT..IFT; true : b.Boolean; false : b.Boolean;
      and : p.Boolean → p.Boolean → p.Boolean }
*)
Definition iftAnd false : vl := vabs (vabs'
  (lett (tv packBoolean) (tapp (tapp (tapp (tv x2) (tv x0)) (tv x1)) false))).

Example iftAndTyp Γ :
  Γ u⊢ₜ tv (iftAnd (tv iftFalse)) : TAll IFT (TAll IFT (▶IFT)).
Proof.
  rewrite /iftAnd /vabs'.
  tcrush.
  eapply Let_typed; first apply packBooleanTyp0.
  2: tcrush.
  eapply App_typed; last exact: iftFalseTyp.
  eapply App_typed; last exact: Var_typed'.
  rewrite /= -/IFT -/(typeEq "A" IFT).
  eapply Subs_typed_nocoerce. {
    eapply Appv_typed'; first exact: Var_typed'.
    rewrite /= -/IFT.
    2: by change IFTBody.|[_] with IFTBody.
    apply: Var_typed_sub; by [|tcrush].
  }

  apply TAllConCov_stp; stcrush.
  { eapply Trans_stp. exact: packBooleanLB. tcrush. }
  apply TLaterCov_stp, TAllConCov_stp; stcrush.
  - rewrite /= -/IFT. asimpl.
    eapply Trans_stp.
    eapply (val_LB _ _ _ _ 1); exact: Var_typed'.
    tcrush.
  - eapply TLaterCov_stp, Trans_stp.
    eapply val_UB. exact: Var_typed'.
    tcrush.
Qed.

(* Eta-expand to drop the later. *)

Example iftAndTyp'1 Γ :
  Γ u⊢ₜ vabs' (vabs'
    (tskip
      (tapp (tapp (tv (iftAnd (tv iftFalse))) (tv x1)) (tv x0)))) :
    TAll IFT (TAll IFT IFT).
Proof.
  tcrush; rewrite -(iterate_S tskip 0).
  eapply (Subs_typed (T1 := ▶IFT)); first tcrush.
  eapply App_typed; last exact: Var_typed';
    eapply App_typed; last exact: Var_typed'; rewrite /= -/IFT.
  apply iftAndTyp; eauto.
Qed.

Definition iftCoerce t :=
  lett t (vabs' (vabs' (tskip (tapp (tapp (tv x2) (tv x1)) (tv x0))))).

Lemma coerce_tAppIFT Γ t T :
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ t : TAll T (TAll T.|[ren (+1)] (▶ T.|[ren (+2)])) →
  Γ u⊢ₜ iftCoerce t : TAll T (TAll T.|[ren (+1)] T.|[ren (+2)]).
Proof.
  move => HsT1 Ht.
  move: (HsT1) => /is_unstamped_ren1_ty HsT2.
  move: (HsT2) => /is_unstamped_ren1_ty; rewrite -hrenS => HsT3.
  move: (HsT3) => /is_unstamped_ren1_ty; rewrite -hrenS => HsT4.
  eapply Let_typed; [exact: Ht| |tcrush].
  rewrite /= !(hren_upn_gen 1) (hren_upn_gen 2) /=.
  tcrush; rewrite -!hrenS -(iterate_S tskip 0).
  eapply (Subs_typed (T1 := ▶T.|[_])); first tcrush.
  eapply App_typed; last exact: Var_typed';
    eapply App_typed; last exact: Var_typed'.
  apply: Var_typed' => //.
  rewrite /= !(hren_upn 1) (hren_upn_gen 1) (hren_upn_gen 2)
    !hsubst_comp !ren_ren_comp /=. done.
Qed.

Example iftAndTyp'2 Γ :
  Γ u⊢ₜ iftCoerce (tv (iftAnd (tv iftFalse))) : TAll IFT (TAll IFT IFT).
Proof. intros. apply /coerce_tAppIFT /iftAndTyp; tcrush. Qed.

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

Lemma tAppIFT_typed Γ T t :
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ t : IFT →
  Γ u⊢ₜ tApp Γ t T.|[ren (+1)]:
    TAll T (TAll T.|[ren (+1)] (▶ T.|[ren (+2)])).
Proof.
  move => HsT1 Ht; move: (HsT1) => /is_unstamped_ren1_ty HsT2.
  intros; eapply typeApp_typed => //; tcrush.
  intros; asimpl. exact: (subIFT 1).
Qed.

Lemma tAppIFT_coerced_typed Γ T t :
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ t : IFT →
  Γ u⊢ₜ iftCoerce (tApp Γ t T.|[ren (+1)]) :
    TAll T (TAll T.|[ren (+1)] T.|[ren (+2)]).
Proof. intros. by apply /coerce_tAppIFT /tAppIFT_typed. Qed.

Lemma tAppIFT_coerced_typed_IFT Γ t :
  Γ u⊢ₜ t : IFT →
  Γ u⊢ₜ iftCoerce (tApp Γ t IFT.|[ren (+1)]) :
    TAll IFT (TAll IFT IFT).
Proof. intros. apply tAppIFT_coerced_typed; eauto 2. tcrush. Qed.

Definition IFTp0 := TAll p0Bool (TAll p0Bool.|[ren (+1)] (p0Bool.|[ren (+2)])).

Lemma tAppIFT_coerced_typed_p0Boolean Γ T t :
  T :: Γ u⊢ₜ t : IFT →
  T :: Γ u⊢ₜ iftCoerce (tApp (T :: Γ) t p0Bool.|[ren (+1)]) :
    TAll p0Bool (TAll p0Bool.|[ren (+1)] p0Bool.|[ren (+2)]).
Proof. intros. apply tAppIFT_coerced_typed; eauto 3. tcrush. Qed.

Definition iftNot Γ t s :=
  tapp (tapp
      (iftCoerce (tApp Γ t s))
    (tv iftFalse))
  (tv iftTrue).

Lemma iftNotTyp Γ T t :
  Γ u⊢ₜ t : IFT →
  Γ u⊢ₜ iftNot Γ t IFT : IFT.
Proof.
  intros.
  eapply App_typed; last exact: iftTrueTyp.
  eapply App_typed; last exact: iftFalseTyp.
  exact: tAppIFT_coerced_typed_IFT.
Qed.

Definition iftAnd2 Γ t1 t2 s :=
  tapp (tapp
      (iftCoerce (tApp Γ t1 s))
    t2)
  (tv iftFalse).

Lemma iftAndTyp2 Γ T t1 t2 :
  Γ u⊢ₜ t1 : IFT →
  Γ u⊢ₜ t2 : IFT →
  Γ u⊢ₜ iftAnd2 Γ t1 t2 IFT : IFT.
Proof.
  intros Ht1 Ht2.
  eapply App_typed; last exact: iftFalseTyp.
  eapply App_typed; last exact: Ht2.
  exact: tAppIFT_coerced_typed_IFT.
Qed.
