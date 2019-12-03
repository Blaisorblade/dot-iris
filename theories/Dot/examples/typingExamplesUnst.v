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

Notation HashableString := (μ {@ val "hashCode" : TUnit →: TNat }).
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

(* Note how we must weaken the type (or its environment) to account for the
   self-variable of the created object. *)
Definition packTV T := (ν {@ type "A" = shift T }).

Lemma packTV_typed' T n Γ :
  is_unstamped_ty n T →
  n <= length Γ →
  Γ u⊢ₜ tv (packTV T) : typeEq "A" T.
Proof.
  move => HsT1 Hle; move: (Hle) (HsT1) => /le_n_S Hles /is_unstamped_ren1_ty HsT2.
  apply (Subs_typed_nocoerce (μ {@ typeEq "A" (shift T) }));
    last (eapply Trans_stp; first apply (@Mu_stp _ ({@ typeEq "A" T })); tcrush).
  apply VObj_typed; tcrush.
Qed.

Lemma packTV_typed T Γ :
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ tv (packTV T) : typeEq "A" T.
Proof. intros; exact: packTV_typed'. Qed.

Definition tyApp t T :=
  lett t (lett (tv (packTV (shift T))) (tapp (tv x1) (tv x0))).

Lemma tyApp_typed Γ T U V t :
  Γ u⊢ₜ t : TAll (tparam "A") U →
  (** This subtyping premise is needed to perform "avoidance", as in compilers
    for ML and Scala: that is, producing a type [V] that does not refer to
    variables bound by let in the expression. *)
  (∀ L, typeEq "A" T.|[ren (+2)] :: L :: Γ u⊢ₜ U.|[up (ren (+1))], 0 <: V.|[ren (+2)], 0) →
  is_unstamped_ty (length Γ) T →
  is_unstamped_ty (S (length Γ)) U →
  Γ u⊢ₜ tyApp t T : V.
Proof.
  move => Ht Hsub HsT1 HsU1; move: (HsT1) => /is_unstamped_ren1_ty HsT2.
  move: (HsT2) => /is_unstamped_ren1_ty HsT3.
  rewrite -hrenS in HsT3.
  eapply Let_typed; [exact: Ht| |tcrush].
  eapply Let_typed; [by apply packTV_typed| |tcrush].
  rewrite /= -!hrenS -/(typeEq _ _).

  apply /Subs_typed_nocoerce /Hsub.

  eapply Appv_typed'; first var.
  apply: Var_typed_sub; repeat tcrush; rewrite /= hsubst_id //.
  rewrite !hsubst_comp; f_equal. autosubst.
Qed.

Lemma Mu_stp' {Γ T T' i}:
  T' = shift T →
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ μ T', i <: T, i.
Proof. intros; subst. auto. Qed.

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
    + eapply Trans_stp; first last.
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
    + eapply Trans_stp; first last.
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
Proof.
  apply psubst_ty_rtc_sufficient.
  by rewrite /= !(decide_True _ _ (eq_refl _)) !decide_False.
Qed.

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
Definition IFTBody : ty := p0 @; "A" →: p0 @; "A" →: p0 @; "A".
Definition IFT : ty :=
  TAll (tparam "A") IFTBody.

(* Definition IFT : ty := {@ val "if" : IFTFun }. *)

Definition iftTrue := vabs (vabs' (vabs' (tv x1))).
Definition iftFalse := vabs (vabs' (vabs' (tv x0))).

Example iftTrueTyp Γ : Γ u⊢ₜ tv iftTrue : IFT.
Proof. tcrush. var. Qed.
Example iftFalseTyp Γ : Γ u⊢ₜ tv iftFalse : IFT.
Proof. tcrush. var. Qed.

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

Example SubIFT_P0Bool Γ : {@
    typeEq "Boolean" IFT;
    val "true" : IFT;
    val "false" : IFT
  }%ty :: Γ u⊢ₜ IFT, 0 <: p0Bool, 0.
Proof. eapply LSel_stp'; tcrush. varsub; tcrush. Qed.

Example SubIFT_LaterP0Bool' Γ : {@
    typeEq "Boolean" IFT;
    val "true" : IFT;
    val "false" : IFT
  }%ty :: Γ u⊢ₜ IFT, 0 <: ▶ p0Bool, 0.
Proof. eapply Trans_stp; first exact: SubIFT_P0Bool. tcrush. Qed.

Example SubIFT_LaterP0Bool Γ : (▶ {@
    typeEq "Boolean" IFT;
    val "true" : ▶ p0Bool;
    val "false" : ▶ p0Bool
  })%ty :: Γ u⊢ₜ IFT, 0 <: ▶ p0Bool, 0.
Proof.
  asideLaters.
  eapply Trans_stp; first (apply (AddI_stp _ _ 1); tcrush).
  eapply LSel_stp'; tcrush.
  varsub; tcrush.
Qed.

Example boolImplTypConcr Γ :
  Γ u⊢ₜ tv boolImpl : boolImplTConcr.
Proof. tcrush; by [apply (dty_typed IFT); tcrush | var]. Qed.

Example boolImplTyp Γ :
  Γ u⊢ₜ tv boolImpl : boolImplT.
Proof.
  apply (Subs_typed_nocoerce boolImplTConcr); first by apply boolImplTypConcr.
  tcrush; rewrite iterate_0.
  - lThis.
  - lNext.
    lThis.
    apply SubIFT_LaterP0Bool'.
  - do 2 lNext.
    lThis.
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
  shift T1 :: V :: Γ u⊢ₜ e : T2 →
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
  Γ u⊢ₜ tyApp t T : T →: T →: ▶ T.
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
  Γ u⊢ₜ iftCoerce (tyApp t T) : T →: T →: T.
Proof. intros. by apply /iftCoerce_typed /tyAppIFT_typed. Qed.

Lemma iftCoerce_tyAppIFT_typed_IFT Γ t :
  Γ u⊢ₜ t : IFT →
  Γ u⊢ₜ iftCoerce (tyApp t IFT) : IFT →: IFT →: IFT.
Proof. intros. apply iftCoerce_tyAppIFT_typed; tcrush. Qed.

Definition iftNotBody t T true false :=
  tapp (tapp
      (iftCoerce (tyApp t T))
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
      (iftCoerce (tyApp t1 T))
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
let bool = boolImpl :
  μ { Boolean: IFT..IFT; true : b.Boolean; false : b.Boolean;
      and : p.Boolean →: p.Boolean →: p.Boolean }
*)

Definition IFTp0 : ty := p0Bool →: p0Bool →: p0Bool.

Lemma iftCoerce_tyAppIFT_typed_p0Boolean Γ T t :
  T :: Γ u⊢ₜ t : IFT →
  T :: Γ u⊢ₜ iftCoerce (tyApp t p0Bool) : p0Bool →: p0Bool →: p0Bool.
Proof. intros. apply iftCoerce_tyAppIFT_typed; tcrush. Qed.

(*
  Encoding Option. Beware I'm using raw Church-encoded booleans, simply
    because it's easier.
  type Option = {
    type T
    val isEmpty: Boolean
    val pmatch: [U] => U => (T => U) => U
  }
*)

Definition optionT : ty := μ {@ (* self => *)
  tparam "T";
  val "isEmpty" : IFT;
  val "pmatch" : TAll (tparam "U") (p0 @; "U" →: (p1 @; "T" →: p0 @; "U") →: p0 @; "U")
  (* ∀ x : {type U}, x.U → (self.T -> x.U) -> x.U *)
}.
(*
  type None = Option { type T = Nothing }
  def mkNone[T]: None = new {
    type T = Nothing
    val isEmpty = true
    val pmatch: [U] => U => (T => U) => U = [U] => (none: U) => (some: T => U) => none
  }
*)
Definition noneT0 := TAnd optionT ({@ typeEq "T" ⊥}).
Definition noneT : ty := μ {@ (* self => *)
  typeEq "T" ⊥;
  val "isEmpty" : IFT;
  val "pmatch" : TAll (tparam "U") (p0 @; "U" →: (p1 @; "T" →: p0 @; "U") →: p0 @; "U")
}.
Definition mkNone : vl := ν {@
  type "T" = ⊥;
  val "isEmpty" = iftTrue;
  val "pmatch" = vabs (vabs' (vabs' (tv x1)))
}.

Example noneTyp Γ :
  Γ u⊢ₜ tv mkNone : noneT.
Proof.
  (* apply VObj_typed; last stcrush.
  apply dcons_typed; [tcrush| |tcrush].
  apply dcons_typed; [eauto using iftTrueTyp| |tcrush]. *)
  tcrush; var.
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

Definition someT T : ty := μ {@ (* self => *)
  typeEq "T" (shift T);
  val "isEmpty" : IFT;
  val "pmatch" : TAll (tparam "U") (p0 @; "U" →: (p1 @; "T" →: p0 @; "U") →: p0 @; "U");
  val "get" : ▶ p0 @; "T"
}.
Definition mkSomeT : ty := TAll (tparam "A") (p0 @; "A" →: someT (p0 @; "A")).
Definition mkSome : tm := vabs' $ vabs' $ tv $ ν {@
  type "T" = p2 @; "A";
  val "isEmpty" = iftFalse;
  val "pmatch" = vabs (vabs' (vabs' (tapp (tv x0) (tskip (tproj (tv x3) "get")))));
  val "get" = x1
}.

Example mkSomeTyp Γ :
  Γ u⊢ₜ mkSome : mkSomeT.
Proof.
  tcrush; first var; cbv; hideCtx.
  - eapply App_typed; first var.
    rewrite -(iterate_S tskip 0);
      apply (Subs_typed (T1 := (▶ (p3 @; "T"))%ty)); tcrush.
    varsub.
    repeat lNext.
  - varsub.
    eapply Trans_stp; first (apply TAddLater_stp; tcrush).
    asideLaters.
    eapply LSel_stp'; tcrush.
    varsub; tcrush.
Qed.

Definition loopDefV : vl := ν {@ (* self => *)
  val "loop" = vabs (tapp (tproj (tv x1) "loop") (tv x0))
  (* λ v, self.loop v. *)
}.
Definition loopDefTConcr : ty := μ {@ val "loop" : ⊤ →: ⊥ }.
Definition loopDefT : ty := val "loop" : ⊤ →: ⊥.
Example loopDefTyp Γ : Γ u⊢ₜ tv loopDefV : loopDefT.
Proof.
  apply (Subs_typed_nocoerce loopDefTConcr).
  - tcrush; cbv.
    eapply App_typed; last var. tcrush.
    varsub. cbv. lThis.
  - apply Bind1; tcrush.
Qed.

Definition loopTm := tapp (tproj (tv loopDefV) "loop") (tv (vnat 0)).
Example loopTyp Γ : Γ u⊢ₜ loopTm : ⊥.
Proof.
  pose proof loopDefTyp Γ.
  apply (App_typed (T1 := ⊤)); tcrush.
  apply (Subs_typed_nocoerce 𝐍); tcrush.
Qed.

Section listLib.

Definition trueTm := tskip (tproj (tv x0) "true").
Definition falseTm := tskip (tproj (tv x0) "false").

Definition nilV : vl := ν {@ (* self => *)
  type "A" = ⊥;
  val "isEmpty" = vabs (* d => *) (trueTm.|[ren (+2)]); (* for self and d *)
  val "head" = vabs loopTm;
  val "tail" = vabs loopTm
}.

(*
  λ(x: {A})λ(hd: x.A)λ(tl: sci.List∧{A <: x.A}) let result = ν(self) {
    A = x.A; isEmpty = bool.false; head = hd; tail = tl } in result *)
Definition consV : vl :=
  vabs (* x => *) $ vabs' (* hd => *) $ vabs' (* tl => *) $ tv $ ν {@ (* self => *)
    type "A" = p3 @; "T";
    val "isEmpty" = vabs (* d => *) falseTm.|[ren (+5)];
    val "head" = vabs (* d => *) (tv x3);
    val "tail" = vabs (* d => *) (tv x2)
  }.

Definition listTBodyGen L U := μ {@ (* self => *)
  type "A" >: shift L <: shift U;
  val "isEmpty" : ⊤ →: p2 @; "Boolean"; (* bool.Boolean *)
  val "head" : ⊤ →: p0 @; "A"; (* self.A *)
  val "tail" : ⊤ →: TAnd (p1 @; "List") (type "A" >: ⊥ <: p0 @; "A" )
}.

Definition listTBody := listTBodyGen ⊥ ⊤.

Definition listV : vl := ν {@ (* sci => *)
  type "List" = listTBody; (* [shift] is for [sci] *)
  val "nil" = shiftV nilV;
  val "cons" = shiftV consV
}.

Definition nilT := TAnd listTBody (typeEq "A" ⊥).

(** ∀(x: {A})∀(hd: x.A)∀(tl: sci.List∧{A <: x.A})sci.List∧{A <: x.A} *)
Definition consT sci : ty :=
  TAll (tparam "T")
    (p0 @; "T" →:
    (TAnd (shift sci @; "List") (type "A" >: ⊥ <: p0 @; "T")) →:
    TAnd (shift sci @; "List") (type "A" >: ⊥ <: p0 @; "T")).

Definition listT : ty := μ {@ (* sci => *)
  type "List" >: ⊥ <: listTBody; (* [shift] is for [sci] *)
  val "nil" : nilT;
  val "cons" : consT p0
}.
Context Γ.

(* bool : boolImplT *)
Let Γ' := boolImplT :: Γ.

Lemma trueTyp Γ'' : Γ'' ++ Γ' u⊢ₜ trueTm.|[ren (+length Γ'')] : p0.|[ren (+length Γ'')] @; "Boolean".
Proof.
  have ?: length Γ'' < length (Γ'' ++ Γ') by rewrite app_length /Γ'/=; lia.
  rewrite /trueTm /= -(iterate_S tskip 0).
  apply (Subs_typed (T1 := ▶ pv (ids (length Γ'')) @; "Boolean"));
    rewrite plusnO; tcrush.
  eapply Subs_typed_nocoerce.
  - eapply TMuE_typed'; first eapply Var_typed'; by [rewrite lookup_app_r ?Nat.sub_diag|].
  - repeat lNext.
Qed.

Lemma falseTyp Γ'' : Γ'' ++ Γ' u⊢ₜ falseTm.|[ren (+length Γ'')] : p0.|[ren (+length Γ'')] @; "Boolean".
Proof.
  have ?: length Γ'' < length (Γ'' ++ Γ') by rewrite app_length /Γ'/=; lia.
  rewrite /falseTm /= -(iterate_S tskip 0).
  apply (Subs_typed (T1 := ▶ pv (ids (length Γ'')) @; "Boolean"));
    rewrite plusnO; tcrush.
  eapply Subs_typed_nocoerce.
  - eapply TMuE_typed'; first eapply Var_typed'; by [rewrite lookup_app_r ?Nat.sub_diag|].
  -
    (* Optional tactic, just for seeing what happens: *)
    lNext; rewrite -(decomp_s _ (ids _ .: ren _)) /=.
    (* Needed: *)
    repeat lNext.
Qed.

Definition consTResConcr U : ty := listTBodyGen U U.
Definition consTConcr sci : ty :=
  TAll (tparam "T")
    (p0 @; "T" →:
      TAnd (shift sci @; "List") (type "A" >: ⊥ <: p0 @; "T") →:
      (* This renaming is needed because I'm inserting a local variable that isn't expected by
      [consTResConcr] *and I'm using it in the argument*. I could also just clone *)
      (consTResConcr (p2 @; "T")).|[ids 1 .: ids 2 .: ids 0 .: ids]).

Definition listTConcrBody : ty := {@ (* sci => *)
  typeEq "List" $ listTBody; (* [shift] is for [sci] *)
  val "nil" : nilT;
  val "cons" : consTConcr p0
}.

Definition listTConcr : ty := μ listTConcrBody.

Definition nilTConcr : ty := listTBodyGen ⊥ ⊥.

Example nilTyp : (▶ listTConcrBody)%ty :: Γ' u⊢ₜ shift (tv nilV) : nilT.
Proof.
  apply (Subs_typed_nocoerce nilTConcr).
  - evar (T : ty).
    have := trueTyp [⊤; T; ▶ listTConcrBody]%ty.
    have := loopTyp (⊤ :: T :: ▶ listTConcrBody :: Γ')%ty.
    rewrite {}/T/= => Ht Hl.
    tcrush; apply (Subs_typed_nocoerce ⊥); tcrush.
  - tcrush.
    lThis.
    apply Bind1; tcrush.
Qed.

Example consTyp :
  (▶ listTConcrBody)%ty :: Γ' u⊢ₜ shift (tv consV) : consTConcr p0.
Proof.
  epose proof falseTyp [_; _; _; _; _; _] as Ht; cbn in Ht.
  tcrush; clear Ht; first by varsub; eapply (LSel_stp' _ (p4 @; "T")); tcrush; varsub; lThis.
  hideCtx. varsub. cbn. tcrush. lNext.
  eapply LSel_stp'; tcrush. varsub. lThis.
Qed.

Lemma consTSub : listTConcrBody :: Γ' u⊢ₜ consTConcr p0, 0 <: consT p0, 0.
Proof.
  tcrush; rewrite !iterate_S !iterate_0; hideCtx.
  eapply LSel_stp'; tcrush. varsub. tcrush. lThis.
  by lThis.
  apply Bind1; stcrush. by lThis.
Qed.

Example listTypConcr : Γ' u⊢ₜ tv listV : listTConcr.
Proof.
  have := nilTyp => *.
  (* Without the call to [dvl_typed], Coq would (smartly) default to [dvabs_typed] *)
  have := consTyp => /(dvl_typed "cons") *.
  tcrush.
Qed.

Example listTyp : Γ' u⊢ₜ tv listV : listT.
Proof.
  have Hv := listTypConcr.
  have Hsub := consTSub.
  apply (Subs_typed_nocoerce listTConcr); tcrush.
  lThis.
  lNext.
  do 2 lNext; lThis.
Qed.

End listLib.
