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
