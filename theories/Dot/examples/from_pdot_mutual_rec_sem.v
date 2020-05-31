(** * Motivating example, semantic version.

This example is called in code [fromPDotPaper], because it is indeed inspired
by the pDOT paper. This example is encoded using both [DBNotation] and
[hoasNotation].

Here, the main lemmas are
- [fromPDotPaperTyp], saying that
  [fromPDotPaper] has semantic type [μ (fromPDotPaperAbsTBody x1)]
  in a suitable context, and
- [pcoreSafe], asserting safety of
  [lett hoptionModV fromPDotPaper], which links [fromPDotPaper] against
  [hoptionModV], an implementation of Option.

The implementation also uses, for convenience, storeless typing.
*)

From stdpp Require Import strings.
From iris.program_logic Require Import ectx_language.
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import weakestpre lifting.

From D Require Import tactics swap_later_impl.
From D.Dot.typing Require Import storeless_typing.
From D.Dot Require Import path_repl.
From D.Dot Require Import ex_iris_utils.
From D.Dot Require Import prim_boolean_option.

Import dlang_adequacy stamp_transfer prim_boolean_option_mod.

Import DBNotation.

(* Override some imports. *)
Import prelude.

Set Implicit Arguments.
Set Suggest Proof Using.
Set Default Proof Using "Type*".

Section hoas.
  Import hoasNotation.
  Definition hoptionTyConcr pCore :=
    hTOr hnoneConcrT (hsomeConcrT
      ⊥
      (pCore @ "types" @; "Type")).
  Definition optionModTInv : ty := μ: self, hoptionModTInvBody self.

  Definition hsomeType pCore := hTAnd (hsomeConcrT ⊥ ⊤)
      (type "T" >: ⊥ <: pCore @ "types" @; "Type").
  Definition hoptionTyConcr1 (pCore : hpath) := hTOr hnoneConcrT (hsomeType pCore).
End hoas.

(** FromPDotPaper *)

Definition typeRefTBody : ty := {@
  val "symb" : TAnd (x1 @ "symbols" @; "Symbol") (val "tpe" : hsomeConcrT ⊥ ⊤)
}.

Definition fromPDotPaperTypesTBody : ty := {@
  typeEq "Type" ⊤;
  typeEq "TypeTop" ⊤;
  val "newTypeTop" : ⊤ →: x0 @; "TypeTop";
  typeEq "TypeRef" $ TAnd (x0 @; "Type") typeRefTBody;
  val "AnyType" : ▶: (x0 @; "Type");
  val "newTypeRef" : x1 @ "symbols" @; "Symbol" →: x0 @; "TypeRef";
  val "getTypeFromTypeRef" : x0 @; "TypeRef" →: x0 @; "Type"
}.

Definition fromPDotPaperAbsTypesTBody : ty := {@
  type "Type" >: ⊥ <: TTop;
  type "TypeTop" >: ⊥ <: x0 @; "Type";
  val "newTypeTop" : ⊤ →: x0 @; "TypeTop";
  type "TypeRef" >: ⊥ <: TAnd (x0 @; "Type") typeRefTBody;
  val "AnyType" : ▶: (x0 @; "Type");
  val "newTypeRef" : x1 @ "symbols" @; "Symbol" →: x0 @; "TypeRef";
  val "getTypeFromTypeRef" : x0 @; "TypeRef" →: x0 @; "Type"
}.

Definition optionTy pOpt pCore := TAnd (pOpt @; "Option") (type "T" >: ⊥ <: (pCore @ "types" @; "Type")).

Section semExample.
Context `{HdlangG: !dlangG Σ} `{HswapProp : !SwapPropI Σ}.
Context (pTop_stamp pSymbol_stamp pTypeRef_stamp : stamp).

Definition pTop : stampTy := MkTy pTop_stamp [] ⊤ 0.

Definition pSymbol : stampTy := MkTy pSymbol_stamp [x0; x1; x2] {@
  val "tpe" : optionTy x2 x1;
  val "id" : TInt
} 3.

Definition pTypeRef : stampTy := MkTy pTypeRef_stamp [x0; x1] (TAnd (x0 @; "Type") typeRefTBody) 2.

(** The syntactic stamp map we use in our syntactic judgments. *)
Definition fromPDotG : stys := psAddStys primOptionG [pTypeRef; pTop; pSymbol].

Context (Htop : styConforms fromPDotG pTop).
Context (Hsymbol : styConforms fromPDotG pSymbol).
Context (HtypeRef : styConforms fromPDotG pTypeRef).

Definition fromPDotGφ := Vs⟦ fromPDotG ⟧.
Arguments fromPDotG : simpl never.

Lemma pTopStamp : TyMemStamp fromPDotG pTop. Proof. split; stcrush. Qed.
Lemma pTypeRefStamp : TyMemStamp fromPDotG pTypeRef. Proof. split; stcrush. Qed.
Lemma pSymbolStamp : TyMemStamp fromPDotG pSymbol. Proof. split; stcrush. Qed.

Definition assert cond :=
  tif cond 0 hloopTm.
Definition seq (e1 e2 : tm) := lett e1 (shift e2).

Definition newTypeRefBody :=
  seq (assert (~ (tskip x0 @: "tpe" @: "isEmpty")))
    (ν {@ val "symb" = x1 }).

Notation "t @:: l" := ((tskip t) @: l) (at level 59, l at next level).
Definition fromPDotPaperTypesVBody : dms := {@
  type "Type" =[ pTop ];
  type "TypeTop" =[ pTop ];
  val "newTypeTop" = vabs (ν {@ });
  type "TypeRef" =[ pTypeRef ];
  val "AnyType" = ν {@ };
  val "newTypeRef" = vabs newTypeRefBody;
  val "getTypeFromTypeRef" = vabs (
    iterate tskip 2 (x0 @:: "symb" @:: "tpe" @: "get")
  )
}.

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

Definition fromPDotPaperSymbolsV : vl := ν {@
  type "Symbol" =[ pSymbol ];
  val "newSymbol" = (vabs $ vabs $ ν {@
    val "tpe" = x2;
    val "id" = x1
  })
}.

Definition fromPDotPaper : vl := ν {@
  val "types" = ν fromPDotPaperTypesVBody;
  val "symbols" = fromPDotPaperSymbolsV
}.

Tactic Notation "smart_wp_bind'" uconstr(ctxs) ident(v) constr(Hv) uconstr(Hp) :=
  iApply (wp_bind (ectx_language.fill ctxs));
  iApply (wp_wand with "[-]"); [iApply Hp; trivial|];
  iIntros (v) Hv.

Lemma sem_later T a b c: V⟦TLater T⟧ a b c ⊣⊢ ▷ V⟦T⟧ a b c. Proof. done. Qed.

Lemma ty_sub_TAnd_TLater_TAnd_distr_inv T U :
  ⊨T TAnd (TLater T) (TLater U) <: TLater (TAnd T U).
Proof. iIntros (??) "[$$]". Qed.

(* This is an essential optimization to speed up [iNext]. *)
Typeclasses Opaque pty_interp.

Let newTypeRefΓ Γ :=
  x2 @ "symbols" @; "Symbol" ::
  TAnd fromPDotPaperTypesTBody (TSing (x1 @ "types")) ::
  fromPDotPaperAbsTBody x1 :: optionModTInv :: Γ.
Lemma Hsub0X0 Γ g :
  newTypeRefΓ Γ v⊢ₜ[g] x2 @ "symbols" @; "Symbol", 0 <:
    val "tpe" : optionTy x3 x2 , 1.
Proof.
  ettrans; last apply iLater_Sub; stcrush.
  eapply (iSel_Sub (L := ⊥)).
  (* Necessary: Pick this over [iP_Later]. *)
  apply iP_Fld_E.
  tcrush; varsub.
  ltcrush; mltcrush.
Qed.

Lemma HoptSubT Γ g:
  newTypeRefΓ Γ v⊢ₜ[g]
    val "tpe" : optionTy x3 x2, 1 <:
    val "tpe" : TLater (hoptionTyConcr1 hoasNotation.hx2), 1.
Proof.
  tcrush; asideLaters.
  rewrite /hoptionTyConcr/hoptionTyConcr1/optionTy/=.
  eapply (iSub_Trans (T2 := TAnd hoptionTConcr
    (type "T" >: ⊥ <: x2 @ "types" @; "Type")) (i2 := 2));
    first apply iSub_And; first 1 last.
  - ettrans; first apply iSub_Add_Later; stcrush; asideLaters; ltcrush.
  - rewrite /hoptionTConcr/=; ettrans; first apply iDistr_And_Or_Sub;
    stcrush; apply iOr_Sub_split; ltcrush.
  - lThis. ettrans; last apply iLater_Sub; stcrush.
    eapply (iSel_SubL (L := ⊥) (U := hoptionTConcr)); tcrush.
    varsub.
    ettrans; first apply iSub_Add_Later; stcrush.
    asideLaters; mltcrush.
Qed.

Lemma Hsublast Γ g:
  newTypeRefΓ Γ v⊢ₜ[g] shift typeRefTBody, 0 <: x1 @; "TypeRef", 0.
Proof.
  eapply iSub_Sel'; tcrush.
  varsub; lThis.
  ltcrush.
  eapply iSub_Sel'; tcrush.
  varsub; lThis.
  ettrans; first apply iSub_Add_Later; stcrush.
  asideLaters.
  ltcrush.
Qed.

Lemma Hx0 Γ g :
  newTypeRefΓ Γ v⊢ₜ[g] x0 :
    ▶: val "tpe" : ▶: hoptionTyConcr1 hoasNotation.hx2.
Proof.
  varsub. eapply iSub_Trans, iSub_Trans, iSub_Later;
    [apply Hsub0X0 | apply HoptSubT | tcrush].
Qed.
Lemma HvT Γ g : newTypeRefΓ Γ v⊢ₜ[g] hnoneConcrT, 0 <: val "isEmpty" : TSing true, 0.
Proof. mltcrush. Qed.
Lemma HvF Γ g : newTypeRefΓ Γ v⊢ₜ[g]
  hsomeType hoasNotation.hx2, 0 <: val "isEmpty" : TSing false, 0.
Proof. lThis; mltcrush. Qed.

Tactic Notation "lrSimpl" := iEval (cbv [pty_interp]).
Tactic Notation "lrSimpl" "in" constr(iSelP) :=
  iEval (cbv [pty_interp]) in iSelP.

Tactic Notation "wp_bind" uconstr(p) := iApply (wp_bind (fill [p])).
Ltac wp_pure := rewrite -wp_pure_step_later -1?wp_value; last done; iNext.

Lemma newTypeRef_semTyped Γ g :
  ⊢ newTypeRefΓ Γ ⊨[ Vs⟦ g ⟧ ] newTypeRefBody : x1 @; "TypeRef".
Proof.
  have := Hx0 Γ g; set Γ2 := newTypeRefΓ Γ; unfold newTypeRefΓ in Γ2 => Hx0.

  iIntros "#Hs !> %ρ #Hg !>".
  iPoseProof (fundamental_typed Hx0 with "Hs Hg") as "#Hx0".
  wp_bind (AppRCtx _); wp_bind (IfCtx _ _); wp_bind (UnCtx _);
    wp_bind (ProjCtx _); wp_bind (ProjCtx _); iSimpl.

  rewrite /interp_expr wp_value_inv /vclose sem_later /newTypeRefBody /of_val.
  wp_pure.

  lrSimpl in "Hx0"; iDestruct "Hx0" as (d Hl p ->) "Hx0".
  rewrite path_wp_eq; iDestruct "Hx0" as (optV Hal) "HoptV"; rewrite sem_later.
  wp_pure.
  have [n HpOptV] := path_wp_exec_pure _ _ Hal; wp_pure => {HpOptV n}.
  rewrite /hoptionTyConcr1; lrSimpl in "HoptV".
  iDestruct "HoptV" as "[Hw|Hw]"; [have Hv := HvT | have Hv := HvF].
  all: iPoseProof (fundamental_subtype (Hv Γ g) with "Hs") as "Hv";
    iSpecialize ("Hv" $! _ optV with "Hg Hw"); lrSimpl in "Hv";
    iDestruct "Hv" as (? Hl' pb ->) "Hpb"; lrSimpl in "Hpb";
    rewrite path_wp_pure_exec; iDestruct "Hpb" as %(bv & [n1 ?] & Heq).
  all: move: Heq; rewrite alias_paths_pv_eq_2 path_wp_pure_pv_eq => Heq; cbn in Heq;
    wp_pure; wp_pure.
  all: simpl in Heq; rewrite -{}Heq; wp_pure; wp_pure.
  by iApply wp_wand; [iApply loopSemT | iIntros "% []"].
  wp_pure.
  (* To conclude, prove the right subtyping for hsomeType and TypeRef. *)
  iPoseProof (fundamental_subtype (Hsublast Γ g) with "Hs Hg") as "{Hs} Hsub"; lrSimpl in "Hsub".
  iApply "Hsub"; iClear "Hsub".

  (* Just to restate the current goal (for some extra readability). *)
  iAssert (V⟦ shift typeRefTBody ⟧ vnil ρ
    (shiftV (ν [val "symb" = x1])).[up ρ].[vint 0/])
    as "{Hw} #Hw"; last iApply "Hw".
  rewrite (_ : (shiftV _).[_].[_] = ν [val "symb" = shiftV (ρ 0)]); last
    by rewrite up_sub_compose_vl; autosubst.
  lrSimpl; iSplit; last by []. iExists _; iSplit; first by eauto.
  iExists _; iSplit; first by []. rewrite path_wp_pv_eq.
  rewrite (_ : ∀ v w, (shiftV v).[w/] = v); last by
    intros; autosubst.
  iDestruct "Hg" as "[_ H]"; lrSimpl in "H"; lrSimpl.
  iSplit; [by iApply "H"| iClear "H"].

  iAssert (V⟦ val "tpe" : hsomeConcrT ⊥ ⊤ ⟧ vnil ρ (ρ 0)) as "{Hw} #Hw";
    lrSimpl; last iApply "Hw".
  iExists (dpt p); iFrame (Hl); iExists p; iSplit; first done; rewrite path_wp_eq.
  iExists optV; iSplit; first done; lrSimpl in "Hw"; lrSimpl.
  by iDestruct "Hw" as "[$ _]".
Qed.

Ltac semTMember i := iApply D_Typ; iApply (extraction_to_leadsto_envD_equiv (n := i) with "Hs"); by_extcrush.

Example semFromPDotPaperTypesTyp Γ :
  ⊢ TAnd (▶: fromPDotPaperTypesTBody) (TSing (x1 @ "types")) ::
  (▶: fromPDotPaperAbsTBody x1)%ty :: optionModTInv :: Γ
  ⊨ds[ fromPDotGφ ] fromPDotPaperTypesVBody : fromPDotPaperTypesTBody.
Proof.
  set Γ' := TAnd fromPDotPaperTypesTBody (TSing (x1 @ "types")) ::
    fromPDotPaperAbsTBody x1 :: optionModTInv :: Γ.
  have Hctx:
    ⊨G TAnd (▶: fromPDotPaperTypesTBody) (TSing (x1 @ "types")) ::
    (▶: fromPDotPaperAbsTBody x1)%ty :: optionModTInv :: Γ <:* (TLater <$> Γ').
    by rewrite /Γ'/= -ty_sub_TAnd_TLater_TAnd_distr_inv; ietp_weaken_ctx.

  iIntros "#Hs".
  iApply D_Cons; [done | semTMember 0 | ].
  iApply D_Cons; [done | semTMember 0 | ].
  iApply D_Cons; [done | iApply D_Val | ]. {
    iApply (T_All_I_Strong (Γ' := Γ')). apply Hctx.
    iApply (fundamental_typed with "Hs").
    eapply (iT_Sub_nocoerce (TMu TTop)).
    + wtcrush.
    + apply (iSub_Sel' TTop); tcrush; varsub. lThis; ltcrush.
  }
  iApply D_Cons; [done | semTMember 2 | ].
  iApply D_Cons; [done | iApply (fundamental_dm_typed with "Hs")| ]. {
    tcrush.
    eapply (iT_Sub_nocoerce (TMu ⊤)); first tcrush.
    eapply (iSub_Trans (T2 := ⊤) (i2 := 0)); tcrush.
    eapply (iSub_Trans (i2 := 1)); first exact: iSub_AddI.
    asideLaters.
    eapply (iSub_Sel' ⊤); tcrush. varsub; lThis.
  }
  iApply D_Cons; [done | iApply D_Val | ]. {
    iApply (T_All_I_Strong (Γ' := Γ')); first
      by rewrite /defCtxCons/=; ietp_weaken_ctx.
    iApply (newTypeRef_semTyped with "Hs").
  }

  iApply D_Cons; [done | iApply D_Val | iApply D_Nil].
  iApply (T_All_I_Strong (Γ' := Γ')). apply Hctx.
  iApply (fundamental_typed with "Hs").
  have Hx: x1 @; "TypeRef" :: Γ' v⊢ₜ[ fromPDotG ] x0 : ▶: shift typeRefTBody. {
    varsub.
    eapply (iSub_Trans (T2 := ▶: TAnd (x1 @; "Type") (shift typeRefTBody))).
    + apply (iSel_Sub (L := ⊥)); tcrush. varsub. lThis; ltcrush.
    + tcrush.
  }

  (* The proper fix might be to use intersections introduction and Fld_I here.
  (A) on the one hand, show what x.T is.
  (B) on the other hand, thanks to hsomeConcr, we have a get method.
  *)
  eapply (iT_Sub (i := 2)); first apply (iLaterN_Sub (j := 2)); tcrush.

  apply (iT_Sub (i := 1) (T1 := TAnd (x2 @ "symbols" @; "Symbol")
    (▶: val "tpe" : hsomeConcrT ⊥ ⊤))); first last. {
    typconstructor. eapply (iT_Sub (i := 1)), Hx. asideLaters. ltcrush.
    ettrans; first apply iSub_Add_Later; tcrush; lNext.
  }
  asideLaters.
  apply (iSub_Trans (i2 := 0) (T2 :=
    TAnd (▶: val "tpe" : optionTy x3 x2)
        (▶: val "tpe" : hsomeConcrT ⊥ ⊤))). {
    apply iSub_And_split, iSub_Refl; stcrush.
    apply (iSel_Sub (L := ⊥)), iP_Fld_E.
    tcrush; varsub.
    mltcrush.
    by mltcrush.
  }
  rewrite /optionTy; simplSubst.
  (* Next: try to use distributivity. *)
  ettrans; first apply iAnd_Later_Sub_Distr; stcrush.
  asideLaters.
  ettrans; first apply iAnd_Fld_Sub_Distr; tcrush.
  eapply (iSub_Trans (T2 := val "get" : ▶: ▶: x2 @ "types" @; "Type")),
    (iSngl_pq_Sub_inv (q := x1) (p := x2 @ "types"));
    stcrush; [|exact: psubst_ty_rtc_sufficient|]; first last. {
    tcrush; varsub; asideLaters. lNext.
    by ettrans; first apply (iSub_AddIJ' (j := 1)); wtcrush.
  }
  ettrans; first apply assoc_and; tcrush.
  lNext.
  rewrite /hsomeConcrT/=.
  apply iSub_Skolem_P; stcrush.
  rewrite !iterate_S !iterate_0; hideCtx. simplSubst.
  apply (iP_Sub' (T1 := TAnd (val "get" : ▶: x0 @; "T")
    (type "T" >: ⊥ <: x3 @ "types" @; "Type"))); first last.
  apply iP_And; last by tcrush; varsub; tcrush. {
    apply (iP_Mu_E (p := x0) (T := val "get" : ▶: x0 @; "T")); tcrush.
    exact: psubst_ty_rtc_sufficient.
    varsub. asideLaters. lNext. ltcrush.
  }
  lThis.
  apply (iSel_SubL (L := ⊥)); tcrush.
  varsub. mltcrush. lThis.
Qed.

Lemma fromPDotPaperTypesSub Γ:
  ⊢ (▶: fromPDotPaperAbsTBody x1)%ty :: optionModTInv :: Γ ⊨[ fromPDotGφ ]
  μ fromPDotPaperTypesTBody, 0 <: μ fromPDotPaperAbsTypesTBody, 0.
Proof.
  iApply fundamental_subtype.
  ltcrush.
  (* eapply iT_Sub_nocoerce; first exact: fromPDotPaperTypesTyp; ltcrush. *)
  eapply iSub_Sel', (path_tp_delay (i := 0)); wtcrush.
  varsub; tcrush.
Qed.

Example fromPDotPaperSymbolsTyp Γ :
  TLater (fromPDotPaperAbsTBody x1) :: optionModTInv :: Γ v⊢ₜ[fromPDotG]
    fromPDotPaperSymbolsV : μ (fromPDotPaperSymbolsTBody x2).
Proof.
  tcrush; first tMember.
  eapply (iT_Sub_nocoerce) => /=; hideCtx.
  - repeat first [var | typconstructor | tcrush].
  - ettrans; first last.
    eapply iSub_Sel'; first last.
    + constructor; varsub; tcrush.
    + tcrush.
    + mltcrush.
Qed.

Example fromPDotPaperSymbolsAbsTyp Γ :
  TLater (fromPDotPaperAbsTBody x1) :: optionModTInv :: Γ v⊢ₜ[fromPDotG]
    fromPDotPaperSymbolsV : μ (fromPDotPaperAbsSymbolsTBody x2).
Proof.
  eapply iT_Sub_nocoerce; first exact: fromPDotPaperSymbolsTyp; tcrush.
  lThis.
Qed.

Example fromPDotPaperTyp Γ : ⊢ optionModTInv :: Γ ⊨[fromPDotGφ]
  fromPDotPaper : μ (fromPDotPaperAbsTBody x1).
Proof.
  iIntros "#Hs".
  iApply T_Obj_I.
  iApply D_Cons; [done| |].
  - iApply D_Path_Sub; last iApply D_Val_New.
    + iApply (fromPDotPaperTypesSub with "Hs").
    + iApply (semFromPDotPaperTypesTyp with "Hs").

  - iApply D_Cons; [done| iApply D_Val | iApply D_Nil].
    iApply (fundamental_typed with "Hs").
    exact: fromPDotPaperSymbolsAbsTyp.
Qed.

Context (HextMap : primOptionG ⊆ fromPDotG).
Example pCoreSemTyped Γ : ⊢ Γ ⊨[fromPDotGφ]
  lett hoptionModV fromPDotPaper : ⊤.
Proof.
  rewrite /lett.
  iIntros "#Hs".
  iApply T_All_E; first last.
  iApply (fundamental_typed with "Hs").
  eapply storeless_typing_mono_mut; [exact: optionModInvTyp|exact: HextMap].
  iApply (T_All_I_Strong (Γ' := Γ)). ietp_weaken_ctx.
  iApply (T_Sub (i := 0)).
  iApply (fromPDotPaperTyp with "Hs").
  iApply sSub_Top.
Qed.

(** ** Additional examples of client code, not mentioned in the paper.
As they are open terms, technically not covered by the safety theorem below,
but of course they could be, after being made closed. *)
Definition getAnyTypeT pOpt : ty :=
  TAll (μ fromPDotPaperAbsTBody (shift pOpt)) (x0 @ "types" @; "Type").
Definition getAnyType : vl := vabs (tskip (x0 @: "types" @: "AnyType")).

Definition fromPDotPaperAbsTypesTBodySubst : ty := {@
  type "Type" >: ⊥ <: ⊤;
  type "TypeTop" >: ⊥ <: x0 @ "types" @; "Type";
  val "newTypeTop" : ⊤ →: x0 @ "types" @; "TypeTop";
  type "TypeRef" >: ⊥ <: TAnd (x0 @ "types" @; "Type") ({@
    val "symb" : TAnd (x0 @ "symbols" @; "Symbol") (val "tpe" : hsomeConcrT ⊥ ⊤)
  });
  val "AnyType" : ▶: (x0 @ "types" @; "Type");
  val "newTypeRef" : x0 @ "symbols" @; "Symbol" →: x0 @ "types" @; "TypeRef";
  val "getTypeFromTypeRef" : x0 @ "types" @; "TypeRef" →: x0 @ "types" @; "Type"
}.

Lemma fromPDotPSubst: fromPDotPaperAbsTypesTBody .Tp[ x0 @ "types" /]~ fromPDotPaperAbsTypesTBodySubst.
Proof. exact: psubst_ty_rtc_sufficient. Qed.

Example getAnyTypeFunTyp Γ :
  μ (fromPDotPaperAbsTBody x2) :: optionModTInv :: Γ
  v⊢ₜ[fromPDotG] getAnyType : getAnyTypeT x1.
Proof.
  rewrite /getAnyType; tcrush.
  eapply (iT_Sub (T1 := TLater (x0 @ "types" @; "Type")) (i := 1)); tcrush.
  set Γ' := shift (μ (fromPDotPaperAbsTBody x2)) ::
    μ (fromPDotPaperAbsTBody x2) :: optionModTInv :: Γ.
  have Hpx: Γ' v⊢ₚ[fromPDotG] x0 @ "types" : μ fromPDotPaperAbsTypesTBody, 0
    by tcrush; eapply iT_Sub_nocoerce;
      [ by eapply iT_Mu_E; first var; stcrush | tcrush].
  have HpxSubst: Γ' v⊢ₚ[fromPDotG] x0 @ "types" : fromPDotPaperAbsTypesTBodySubst, 0.
  by eapply (iP_Mu_E (T := fromPDotPaperAbsTypesTBody)
    (p := x0 @ "types")), Hpx; tcrush; exact: fromPDotPSubst.
  eapply (iT_Path (p := x0)), iP_Fld_I, (iP_Sub (i := 0)), HpxSubst.
  repeat lNext.
Qed.

Example getAnyTypeTyp0 Γ :
  μ (fromPDotPaperAbsTBody x2) :: optionModTInv :: Γ v⊢ₜ[fromPDotG]
    tapp getAnyType x0 : x0 @ "types" @; "Type".
Proof. eapply iT_All_Ex'; [exact: getAnyTypeFunTyp|var|tcrush..]. Qed.

End semExample.

(** Allocate global stamps. *)
Lemma pcoreSafe: safe (lett hoptionModV (fromPDotPaper 40 50 60)).
Proof.
  eapply (safety_dot_sem dlangΣ (T := _))=>*.
  rewrite (transfer_empty (fromPDotGφ _ _ _)).
  iIntros "> H !>".
  iApply (pCoreSemTyped with "H"); [done..|].
  rewrite /fromPDotG/=.
  by repeat (etrans; last apply map_union_subseteq_r; last solve_map_disjoint).
Qed.
