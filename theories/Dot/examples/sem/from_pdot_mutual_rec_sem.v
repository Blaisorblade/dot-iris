(** * Motivating example, semantic version.

This example is called in code [fromPDotPaper], because it is indeed inspired
by the pDOT paper. This example is encoded using both [DBNotation] and
[hoasNotation].

Here, the main lemmas are
- [fromPDotPaperTyp], saying that
  [fromPDotPaper] has semantic type [μ (fromPDotPaperAbsTBody options)]
  in a context binding [options] to a module implementing [Option], and
- [pCoreClosedClientSafe], asserting safety of
  [pCoreClosedClientTm], which links [fromPDotPaper] against
  [hoptionModV], an implementation of Option, and against
  [getAnyType], a client that invokes a method on [fromPDotPaper].

The implementation also uses storeless typing for convenience, since we have
some automation using it.
*)

From stdpp Require Import strings.
From iris.program_logic Require Import ectx_language.
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import weakestpre lifting.

From D Require Import tactics swap_later_impl.
From D.Dot Require Import storeless_typing skeleton path_repl unstampedness_binding.
From D.Dot Require Import examples_lr_syn.
From D.Dot Require Import sem_unstamped_typing ex_iris_utils.
From D.Dot Require Import prim_boolean_option.

Import dlang_adequacy prim_boolean_option_mod.
Import DBNotation.

(* Override some imports. *)
Import prelude.

Set Implicit Arguments.
Unset Strict Implicit.
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

Definition tTop : ty := ⊤.

Definition tSymbol : ty := {@
  val "tpe" : optionTy x2 x1;
  val "id" : TInt
}.

Definition tTypeRef : ty := TAnd (x0 @; "Type") typeRefTBody.

Definition assert cond :=
  tif cond 0 hloopTm.
Definition seq (e1 e2 : tm) := lett e1 (shift e2).

Definition newTypeRefBody :=
  seq (assert (~ (tskip x0 @: "tpe" @: "isEmpty")))
    (ν {@ val "symb" = x1 }).

Notation "t @:: l" := ((tskip t) @: l) (at level 59, l at next level).
Definition fromPDotPaperTypesVBody : dms := {@
  type "Type" = tTop;
  type "TypeTop" = tTop;
  val "newTypeTop" = vabs (ν {@ });
  type "TypeRef" = tTypeRef;
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
  type "Symbol" = tSymbol;
  val "newSymbol" = (vabs $ vabs $ ν {@
    val "tpe" = x2;
    val "id" = x1
  })
}.

Definition fromPDotPaper : vl := ν {@
  val "types" = ν fromPDotPaperTypesVBody;
  val "symbols" = fromPDotPaperSymbolsV
}.

Lemma sem_later T a b c: V⟦TLater T⟧ a b c ⊣⊢ ▷ V⟦T⟧ a b c.
Proof. by rw. Qed.

Lemma ty_sub_TAnd_TLater_TAnd_distr_inv T U :
  ⊨T TAnd (TLater T) (TLater U) <: TLater (TAnd T U).
Proof. rewrite /ty_sub. rw. iIntros (??) "[$$]". Qed.

(* This is an essential optimization to speed up [iNext]. *)
Typeclasses Opaque pty_interp.

Let newTypeRefΓ Γ :=
  x2 @ "symbols" @; "Symbol" ::
  TAnd fromPDotPaperTypesTBody (TSing (x1 @ "types")) ::
  fromPDotPaperAbsTBody x1 :: optionModTInv :: Γ.
Lemma Hsub0X0 Γ :
  newTypeRefΓ Γ u⊢ₜ x2 @ "symbols" @; "Symbol", 0 <:
    val "tpe" : optionTy x3 x2 , 1.
Proof.
  ettrans; last apply iLater_Sub; stcrush.
  eapply (iSel_Sub (L := ⊥)).
  (* Necessary: Pick this over [iP_Later]. *)
  apply iP_Fld_E.
  varsub.
  ltcrush; mltcrush.
Qed.

(**
Use distributivity of intersections and unions (iDistr_And_Or_Sub, aka
[Distr-∧-∨-<:]) to show, essentially:
<<
  ▷^i ((None ∨ Some) ∧ { type T >: ⊥ <: pcore.types.Type }) <:
  ▷^i (None ∨ (Some ∧ { type T >: ⊥ <: pcore.types.Type }))
>>
as noted in the paper (Sec. 6.3).
*)
Lemma iRefinedOptionSubNoneOrSome Γ i :
  newTypeRefΓ Γ u⊢ₜ
  TAnd hoptionTConcr (type "T" >: ⊥ <: (x2 @ "types") @; "Type"), i <:
  TOr (hnoneConcrT 0) (hsomeType (hoasNotation.hx 2) 0), i.
Proof.
  rewrite /hoptionTConcr/=; ettrans; first apply iDistr_And_Or_Sub;
    stcrush; apply iOr_Sub_split; ltcrush.
Qed.

Lemma HoptSubT Γ :
  newTypeRefΓ Γ u⊢ₜ
    val "tpe" : optionTy x3 x2, 1 <:
    val "tpe" : TLater (hoptionTyConcr1 hoasNotation.hx2), 1.
Proof.
  tcrush; asideLaters.
  rewrite /hoptionTyConcr/hoptionTyConcr1/optionTy/=.
  eapply (iSub_Trans (T2 := TAnd hoptionTConcr
    (type "T" >: ⊥ <: x2 @ "types" @; "Type")) (i2 := 2));
    first apply iSub_And; first 1 last.
  - ettrans; first apply iSub_Add_Later; stcrush; asideLaters; ltcrush.
  - apply iRefinedOptionSubNoneOrSome.
  - lThis. ettrans; last apply iLater_Sub; stcrush.
    eapply (iSel_SubL (L := ⊥) (U := hoptionTConcr)); tcrush.
    varsub.
    ettrans; first apply iSub_Add_Later; stcrush.
    asideLaters; mltcrush.
Qed.

Lemma Hsublast Γ:
  newTypeRefΓ Γ u⊢ₜ shift typeRefTBody, 0 <: x1 @; "TypeRef", 0.
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

Lemma Hx0 Γ :
  newTypeRefΓ Γ v⊢ₜ x0 :
    ▶: val "tpe" : ▶: hoptionTyConcr1 hoasNotation.hx2.
Proof.
  varsub. eapply iSub_Trans, iSub_Trans, iSub_Later;
    [apply Hsub0X0 | apply HoptSubT].
Qed.
Lemma HvT Γ : newTypeRefΓ Γ u⊢ₜ hnoneConcrT, 0 <: val "isEmpty" : TSing true, 0.
Proof. mltcrush. Qed.
Lemma HvF Γ : newTypeRefΓ Γ u⊢ₜ
  hsomeType hoasNotation.hx2, 0 <: val "isEmpty" : TSing false, 0.
Proof. lThis; mltcrush. Qed.

(* Tactic Notation "lrSimpl" := iEval (cbv [pty_interp]).
Tactic Notation "lrSimpl" "in" constr(iSelP) :=
  iEval (cbv [pty_interp]) in iSelP. *)

Tactic Notation "lrSimpl" "in" constr(iSelP) :=
  iEval (rewrite vlr) in iSelP.
Tactic Notation "lrSimpl" := iEval (rewrite vlr).

#[local] Arguments iPPred_car : simpl never.
#[local] Arguments pty_interp : simpl never.

Lemma newTypeRef_semTyped Γ :
  ⊢ newTypeRefΓ Γ u⊨ newTypeRefBody : x1 @; "TypeRef".
Proof.
  iMod (fundamental_typed (Hx0 Γ)) as (x0_s Hsk) ">#Hx0".
  iMod (fundamental_subtype (HvT Γ)) as "#HvT".
  iMod (fundamental_subtype (HvF Γ)) as "#HvF".
  iMod (fundamental_subtype (Hsublast Γ)) as "#Hsub".
  iMod loopSemT as "#Hl".
  unstamp_goal_tm; iIntros "!> %ρ #Hg".
  iSpecialize ("Hx0" with "Hg").

  wp_abind; rewrite -wp_value; iSimpl.
  have {Hsk x0_s} ->: x0_s = x0.
  by repeat constrain_bisimulating.

  rewrite /interp_expr wp_value_inv sem_later /of_val.
  wp_pure.

  rewrite vlr oVMem_eq. iDestruct "Hx0" as (p Hl) "Hx0".
  rewrite path_wp_eq; iDestruct "Hx0" as (optV Hal) "HoptV"; rewrite sem_later.
  wp_pure.
  have [n HpOptV] := path_wp_exec_pure _ _ Hal; wp_pure => {HpOptV n}.
  lrSimpl in "HoptV".
  (* iEval (rewrite /hoptionTyConcr1 [hTOr _ _]/= /hclose_ty /hclose vlr) in "HoptV". *)
  (* lrSimpl in "HoptV". *)
  (* iClear "HvT HvF Hsub Hl Hg".
  iExFalso.

  (* assert True. { clear.
  About cinterp_TOr. *)
  iEval (rewrite cinterp_TOr) in "HoptV".
  iPPred_car_proper
  clty_olty _proper
  c2o
  rewrite cinterp_TOr.
  iEval (rewrite (vlr, klr, clr)) in "HoptV". *)

  iDestruct "HoptV" as "[Hw|Hw]";
    [iPoseProof "HvT" as "Hv" | iPoseProof "HvF" as "Hv"]; iClear "HvT HvF".
  all: iSpecialize ("Hv" $! _ optV with "Hg Hw").
  (* iEval (rewrite vlr) in "Hv". *)
(*
  iClear "Hsub Hl Hg Hw".

  iMatchHyp (fun name T =>
    match name with
    | INamed "Hw" =>
    match T with
      idtac T
    | _ =>
      fail
    end). *)
(* Tactic Notation "lrSimpl" := iEval (cbv [pty_interp]). *)

  all: lrSimpl in "Hv"; iDestruct "Hv" as (? Hl' pb ->) "Hpb".
  all: rewrite path_wp_pure_exec; iDestruct "Hpb" as (bv) "Hpb".
  all: lrSimpl in "Hpb"; iDestruct "Hpb" as %([n1 Hexec] & Heq).
    (* iDestruct "Hpb" as %(bv & [n1 Hexec] & Heq). *)
  all: move: Heq; rewrite alias_paths_pv_eq_2 path_wp_pure_pv_eq => Heq; cbn in Heq;
    wp_pure; wp_pure => {Hl' n1 pb Hexec}.
  all: rewrite -{bv}Heq; wp_pure; wp_pure.
  by iApply wp_wand; [iApply "Hl" | iIntros "% []"].
  wp_pure.
  (* To conclude, prove the right subtyping for hsomeType and TypeRef. *)
  iSpecialize ("Hsub" with "Hg"); lrSimpl in "Hsub".

  lrSimpl; iApply "Hsub"; iClear "Hsub".

  (* Just to restate the current goal (for some extra readability). *)
  iAssert (V⟦ shift typeRefTBody ⟧ anil ρ
    (shiftV (ν [val "symb" = x1])).[up ρ].[vint 0/])
    as "Hgoal"; last by iApply "Hgoal".
  lrSimpl; iSplit; lrSimpl; last by [].
  rewrite up_sub_compose_vl (_ : (shiftV _).[_] = ν [val "symb" = shiftV (ρ 0)]); last
    by autosubst.
  iApply oVMem_eq; iExists _; iSplit; first by eauto.
  cbn [shift]; rewrite (_: shiftV x1 = x2) //.
  rewrite path_wp_pv_eq.
  rewrite subst_comp ren_scons subst_id /newTypeRefΓ.
  lrSimpl; iSplit. { rewrite fmap_cons. iDestruct "Hg" as "[_ $]". }
  iClear "Hg".

  (* Just to restate/simplify the current goal (for some extra readability). *)
  iAssert (V⟦ val "tpe" : hsomeConcrT ⊥ ⊤ ⟧ anil ρ (ρ 0)) as "Hgoal";
    last by iApply "Hgoal".
  lrSimpl.
  iExists (dpt p); iFrame (Hl); rewrite oDVMem_eq path_wp_eq.
  iExists optV; iFrame (Hal); lrSimpl in "Hw".
  iDestruct "Hw" as "#[$ _]".
Qed.

Ltac semTMember n :=
  iApply (uD_Typ (n := n)); tcrush_nclosed.

Example semFromPDotPaperTypesTyp Γ :
  ⊢ TAnd (▶: fromPDotPaperTypesTBody) (TSing (x1 @ "types")) ::
  (▶: fromPDotPaperAbsTBody x1)%ty :: optionModTInv :: Γ
  u⊨ds fromPDotPaperTypesVBody : fromPDotPaperTypesTBody.
Proof.
  set Γ' := TAnd fromPDotPaperTypesTBody (TSing (x1 @ "types")) ::
    fromPDotPaperAbsTBody x1 :: optionModTInv :: Γ.
  have Hctx:
    ⊨G TAnd (▶: fromPDotPaperTypesTBody) (TSing (x1 @ "types")) ::
    (▶: fromPDotPaperAbsTBody x1)%ty :: optionModTInv :: Γ <:* (TLater <$> Γ').
    by rewrite /Γ'/= -ty_sub_TAnd_TLater_TAnd_distr_inv; ietp_weaken_ctx.

  iApply uD_Cons; [done | semTMember 0 | ].
  iApply uD_Cons; [done | semTMember 0 | ].
  iApply uD_Cons; [done | iApply uD_Val | ]. {
    iApply (uT_All_I_Strong (Γ' := Γ')). apply Hctx.
    iApply fundamental_typed.
    eapply (iT_ISub_nocoerce (TMu TTop)).
    + wtcrush.
    + apply (iSub_Sel' TTop); tcrush; varsub. lThis; ltcrush.
  }
  iApply uD_Cons; [done | semTMember 2 | ].
  iApply uD_Cons; [done | | ]. {
    iApply fundamental_dm_typed.
    tcrush.
    eapply (iT_ISub_nocoerce (TMu ⊤)); first tcrush.
    eapply (iSub_Trans (T2 := ⊤) (i2 := 0)); tcrush.
    eapply (iSub_Trans (i2 := 1)); first exact: iSub_AddI.
    asideLaters.
    eapply (iSub_Sel' ⊤); tcrush. varsub; lThis.
  }
  iApply uD_Cons; [done | iApply uD_Val | ]. {
    iApply (uT_All_I_Strong (Γ' := Γ')); first
      by rewrite /defCtxCons/=; ietp_weaken_ctx.
    iApply newTypeRef_semTyped.
  }

  iApply uD_Sing; iApply uD_Val.
  iApply (uT_All_I_Strong (Γ' := Γ')). apply Hctx.
  iApply fundamental_typed.
  have Hx: x1 @; "TypeRef" :: Γ' v⊢ₜ x0 : ▶: shift typeRefTBody. {
    varsub.
    eapply (iSub_Trans (T2 := ▶: TAnd (x1 @; "Type") (shift typeRefTBody))).
    + apply (iSel_Sub (L := ⊥)); tcrush. varsub. lThis; ltcrush.
    + tcrush.
  }

  (* The proper fix might be to use intersections introduction and Fld_I here.
  (A) on the one hand, show what x.T is.
  (B) on the other hand, thanks to hsomeConcr, we have a get method.
  *)
  eapply (iT_ISub (i := 2)); first apply (iLaterN_Sub _ 2); tcrush.

  apply (iT_ISub (i := 1) (T1 := TAnd (x2 @ "symbols" @; "Symbol")
    (▶: val "tpe" : hsomeConcrT ⊥ ⊤))); first last. {
    typconstructor. eapply (iT_ISub (i := 1)), Hx. asideLaters. ltcrush.
    ettrans; first apply iSub_Add_Later; tcrush; lNext.
  }
  asideLaters.
  apply (iSub_Trans (i2 := 0) (T2 :=
    TAnd (▶: val "tpe" : optionTy x3 x2)
        (▶: val "tpe" : hsomeConcrT ⊥ ⊤))). {
    apply iSub_And_split, iSub_Refl; stcrush.
    apply (iSel_Sub (L := ⊥)), iP_Fld_E.
    varsub.
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
    by ettrans; first apply (iSub_AddIJ' _ 1); wtcrush.
  }
  ettrans; first apply assoc_and; tcrush.
  lNext.
  rewrite /hsomeConcrT/=.
  apply iSub_Skolem_P; stcrush.
  rewrite !iterate_S !iterate_0; hideCtx. simplSubst.
  apply (iP_ISub' (T1 := TAnd (val "get" : ▶: x0 @; "T")
    (type "T" >: ⊥ <: x3 @ "types" @; "Type"))); first last.
  apply iP_And_I; last by tcrush; varsub; tcrush. {
    apply (iP_Mu_E (p := x0) (T := val "get" : ▶: x0 @; "T")); tcrush.
    varsub. asideLaters. lNext. ltcrush.
  }
  lThis.
  apply (iSel_SubL (L := ⊥)); tcrush.
  varsub. mltcrush. lThis.
Qed.

Lemma fromPDotPaperTypesSub Γ:
  ⊢ (▶: fromPDotPaperAbsTBody x1)%ty :: optionModTInv :: Γ ⊨
  μ fromPDotPaperTypesTBody, 0 <: μ fromPDotPaperAbsTypesTBody, 0.
Proof.
  iApply fundamental_subtype.
  ltcrush.
  (* eapply iT_ISub_nocoerce; first exact: fromPDotPaperTypesTyp; ltcrush. *)
  eapply iSub_Sel', (path_tp_delay (i := 0)); wtcrush.
  varsub; tcrush.
Qed.

Example fromPDotPaperSymbolsTyp Γ :
  ⊢ TLater (fromPDotPaperAbsTBody x1) :: optionModTInv :: Γ u⊨
    fromPDotPaperSymbolsV : μ (fromPDotPaperSymbolsTBody x2).
Proof.
  iApply uT_Obj_I.
  iApply uD_Cons; [done | semTMember 3 | ].
  iApply fundamental_dms_typed.
  tcrush.
  eapply (iT_ISub_nocoerce) => /=; hideCtx.
  - repeat first [var | typconstructor | tcrush].
  - ettrans; first last.
    eapply iSub_Sel'; first last.
    + varsub; tcrush.
    + mltcrush.
Qed.

Example fromPDotPaperSymbolsAbsTyp Γ :
  ⊢ TLater (fromPDotPaperAbsTBody x1) :: optionModTInv :: Γ u⊨
    fromPDotPaperSymbolsV : μ (fromPDotPaperAbsSymbolsTBody x2).
Proof.
  iApply (uT_ISub (i := 0)); first by iApply fromPDotPaperSymbolsTyp.
  iApply fundamental_subtype.
  tcrush; lThis.
Qed.

Example fromPDotPaperTyp Γ :
  ⊢ optionModTInv :: Γ u⊨ fromPDotPaper : μ (fromPDotPaperAbsTBody x1).
Proof.
  iApply uT_Obj_I.
  iApply uD_Cons; [done| | iApply uD_Sing].
  - iApply uD_Path_Sub; last iApply uD_Val_New.
    + iApply fromPDotPaperTypesSub.
    + iApply semFromPDotPaperTypesTyp.
  - iApply uD_Val.
    iApply fromPDotPaperSymbolsAbsTyp.
Qed.

Example pCoreSemTyped Γ :
  ⊢ Γ u⊨ lett hoptionModV fromPDotPaper : ⊤.
Proof.
  rewrite /lett.
  iApply uT_All_E; first last.
  iApply fundamental_typed.
  exact: optionModInvTyp.
  iApply (uT_All_I_Strong (Γ' := Γ)). ietp_weaken_ctx.
  iApply uT_Sub.
  iApply fromPDotPaperTyp.
  iApply Stp_Top.
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

Example getAnyTypeFunTyp Γ :
  μ (fromPDotPaperAbsTBody x2) :: optionModTInv :: Γ
  v⊢ₜ getAnyType : getAnyTypeT x1.
Proof.
  rewrite /getAnyType; tcrush.
  eapply (iT_ISub (T1 := TLater (x0 @ "types" @; "Type")) (i := 1)); tcrush.
  set Γ' := shift (μ (fromPDotPaperAbsTBody x2)) ::
    μ (fromPDotPaperAbsTBody x2) :: optionModTInv :: Γ.
  have Hpx: Γ' u⊢ₚ x0 @ "types" : μ fromPDotPaperAbsTypesTBody, 0.
  by eapply iP_Fld_E, iP_ISub', iP_Mu_E; last var; [tcrush|stcrush].
  have HpxSubst: Γ' u⊢ₚ x0 @ "types" : fromPDotPaperAbsTypesTBodySubst, 0.
  by eapply (iP_Mu_E (T := fromPDotPaperAbsTypesTBody)
    (p := x0 @ "types")), Hpx; stcrush.
  eapply iT_Path', iP_Fld_I, (iP_ISub (i := 0)), HpxSubst.
  repeat lNext.
Qed.

Example getAnyTypeTyp0 Γ :
  μ (fromPDotPaperAbsTBody x2) :: optionModTInv :: Γ v⊢ₜ
    tapp getAnyType x0 : x0 @ "types" @; "Type".
Proof. by eapply iT_All_Ex'; [exact: getAnyTypeFunTyp|var|]. Qed.

Definition pCoreClosedClientTm :=
  lett hoptionModV
    (lett fromPDotPaper
      (tapp getAnyType x0)).

Lemma pCoreClosedClientTy Γ :
   ⊢ Γ u⊨ pCoreClosedClientTm : ⊤.
Proof.
  rewrite /lett.
  iApply uT_All_E; first last.
  iApply fundamental_typed.
  exact: optionModInvTyp.
  iApply (uT_All_I_Strong (Γ' := Γ)). ietp_weaken_ctx.
  iApply uT_All_E; first last.
  iApply fromPDotPaperTyp.
  iApply uT_All_I_Strong. ietp_weaken_ctx.
  iApply uT_Sub; last iApply Stp_Top.
  iApply fundamental_typed.
  apply getAnyTypeTyp0.
Qed.
End semExample.

(**
Demonstrate applying adequacy to get safety.
*)
Lemma pCoreClosedClientSafe: safe pCoreClosedClientTm.
Proof.
  eapply (unstamped_safety_dot_sem dlangΣ (T := ⊤))=>*.
  iApply pCoreClosedClientTy.
Qed.
