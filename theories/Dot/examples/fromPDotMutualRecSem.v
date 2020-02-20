(**
 *)
From stdpp Require Import strings.
From iris.program_logic Require Import ectx_language.
From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import weakestpre lifting.

From D Require Import tactics.
From D.Dot.syn Require Import syn path_repl.
From D.Dot.typing Require Import typing_storeless.
From D.Dot Require Import exampleInfra typingExInfra examples.
(* From D.Dot Require Import typingExamples. *)
Import scalaLib.
From D.Dot Require Import primOption.

From D Require Import swap_later_impl.
From D.Dot Require Import unary_lr
  lr_lemmas lr_lemmasTSel lr_lemmasNoBinding lr_lemmasDefs lr_lemmasPrim.
From D.Dot Require Import typeExtractionSem.
From D.Dot Require Import fundamental.
(* From D.Dot Require Import scalaLib.
From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived. *)
Import DBNotation.
Import examples prelude saved_interp_dep.
Import later_sub_sem.

Set Implicit Arguments.
Set Suggest Proof Using.
Set Default Proof Using "Type*".
Import primOption.

Section hoas.
  Import hoasNotation.
  Definition hoptionTyConcr pCore :=
    hTOr hnoneConcrT (hsomeConcrT
      ⊥
      (pCore @ "types" @; "Type")).
  Definition optionModTInv := hclose (μ: self, hoptionModTInvBody self).

  Definition hsomeType pCore := (hTAnd (hsomeConcrT ⊥ ⊤)
      (type "T" >: ⊥ <: pCore @ "types" @; "Type")).
  Definition hoptionTyConcr1 (pCore : hpath) := hTOr hnoneConcrT (hsomeType pCore).
End hoas.

Section semExample.
Context `{HdlangG: dlangG Σ} `{HswapProp : !SwapPropI Σ}.
(** FromPDotPaper *)

Definition typeRefTBody : ty := {@
  val "symb" : TAnd (x1 @ "symbols" @; "Symbol") (val "tpe" : hclose (hsomeConcrT ⊥ ⊤))
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

Definition pTop : stampTy := MkTy 40 [] ⊤ 0.

Definition optionTy pOpt pCore := TAnd (pOpt @; "Option") (type "T" >: ⊥ <: (pCore @ "types" @; "Type")).

Definition pSymbol : stampTy := MkTy 50 [x0; x1; x2] {@
  val "tpe" : optionTy x2 x1;
  val "id" : TNat
} 3.

Definition pTypeRef : stampTy := MkTy 60 [x0; x1] (TAnd (x0 @; "Type") typeRefTBody) 2.

(* Definition fromPDotG : stys := psAddStys primOptionG [pTop; pSymbol; pTypeRef]. *)
(** The syntactic stamp map we use in our syntactic judgments. *)
Definition fromPDotG : stys := psAddStys primOptionG [pTop; pSymbol].
Definition fromPDotG' : stys := pAddStys pTypeRef fromPDotG.
Definition fromPDotGφ := Vs⟦ fromPDotG' ⟧.
Opaque fromPDotG.
Opaque fromPDotG'.

Import stamp_transfer.
Lemma transfer : allGs ∅ ==∗ wellMappedφ fromPDotGφ.
Proof. apply transfer_empty. Qed.

Lemma pTopStamp : TyMemStamp fromPDotG pTop. Proof. split; stcrush. Qed.
Lemma pTypeRefStamp : TyMemStamp fromPDotG pTypeRef. Proof. split; stcrush. Qed.
Lemma pSymbolStamp : TyMemStamp fromPDotG pSymbol. Proof. split; stcrush. Qed.
Lemma Htop : styConforms fromPDotG pTop. Proof. done. Qed.
Lemma Hsymbol : styConforms fromPDotG pSymbol. Proof. done. Qed.
Lemma HtypeRef : styConforms fromPDotG' pTypeRef. Proof. done. Qed.

(* Import AssertPlain.
From D.Dot Require Import hoas. *)
Definition fromPDotPaperTypesV : vl := ν {@
  type "Type" =[ pTop ];
  type "TypeTop" =[ pTop ];
  val "newTypeTop" = vabs (ν {@ });
  type "TypeRef" =[ pTypeRef ];
  val "AnyType" = ν {@ };
  val "newTypeRef" = vabs (
    tif (tskip (tskip x0 @: "tpe") @: "isEmpty") (hclose hloopTm)
    (ν {@
      val "symb" = x1
    }));
  val "getTypeFromTypeRef" = vabs (
    tskip (tskip x0 @: "symb") @: "tpe" @: "get"
  )
}.

Definition fromPDotPaperSymbolsTBody pOpt : ty := {@
  typeEq "Symbol" $ {@
    val "tpe" : optionTy pOpt x1;
    val "id" : TNat
  }%ty;
  val "newSymbol" : optionTy pOpt x1 →: TNat →: x0 @; "Symbol"
}.

Definition fromPDotPaperAbsSymbolsTBody pOpt : ty := {@
  type "Symbol" >: ⊥ <: {@
    val "tpe" : optionTy pOpt x1;
    val "id" : TNat
  };
  val "newSymbol" : optionTy pOpt x1 →: TNat →: x0 @; "Symbol"
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
  val "types" = fromPDotPaperTypesV;
  val "symbols" = fromPDotPaperSymbolsV
}.

Definition optionModT := hclose hoptionModT.

Ltac semTMember i := iApply D_Typ; iApply (extraction_to_leadsto_envD_equiv (n := i) with "Hs"); by_extcrush.

Ltac simplSubst := rewrite /= /up/= /ids/ids_vl/=.

Ltac hideCtx' Γ :=
  let x := fresh "Γ" in set x := Γ.
Ltac hideCtx :=
  match goal with
  | |- ?Γ v⊢ₜ[ _ ] _ : _ => hideCtx' Γ
  | |- ?Γ v⊢ₜ[ _ ] _, _ <: _, _ => hideCtx' Γ
  | |- ?Γ v⊢ₚ[ _ ] _ : _, _  => hideCtx' Γ
  | |- ?Γ v⊢[ _ ]{ _ := _  } : _ => hideCtx' Γ
  | |- ?Γ v⊢ds[ _ ] _ : _ => hideCtx' Γ
  end.

Tactic Notation "smart_wp_bind'" uconstr(ctxs) ident(v) constr(Hv) uconstr(Hp) :=
  iApply (wp_bind (ectx_language.fill ctxs));
  iApply (wp_wand with "[-]"); [iApply Hp; trivial|];
  iIntros (v) Hv.

Lemma sem_later T a b c: V⟦TLater T⟧ a b c ⊣⊢ ▷ V⟦T⟧ a b c. Proof. done. Qed.

Example semFromPDotPaperTypesTyp Γ :
  TLater (fromPDotPaperAbsTBody x1) :: optionModTInv :: Γ ⊨[ fromPDotGφ ]
    fromPDotPaperTypesV : μ fromPDotPaperTypesTBody.
Proof.
  iIntros "#Hs".
  iApply T_Obj_I.
  iApply D_Cons; [done | semTMember 0 | ].
  iApply D_Cons; [done | semTMember 0 | ].
  iApply D_Cons; [done | iApply (fundamental_dm_typed with "Hs"); tcrush | ]. {
    eapply iT_Sub_nocoerce.
    + apply (iT_Mu_E (T := TTop)); tcrush.
    + apply (iSub_Sel' _ TTop); last (tcrush; varsub); stcrush. ltcrush.
  }
  iApply D_Cons; [done | semTMember 2 | ].
  iApply D_Cons; [done | iApply (fundamental_dm_typed with "Hs"); tcrush | ]. {
    eapply (iT_Sub_nocoerce (TMu ⊤)); first tcrush.
    eapply (iSub_Trans (T2 := ⊤) (i2 := 0)); tcrush.
    eapply (iSub_Trans (i2 := 1)); [exact: iSub_AddI | ].
    asideLaters.
    eapply (iSub_Sel' _ ⊤); tcrush.
    varsub; apply Sub_later_shift; tcrush.
  }

(*
  iApply D_Cons; [done | | ]. {
    iApply D_Val.
    iApply sT_All_I.
    (* Arguments setp : simpl never.
    cbn. *)
    iApply sT_If.
    admit.
    {
      iIntros "!> % ? !>".
      iApply wp_wand; [iApply loopSemT | iIntros "%[]"].
    }
    admit.
  } *)

  iApply D_Cons; [done | | ]. {
    (* iApply (fundamental_dm_typed with "Hs"); tcrush. *)
    (* XXX maybe strip this later (T_All_I_Strong can) but fix things up! *)
    set Γ1 :=
      fromPDotPaperTypesTBody :: fromPDotPaperAbsTBody x1 :: optionModTInv :: Γ.
    iApply D_Val.
    iApply (T_All_I_Strong (Γ' := Γ1)); first by rewrite /defCtxCons/=; ietp_weaken_ctx.
    set Γ2 := x2 @ "symbols" @; "Symbol" :: Γ1.

    (* Next: *)
    (* evar (T : ty). *)

    have Hx0 : Γ2 v⊢ₜ[ fromPDotG' ] x0 : x2 @ "symbols" @; "Symbol" by var.
    have Hsub0X0 :
      Γ2 v⊢ₜ[ fromPDotG' ] x2 @ "symbols" @; "Symbol", 0 <:
        val "tpe" : optionTy x3 x2 , 1. {
      (* eapply (iT_Sub (i := 1)); last typconstructor; first last. *)
      asideLaters.
      ettrans; last apply iLater_Sub; stcrush.
      eapply (iSel_Sub (L := ⊥)).
      (* Necessary: Pick this over [pv_dlater]. *)
      apply iP_Fld_E.
      tcrush; varsub.
      ltcrush; mltcrush.
    }

    have HoptSub0 :
      Γ2 v⊢ₜ[ fromPDotG' ] optionTy x3 x2, 0 <: hoptionTyConcr1 hoasNotation.hx2, 1. {
      tcrush.
      rewrite /hoptionTyConcr/optionTy.
      eapply (iSub_Trans (T2 := TAnd hoptionTConcr (type "T" >: ⊥ <: (x2 @ "types") @; "Type")) (i2 := 1));
        first apply iSub_And. {
        lThis.
        ettrans; last apply iLater_Sub; stcrush.
        eapply (iSel_Sub (L := ⊥) (U := hclose hoptionTConcr)).
        tcrush.
        varsub.
        mltcrush.
      }
      by ettrans; first apply iSub_Add_Later; stcrush; asideLaters; ltcrush.

      rewrite /hoptionTConcr/=.
      ettrans; first apply iAnd_Or_Sub_Distr; stcrush.
      apply iOr_Sub_split; ltcrush.
    }

    have HoptSub1 :
      Γ2 v⊢ₜ[ fromPDotG' ] optionTy x3 x2, 1 <: hoptionTyConcr1 hoasNotation.hx2, 2. {
      tcrush.
      rewrite /hoptionTyConcr/optionTy.
      eapply (iSub_Trans (T2 := TAnd hoptionTConcr (type "T" >: ⊥ <: (x2 @ "types") @; "Type")) (i2 := 2));
        first apply iSub_And. {
        lThis.
        ettrans; last apply iLater_Sub; stcrush.
        eapply (iSel_Sub (L := ⊥) (U := hclose hoptionTConcr)).
        tcrush.
        varsub.
        ettrans; first apply iSub_Add_Later; stcrush.
        asideLaters.
        mltcrush.
      }
      by ettrans; first apply iSub_Add_Later; stcrush; asideLaters; ltcrush.

      rewrite /hoptionTConcr/=.
      ettrans; first apply iAnd_Or_Sub_Distr; stcrush.
      apply iOr_Sub_split; ltcrush.
    }

    have HoptSubT :
      Γ2 v⊢ₜ[ fromPDotG' ] val "tpe" : optionTy x3 x2, 1 <: val "tpe" : TLater (hoptionTyConcr1 hoasNotation.hx2), 1. {
      tcrush. by asideLaters.
    }

    have Hx0' : Γ2 v⊢ₚ[ fromPDotG' ] x0 : val "tpe" : optionTy x3 x2, 1. {
      eapply (iP_Sub (i := 0)), iP_Val, Hx0. apply Hsub0X0.
    }

    have Hx0'' : Γ2 v⊢ₚ[ fromPDotG' ] x0 : val "tpe" : TLater (hoptionTyConcr1 hoasNotation.hx2), 1. {
      eapply (iP_Sub (i := 1)), Hx0'. apply HoptSubT.
    }
    have Hx0T : Γ2 v⊢ₜ[ fromPDotG' ] x0 : TLater (val "tpe" : TLater (hoptionTyConcr1 hoasNotation.hx2)). {
      eapply (iT_Sub (i := 0)), Hx0.
      ettrans; first apply Hsub0X0.
      ettrans; first apply HoptSubT.
      tcrush.
    }
    iIntros "!>" (ρ) "#Hg !>".
    (* iPoseProof (fundamental_path_typed _ _ _ _ _ Hx0'' with "Hs") as "Hx0". *)
    iPoseProof (fundamental_typed _ _ _ _ Hx0T with "Hs Hg") as "Hx0".
    iPoseProof (wp_value_inv with "Hx0") as "{Hx0} Hx0".
    iApply (wp_bind (fill [SkipCtx; ProjCtx _; SkipCtx; ProjCtx _; IfCtx _ _])).
    rewrite -wp_value.
    (* iApply (wp_bind (fill [SkipCtx; ProjCtx _; SkipCtx; ProjCtx _; IfCtx _ _])). *)
    iEval simplSubst; rewrite /of_val /vclose sem_later.
    iApply (wp_bind (fill [ProjCtx _; SkipCtx; ProjCtx _; IfCtx _ _])).
    rewrite -wp_pure_step_later -?wp_value; last done.
    iNext 1.
    iPoseProof "Hx0" as (d Hl p ->) "Hx0tpe".
    iApply (wp_bind (fill [SkipCtx; ProjCtx _; IfCtx _ _])); iSimpl.
    rewrite path_wp_eq; iDestruct "Hx0tpe" as (optV Hal) "HoptV".
    have [n HpOptV] := path_wp_exec_pure _ _ Hal.
    rewrite sem_later -wp_pure_step_later; last done.
    rewrite -wp_pure_step_later -1?wp_value; last done.
    iNext.
    iNext n.
    (* clear p Hl HpOptV n. *)
    (*
    iAssert ([] ⊨ optV @: "tpe" : ▶: hoptionTyConcr1 (λ x : var, hoasNotation.hx2 x)) as "Htpe". {
    iApply T_Obj_E.
    } *)
    iApply (wp_bind (fill [ProjCtx _; IfCtx _ _])); iSimpl.
    rewrite -wp_pure_step_later -1?wp_value /of_val; last done.
    iNext.
    rewrite /hoptionTyConcr1.
    iDestruct "HoptV" as "[Hw|Hw]";
      [ have Hv: Γ2 v⊢ₜ[ fromPDotG' ] hnoneConcrT, 0 <:
          val "isEmpty" : TSing true, 0 by mltcrush
      | have Hv: Γ2 v⊢ₜ[ fromPDotG' ] hsomeType hoasNotation.hx2, 0 <:
          val "isEmpty" : TSing false, 0 by lThis; mltcrush ];
      iPoseProof (fundamental_subtype _ _ _ _ _ _ Hv with "Hs") as "Hv";
      iDestruct ("Hv" $! _ optV with "Hg Hw") as (? Hl' pb ->) "{Hv} Hpb";
      iDestruct (path_wp_pure_exec with "Hpb") as %(bv & [n1 ?] & Heq); iClear "Hpb".
    all: move: Heq; rewrite alias_paths_pv_eq_2 path_wp_pure_pv_eq => Heq;
      iApply (wp_bind (fill [IfCtx _ _]));
      rewrite -wp_pure_step_later; last done;
      rewrite -wp_pure_step_later -1?wp_value; last done.
    all: iNext; iNext n1; iSimpl; simpl in Heq; rewrite -{}Heq.
    all: rewrite -wp_pure_step_later -1?wp_value; last done.
    by iApply wp_wand; [iApply loopSemT | iIntros "!>% []"].

    (* iPoseProof (fundamental_subtype _ _ _ _ _ _ Hv with "Hs") as "Ht".
    iDestruct ("Ht" $! _ optV with "Hg HwT") as (? Hl' pb ->) "{Ht} Hpb".
    iDestruct (path_wp_pure_exec with "Hpb") as %(bv & [n?] & Heq); iClear "Hpb".
    move: Heq; rewrite alias_paths_pv_eq_2 path_wp_pure_pv_eq => Heq.
    iApply (wp_bind (fill [IfCtx _ _])).
    rewrite -wp_pure_step_later; last done.
    rewrite -wp_pure_step_later -1?wp_value; last done.
    iNext.
    iNext n1.
    iSimpl.
    clear pb Hl H n.
    simpl in Heq; rewrite -{}Heq.
    rewrite -wp_pure_step_later -1?wp_value; last done. *)

    (* To conclude, prove the right subtyping for hsomeType and TypeRef. *)
    cbn in Hl.
    rewrite /hsomeType.
    set T := typeRefTBody; unfold typeRefTBody in T.
    (* sum up ingredient. We need to get typereftbody semantically, prove that's a subtype of abstract TypeRef*)
    iAssert (V⟦ val "tpe" : hsomeConcrT ⊥ ⊤ ⟧ vnil ρ (ρ 0)) as "#Hww". {
      iExists (dpt p); iFrame (Hl). iExists p; iSplit; first done.
      iApply path_wp_eq.
      iExists optV; iFrame (Hal).
      iDestruct "Hw" as "[$ _]".
    }

    iAssert (V⟦ TAnd ((x2 @ "symbols") @; "Symbol") (val "tpe" : hclose (hsomeConcrT ⊥ ⊤)) ⟧ vnil ρ (ρ 0)) as "#Hw1". {
      iDestruct "Hg" as "[_$]". iApply "Hww".
    }
    iAssert (V⟦ shift typeRefTBody ⟧ vnil ρ (ν [val "symb" = rename (+1) (ρ 0)])) as "#Hw2". {
      iSplit; last by [].
      iExists _; iSplit; first by eauto.
      iExists _; iSplit; first by [].
      rewrite path_wp_pv_eq.
      rewrite (_ : (rename (+1) (ρ 0)).[_] = ρ 0); last autosubst.
      iApply "Hw1".
    }
    have Hsublast : Γ2 v⊢ₜ[ fromPDotG' ] shift typeRefTBody, 0 <: x1 @; "TypeRef", 0. {
      eapply iSub_Sel'; tcrush.
      varsub.
      ltcrush.
      eapply iSub_Sel'; tcrush.
      varsub.
      ettrans; first apply iSub_Add_Later; stcrush.
      asideLaters.
      ltcrush.
    }

    iApply (fundamental_subtype _ _ _ _ _ _ Hsublast with "Hs Hg").
    iNext.
    iClear "Hx0 Hg Hs Hw Hww Hw1".
    iApply "Hw2".

    (* iPoseProof (fundamental_subtype _ _ _ _ _ _ Hsublast with "Hs Hg") as "Hsublast".
    iPoseProof

    have: Γ2 v⊢ₜ[ fromPDotG' ]
      ν {@ val "symb" = x1 } : x1 @; "TypeRef". {
    apply (iT_Sub (i := 0) (T1 := {@ val "symb" : x2 @ "symbols" @; "Symbol"})); first last.
    - apply: (iT_Mu_E (T :=
        {@ val "symb" : (x3 @ "symbols" @; "Symbol")})); tcrush.
      var.
    - ettrans; first last.
      eapply iSub_Sel'; first last.
      * constructor; varsub.
        ltcrush.
      * tcrush.
      * tcrush.
        eapply (iSub_Trans (T2 := ⊤)); tcrush.
        eapply iSub_Sel'; tcrush.
        varsub; tcrush.
        lThis.
        mltcrush.
        (* apply iT_Sub_nocoerce. *)
        admit.
    } *)


(*
    have Hopt'' : Γ2 v⊢ₜ[ fromPDotG' ] tskip (tskip x0) @: "tpe" :
      TLater hoptionTConcr. {
        tcrush.
        admit.
    }

    have Hcond : Γ2 v⊢ₜ[ fromPDotG' ]
      tskip (tskip (tskip x0) @: "tpe") @: "isEmpty" : TBool. {
      tcrush.
      eapply (iT_Sub (i := 1)); first apply iLater_Sub; stcrush.
      eapply (iT_Sub (i := 0)), Hopt''.
      mltcrush; eapply (iT_Sub (i := 0) (T1 := TBool)); tcrush.
    } *)


(*
Arguments iPPred_car : simpl never.
Arguments pty_interp : simpl never. *)
    (* cbn [iPPred_car pty_interp].


    smart_wp_bind' [SkipCtx; ProjCtx _; IfCtx _ _] optV "#Ha" ("Hopt" with "Hg").
    iPoseProof (fundamental_typed _ _ _ _ Hcond with "Hs") as "Hcond". *)

    (* simpl.
    simplSubst. *)

    (* smart_wp_bind' [SkipCtx; ProjCtx _; IfCtx _ _] optV "#Ha" ("Hopt" with "Hg").
    iDestruct "Ha" as "[HF|HT]".
    iApply (wp_bind (fill [IfCtx _ _])). *)

(*
    have Hopt : Γ2 v⊢ₜ[ fromPDotG' ]
      tskip x0 @: "tpe" : optionTy x3 x2. {
      (* eapply (iT_Sub (i := 1)); first apply iLater_Sub; stcrush. *)
      typconstructor.
      eapply (iT_Sub (i := 1)), Hx0. apply Hsub0X0.
    }

    have Hopt' : Γ2 v⊢ₜ[ fromPDotG' ]
      tskip (tskip x0 @: "tpe") : hoptionTyConcr1 hoasNotation.hx2. {
        tcrush.
      eapply (iT_Sub (i := 1)), Hopt. apply HoptSub0.
    } *)


    (* have HoptSub1 :
      Γ2 v⊢ₜ[ fromPDotG' ] optionTy x3 x2, 1 <:
      hclose hoptionTConcr, 2. {
        admit.
    } *)

    (* set foo := hTAnd (hsomeConcrT ⊥ ⊤) (type "T" >: ⊥ <: (hx2 @ "types") @; "Type"). *)
    (* have Hx0'' : Γ2 v⊢ₚ[ fromPDotG' ] x0 : val "tpe" : hoptionTyConcr hx2, 2. { *)

    (* rewrite /hoptionTyConcr1 in HoptSub'. *)

    (* have HoptSub :
      Γ2 v⊢ₜ[ fromPDotG' ] optionTy x3 x2, 1 <:
      hclose (hoptionTyConcr hoasNotation.hx2), 2. {
      tcrush.
      rewrite /hoptionTyConcr/optionTy.
      eapply (iSub_Trans (T2 := TAnd (hclose hoptionTConcr) (type "T" >: ⊥ <: (x2 @ "types") @; "Type")) (i2 := 2));
        first apply iSub_And. {
        lThis.
        ettrans; last apply iLater_Sub; stcrush.
        eapply (iSel_Sub (L := ⊥) (U := hclose hoptionTConcr)).
        tcrush.
        varsub.
        mltcrush; lThis.
      }
      by ettrans; first apply iSub_Add_Later; stcrush; asideLaters; ltcrush.
      rewrite /hoptionTConcr/=.
      ettrans; first apply iAnd_Or_Sub_Distr; stcrush.
      apply iOr_Sub_split; stcrush.
      ltcrush.
      Arguments hterm_lifting.liftBind /.
      rewrite /hsomeConcrT/hpmatchT; simplSubst.
      rewrite /=.
      apply Bind2; stcrush.
      mltcrush.
      by lThis; mltcrush.
      lThis; mltcrush.
      simplSubst.
      mltcrush.
      (* lNext. *)
      ltcrush.
      (* lThis.
      simplSubst. *)
      admit.
    } *)

    (* have Hopt' : Γ2 v⊢ₜ[ pAddStys pTypeRef fromPDotG ]
      tskip (tskip x0) @: "tpe" :
      TLater (hclose (hoptionTyConcr hoasNotation.hx2)). {
      eapply (iT_Sub (i := 0)), Hopt.
      (* ettrans; first apply iSub_Add_Later; stcrush. *)
      tcrush.
      rewrite /hoptionTyConcr/optionTy.
      eapply (iSub_Trans (T2 := TAnd (hclose hoptionTConcr) _) (i2 := 0));
        first apply iSub_And.
      (* XXX nope. *)
      lThis.
      ettrans.
      eapply (iSel_Sub (L := ⊥) (U := hclose hoptionTConcr)).
      tcrush.
      varsub.
      mltcrush; lThis.
      asideLaters.
      tcrush.
      admit.
    } *)

    (* Fails due to using optionModTInv. *)
    (* have Hcond : Γ2 v⊢ₜ[ pAddStys pTypeRef fromPDotG ]
      tskip (tskip (tskip x0) @: "tpe") : val "isEmpty" : TBool. {
      tcrush.
      eapply (iT_Sub (i := 1)); first apply iLater_Sub; stcrush.
      eapply (iT_Sub (i := 0)), Hopt; rewrite /optionTy.
      lThis.
      eapply (iSel_Sub (L := ⊥)).
      tcrush; varsub.
      mltcrush.
      (* Import hoasNotation. *)
      hideCtx.
      simplSubst.
      mltcrush.
      eapply (iT_Sub (i := 0) (T1:=TBool)); tcrush.
    } *)

    (* iPoseProof (fundamental_typed _ _ _ _ Hopt with "Hs") as "Hopt". *)

    (* XXX: Use iP_And. On the path x0! *)

    (* iPoseProof (fundamental_typed _ _ _ _ Hopt'' with "Hs") as "Hopt".
    iPoseProof (fundamental_typed _ _ _ _ Hcond with "Hs") as "Hcond".
    iIntros "!>" (ρ) "#Hg !>".
    (* simpl.
    simplSubst. *)

    (* smart_wp_bind' [SkipCtx; ProjCtx _; IfCtx _ _] optV "#Ha" ("Hopt" with "Hg").
    iDestruct "Ha" as "[HF|HT]".
    iApply (wp_bind (fill [IfCtx _ _])). *)

    smart_wp_bind' [IfCtx _ _] v "#Ha" ("Hcond" with "Hg").
    iEval simplSubst.
    iSimpl.
    iDestruct "Ha" as %[b Hbool]. simpl in b, Hbool; subst.
    destruct b.
    rewrite -wp_pure_step_later //.
    iApply wp_wand; [iApply loopSemT | iIntros "!>% []"].
    rewrite -wp_pure_step_later //.
    cbn. *)

    (* Split, semantically. *)

(*
    evar (T : ty).
    have : Γ0 v⊢ₜ[ pAddStys pTypeRef fromPDotG ] x0 : T; rewrite {}/T; first var.
    intros Hx0.

    evar (T : ty).
    have : Γ0 v⊢ₜ[ pAddStys pTypeRef fromPDotG ] x1 : T; rewrite {}/T; first var.
    intros Hx1.

    evar (T : ty).
    Arguments pTypeRef : simpl never.
    Arguments pAddStys : simpl never.
    have /= : Γ0 v⊢ₜ[ pAddStys pTypeRef fromPDotG ] x2 : T; rewrite {}/T; first var.
    intros _. *)

    (* evar (T : ty).
    have : Γ0 v⊢ₜ[ pAddStys pTypeRef fromPDotG ] x0 : T; rewrite {}/T. {
      eapply (iT_Sub (i := 0)), Hx0.
      (* ettrans; last apply iLater_Sub. *)
      eapply iSel_Sub.
      tcrush.
      varsub.
      asideLaters.
      mltcrush.
      simplSubst.
    } *)
    (* intros Hsx0. *)
(*
    rewrite /optionModT/hoptionModT/=.
    ltcrush.
    lThis.
    ltcrush.
    apply iP_Fld_E.
    mltcrush.
    ettrans.
    apply Bind1; stcrush.
    mltcrush.
    varsub.
    asideLaters.
    mltcrush.
    ltcrush. *)
    (* eapply (iSub_Trans (T2 := val "isEmpty" : TBool) (i2 := 3)); last admit.
    (* ettrans; first apply iSub_Add_Later; stcrush.
    asideLaters. *)
    ettrans; last apply iLater_Sub; stcrush. *)




    (* apply (iT_Sub (i := 0) (T1 := {@ val "symb" : x2 @ "symbols" @; "Symbol"})); first last.
    + apply: (iT_Mu_E (T :=
        {@ val "symb" : shift ((x2 @ "symbols") @; "Symbol")})); tcrush.
    + ettrans; first last.
      eapply iSub_Sel'; first last.
      * constructor; varsub.
        ltcrush.
      * tcrush.
      * tcrush.
        eapply (iSub_Trans (T2 := ⊤)); tcrush.
        eapply iSub_Sel'; tcrush.
        varsub; tcrush.
        admit. *)
  }
  iApply D_Cons; [done | iApply (fundamental_dm_typed with "Hs"); tcrush | ]. {
    set Γ' := x1 @; "TypeRef" :: fromPDotPaperTypesTBody ::
      (▶: fromPDotPaperAbsTBody x1)%ty :: optionModTInv :: Γ.
    (* have ?: Γ' v⊢ₜ[ pAddStys pTypeRef fromPDotG ] x0 : x1 @; "TypeRef"; first var. *)
    set T : ty := (▶: (shift typeRefTBody))%ty.
    unfold typeRefTBody in T.
    (* evar (T : ty). *)
    have : Γ' v⊢ₜ[ pAddStys pTypeRef fromPDotG ] x0 : T; rewrite {}/T. {
      varsub.
      ettrans.
      (* eapply (iSub_Trans (T2 := ▶: TAnd (x1 @; "Type") (shift typeRefTBody))); last by tcrush. *)

      + eapply iSel_Sub; typconstructor. varsub. ltcrush.
      + tcrush.
    }
    intros Hx.

    eapply (iT_Sub (i := 1) (T1 := TLater (TAnd ((x2 @ "symbols") @; "Symbol")
      (TLater (val "tpe" : hclose (hsomeConcrT ⊥ ⊤)))))); first last. {
      typconstructor; eapply (iT_Sub (i := 1)), Hx; asideLaters; ltcrush.
      ettrans; first apply iSub_Add_Later; tcrush; lNext.
    }
    asideLaters.
    ltcrush.
    asideLaters.
    ettrans.
    apply iSub_And_split, iSub_Refl; stcrush.
    eapply (iSel_Sub (L := ⊥) (U := val "tpe" : optionTy x3 x2)).
    apply iP_Fld_E.
    tcrush.
    varsub.
    asideLaters.
    mltcrush.
    by mltcrush.
    rewrite /optionTy.
    simplSubst.
    (* Next: try to use distributivity. *)
    (* ltcrush.
    lThis.
    hideCtx.
    cbn.
     last typconstructor; first last. *)

    (* eapply (iT_Sub (i := 0)); first last. *)
    (* eapply (iT_Sub (i := 1)), Hx.
    asideLaters.
    lThis.
    (* Throws away too much info! *)
    lNext.
    mltcrush.
    simplSubst. *)
    (* Sub_AddLater
    ettrans; last apply iLater_Sub; stcrush. {
    (* var. *)
    ettrans; last apply iLater_Sub. {
      eapply iSel_Sub; typconstructor; varsub. ltcrush.
    }
    stcrush.
    lNext. lThis.
    typconstructor. stcrush.
    eapply iT_Var_Sub.
    eapply iSub_Sel'. first last. *)
    admit.
  }
  iApply D_Nil.
Admitted.

(* Example fromPDotPaperTypesTyp Γ :
  TLater (fromPDotPaperAbsTBody x1) :: optionModTInv :: Γ v⊢ₜ[fromPDotG]
    fromPDotPaperTypesV : μ fromPDotPaperTypesTBody.
Proof.
  (* tcrush; try by [eapply iD_Typ; tcrush; by_extcrush]. *)
  apply iT_Obj_I; last stcrush.
  apply iD_Cons; [tMember | | done].
  apply iD_Cons; [tMember | | done].
  apply iD_Cons; [tcrush| | done]. {
    eapply iT_Sub_nocoerce.
    + apply (iT_Mu_E (T := TTop)); tcrush.
    + apply (iSub_Sel' _ TTop); last (tcrush; varsub); stcrush. ltcrush.
  }
  apply iD_Cons; [ | | done]. {
    tMember. (* TypeRef. *)
  }
  apply iD_Cons; [tcrush | | done]. {
    eapply (iT_Sub_nocoerce (TMu ⊤)); first tcrush.
    eapply (iSub_Trans (T2 := ⊤) (i2 := 0)); tcrush.
    eapply (iSub_Trans (i2 := 1)); [exact: iSub_AddI | ].
    asideLaters.
    eapply (iSub_Sel' _ ⊤); tcrush.
    varsub; apply Sub_later_shift; tcrush.
  }
  apply iD_Cons; [tcrush | | done]. {
    eapply iT_Sub_nocoerce.
    + apply (iT_Mu_E (T :=
        {@ val "symb" : shift ((x2 @ "symbols") @; "Symbol")})); tcrush.
    + ettrans; first last.
      eapply iSub_Sel'; first last.
      * constructor; varsub.
        ltcrush.
      * tcrush.
      * tcrush.
        eapply (iSub_Trans (T2 := ⊤)); tcrush.
        eapply iSub_Sel'; tcrush.
        varsub; tcrush.
        ltcrush.
        admit.
  }
  apply iD_Nil.
Qed. *)

Example fromPDotPaperTypesAbsTyp Γ :
  TLater (fromPDotPaperAbsTBody x1) :: optionModTInv :: Γ ⊨[fromPDotGφ]
    fromPDotPaperTypesV : μ fromPDotPaperAbsTypesTBody.
Proof.
  iIntros "#Hs".
  iApply (T_Sub (i := 0)).
  iApply (semFromPDotPaperTypesTyp with "Hs").
  iApply (fundamental_subtype with "Hs").
  ltcrush.
  (* eapply iT_Sub_nocoerce; first exact: fromPDotPaperTypesTyp; ltcrush. *)
  eapply iSub_Sel', (path_tp_delay (i := 0)); wtcrush.
  varsub; tcrush.
Qed.

Example fromPDotPaperSymbolsTyp Γ :
  TLater (fromPDotPaperAbsTBody x1) :: optionModTInv :: Γ v⊢ₜ[fromPDotG]
    fromPDotPaperSymbolsV : μ (fromPDotPaperSymbolsTBody x2).
Proof.
  tcrush.
  - tMember.
  - eapply (iT_Sub_nocoerce) => /=; hideCtx.
    + repeat first [var | typconstructor | tcrush].
    + ettrans; first last.
      eapply iSub_Sel'; first last.
      * constructor; varsub; tcrush.
      * tcrush.
      * mltcrush.
Qed.

Example fromPDotPaperSymbolsAbsTyp Γ :
  TLater (fromPDotPaperAbsTBody x1) :: optionModTInv :: Γ v⊢ₜ[fromPDotG]
    fromPDotPaperSymbolsV : μ (fromPDotPaperAbsSymbolsTBody x2).
Proof.
  eapply iT_Sub_nocoerce; first exact: fromPDotPaperSymbolsTyp; tcrush.
  lThis.
Qed.

Lemma storeless_objIdent_typing_mono_mut Γ g :
  (∀ e T, Γ v⊢ₜ[ g ] e : T → ∀ g' (Hle : g ⊆ g'), Γ v⊢ₜ[ g' ] e : T) ∧
  (∀ ds T, Γ v⊢ds[ g ] ds : T → ∀ g' (Hle : g ⊆ g'), Γ v⊢ds[ g' ] ds : T) ∧
  (∀ l d T, Γ v⊢[ g ]{ l := d } : T → ∀ g' (Hle : g ⊆ g'), Γ v⊢[ g' ]{ l := d } : T) ∧
  (∀ p T i, Γ v⊢ₚ[ g ] p : T, i → ∀ g' (Hle : g ⊆ g'), Γ v⊢ₚ[ g' ] p : T, i) ∧
  (∀ T1 i1 T2 i2, Γ v⊢ₜ[ g ] T1, i1 <: T2, i2 → ∀ g' (Hle : g ⊆ g'), Γ v⊢ₜ[ g' ] T1, i1 <: T2, i2).
Proof.
Hint Extern 5 (is_stamped_path _ _ _) => try_once is_stamped_mono_path : core.
  eapply storeless_typing_mut_ind with
      (P := λ Γ g e T _, ∀ g' (Hle : g ⊆ g'), Γ v⊢ₜ[ g' ] e : T)
      (P0 := λ Γ g ds T _, ∀ g' (Hle : g ⊆ g'), Γ v⊢ds[ g' ] ds : T)
      (P1 := λ Γ g l d T _, ∀ g' (Hle : g ⊆ g'), Γ v⊢[ g' ]{ l := d } : T)
      (P2 := λ Γ g p T i _, ∀ g' (Hle : g ⊆ g'), Γ v⊢ₚ[ g' ] p : T, i)
      (P3 := λ Γ g T1 i1 T2 i2 _, ∀ g' (Hle : g ⊆ g'), Γ v⊢ₜ[ g' ] T1, i1 <: T2, i2);
  clear Γ g; intros;
    repeat match goal with
    | H : forall g : stys, _ |- _ => specialize (H g' Hle)
    end; eauto 3; eauto.
  Qed.

Transparent wellMappedφ.
Lemma wellMappedφ_extend gφ1 gφ2 (Hle : gφ2 ⊆ gφ1):
    wellMappedφ gφ1 -∗ wellMappedφ gφ2.
Proof.
  iIntros "#Hs" (s φ Hl) "/= !>". iApply ("Hs" with "[%]").
  by eapply map_subseteq_spec, Hl.
Qed.
Opaque wellMappedφ.

Example fromPDotPaperTyp Γ : optionModTInv :: Γ ⊨[fromPDotGφ] fromPDotPaper : μ (fromPDotPaperAbsTBody x1).
Proof.
  iIntros "#Hs".
  iApply T_Obj_I.
  iApply D_Cons; [done| iApply D_Val |].
  iApply (fromPDotPaperTypesAbsTyp with "Hs").
  iApply D_Cons; [done| iApply D_Val | iApply D_Nil].
  (* Fix mismatch between maps; one is an extension. *)
  (* - Way 1, easier: weaken syntactic typing *)
  (* iApply (fundamental_typed with "Hs").
  eapply storeless_objIdent_typing_mono_mut.
  exact: fromPDotPaperSymbolsAbsTyp.
  eapply map_union_subseteq_r.
  (* cbn; solve_map_disjoint. *)
  by apply map_disjoint_singleton_l. *)
  (* - Way 2, harder: weaken wellMapped. *)

  iApply fundamental_typed.
  exact: fromPDotPaperSymbolsAbsTyp.
  iApply (wellMappedφ_extend with "Hs").
  intros s.
  destruct (fromPDotG !! s) as [T|] eqn:Heqs; rewrite !lookup_fmap Heqs/=; last by case_match.
  have Heq: ({[60%positive := TAnd (x0 @; "Type") typeRefTBody]} ∪ fromPDotG) !! s = Some T.
  eapply lookup_union_Some_r, Heqs. by apply map_disjoint_singleton_l.
  by simpl_map by exact: Heq.
Qed.

Definition getAnyTypeT pOpt : ty :=
  TAll (μ fromPDotPaperAbsTBody (shift pOpt)) (x0 @ "types" @; "Type").
Definition getAnyType : vl := vabs (tskip (tproj (tproj x0 "types") "AnyType")).

Definition fromPDotPaperAbsTypesTBodySubst : ty := {@
  type "Type" >: ⊥ <: ⊤;
  type "TypeTop" >: ⊥ <: x0 @ "types" @; "Type";
  val "newTypeTop" : ⊤ →: x0 @ "types" @; "TypeTop";
  type "TypeRef" >: ⊥ <: TAnd (x0 @ "types" @; "Type") ({@
    val "symb" : TAnd (x0 @ "symbols" @; "Symbol") (val "tpe" : hclose (hsomeConcrT ⊥ ⊤))
  });
  val "AnyType" : ▶: (x0 @ "types" @; "Type");
  val "newTypeRef" : x0 @ "symbols" @; "Symbol" →: x0 @ "types" @; "TypeRef";
  val "getTypeFromTypeRef" : x0 @ "types" @; "TypeRef" →: x0 @ "types" @; "Type"
}.

Lemma fromPDotPSubst: fromPDotPaperAbsTypesTBody .Tp[ (p0 @ "types") /]~ fromPDotPaperAbsTypesTBodySubst.
Proof. exact: psubst_ty_rtc_sufficient. Qed.

Example getAnyTypeFunTyp Γ : μ (fromPDotPaperAbsTBody x2) :: optionModTInv :: Γ v⊢ₜ[fromPDotG] getAnyType : getAnyTypeT x1.
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
