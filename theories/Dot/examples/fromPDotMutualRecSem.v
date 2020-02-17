(**
 *)
From stdpp Require Import strings.
From iris.proofmode Require Import tactics.

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

Set Implicit Arguments.
Set Suggest Proof Using.
Set Default Proof Using "Type*".

Section semExample.
Context `{HdlangG: dlangG Σ} `{!SwapPropI Σ}.
Import primOption.
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
    tif (tskip (tskip (tskip x0) @: "tpe") @: "isEmpty") (hclose hloopTm)
    (ν {@
      val "symb" = x1
    }));
  val "getTypeFromTypeRef" = vabs (
    (tskip x0 @: "tpe") @: "get"
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
Import prelude.

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

Section hoas.
  Import hoasNotation.
  Definition hoptionTyConcr pCore :=
    hTOr hnoneConcrT (hsomeConcrT
      ⊥
      (pCore @ "types" @; "Type")).
  Definition optionModTInvBody := hclose (μ: self, hoptionModTInvBody self).
End hoas.

Example semFromPDotPaperTypesTyp Γ :
  TLater (fromPDotPaperAbsTBody x1) :: optionModTInvBody :: Γ ⊨[ fromPDotGφ ]
    fromPDotPaperTypesV : μ fromPDotPaperTypesTBody.
Proof.
  iIntros "#Hs".
  iApply T_Obj_I.
  iApply D_Cons; [done | semTMember 0 | ].
  iApply D_Cons; [done | semTMember 0 | ].
  iApply D_Cons; [done | iApply (fundamental_dm_typed with "Hs"); tcrush | ]. {
    eapply Subs_typed_nocoerce.
    + apply (TMuE_typed (T := TTop)); tcrush.
    + apply (LSel_stp' _ TTop); last (tcrush; varsub); stcrush. ltcrush.
  }
  iApply D_Cons; [done | semTMember 2 | ].
  iApply D_Cons; [done | iApply (fundamental_dm_typed with "Hs"); tcrush | ]. {
    eapply (Subs_typed_nocoerce (TMu ⊤)); first tcrush.
    eapply (Trans_stp (T2 := ⊤) (i2 := 0)); tcrush.
    eapply (Trans_stp (i2 := 1)); [exact: AddI_stp | ].
    asideLaters.
    eapply (LSel_stp' _ ⊤); tcrush.
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
      fromPDotPaperTypesTBody :: fromPDotPaperAbsTBody x1 :: optionModTInvBody :: Γ.
    iApply D_Val.
    iApply (T_All_I_Strong (Γ' := Γ1)).
    Import later_sub_sem.
    rewrite /defCtxCons/=; ietp_weaken_ctx.
    set Γ2 := x2 @ "symbols" @; "Symbol" :: Γ1.

    (* Next: *)
    (* evar (T : ty). *)
    have Hopt : Γ2 v⊢ₜ[ fromPDotG' ]
      tskip (tskip x0) @: "tpe" : optionTy x3 x2. {
      (* eapply (Subs_typed (i := 1)); first apply TLaterL_stp; stcrush. *)
      tcrush.
      eapply (Subs_typed (i := 2)); last var.
      (* eapply (Subs_typed (i := 1)); last typconstructor; first last. *)
      ettrans; first apply TAddLater_stp; stcrush.
      asideLaters.
      ettrans; last apply TLaterL_stp; stcrush.
      eapply (SelU_stp (L := ⊥)).
      (* Necessary: Pick this over [pv_dlater]. *)
      apply pself_typed.
      tcrush; varsub.
      ettrans; first apply TAddLater_stp; stcrush.
      asideLaters.
      ltcrush; mltcrush.
    }

    have HoptSub' :
      Γ2 v⊢ₜ[ fromPDotG' ] optionTy x3 x2, 1 <:
      hclose hoptionTConcr, 2. {
        admit.
    }
    Import ectx_language prelude saved_interp_dep.
      Lemma swapSem {S T U i Γ}: Γ ⊨ TAnd (TOr S T) U , i <: TOr (TAnd S U) (TAnd T U), i.
      Proof.
        iIntros "!> %% #Hg [[HS|HT] Hu] !> /="; [iLeft|iRight]; iFrame.
      Qed.
      (* Lemma swap {S T U i Γ g}: Γ v⊢ₜ[ g ] TAnd (TOr S T) U , i <: TOr (TAnd S U) (TAnd T U), i.
      Proof.
        ettrans; last apply TOr_stp.
      Admitted. *)

    (* have HoptSub :
      Γ2 v⊢ₜ[ fromPDotG' ] optionTy x3 x2, 1 <:
      hclose (hoptionTyConcr hoasNotation.hx2), 2. {
      tcrush.
      rewrite /hoptionTyConcr/optionTy.
      eapply (Trans_stp (T2 := TAnd (hclose hoptionTConcr) (type "T" >: ⊥ <: (x2 @ "types") @; "Type")) (i2 := 2));
        first apply TAnd_stp. {
        lThis.
        ettrans; last apply TLaterL_stp; stcrush.
        eapply (SelU_stp (L := ⊥) (U := hclose hoptionTConcr)).
        tcrush.
        varsub.
        mltcrush; lThis.
      }
      by ettrans; first apply TAddLater_stp; stcrush; asideLaters; ltcrush.
      rewrite /hoptionTConcr/=.
      ettrans; first apply swap.
      Lemma TOr_stp_split Γ g T1 T2 U1 U2 i:
        is_stamped_ty (length Γ) g U1 →
        is_stamped_ty (length Γ) g U2 →
        Γ v⊢ₜ[ g ] T1, i <: U1, i →
        Γ v⊢ₜ[ g ] T2, i <: U2, i →
        Γ v⊢ₜ[ g ] TOr T1 T2, i <: TOr U1 U2, i.
      Proof.
        intros.
        apply TOr_stp; [
          eapply Trans_stp, TOr1_stp | eapply Trans_stp, TOr2_stp]; tcrush.
      Qed.
      apply TOr_stp_split; stcrush.
      ltcrush.
      lNext.
      ltcrush.
      (* lThis.


      simplSubst. *)
      admit.
    } *)

    have Hopt'' : Γ2 v⊢ₜ[ pAddStys pTypeRef fromPDotG ]
      tskip (tskip x0) @: "tpe" :
      TLater (hclose hoptionTConcr). {
        admit.
    }

    (* have Hopt' : Γ2 v⊢ₜ[ pAddStys pTypeRef fromPDotG ]
      tskip (tskip x0) @: "tpe" :
      TLater (hclose (hoptionTyConcr hoasNotation.hx2)). {
      eapply (Subs_typed (i := 0)), Hopt.
      (* ettrans; first apply TAddLater_stp; stcrush. *)
      tcrush.
      rewrite /hoptionTyConcr/optionTy.
      eapply (Trans_stp (T2 := TAnd (hclose hoptionTConcr) _) (i2 := 0));
        first apply TAnd_stp.
      (* XXX nope. *)
      lThis.
      ettrans.
      eapply (SelU_stp (L := ⊥) (U := hclose hoptionTConcr)).
      tcrush.
      varsub.
      mltcrush; lThis.
      asideLaters.
      tcrush.
      admit.
    } *)

    (* In fact, we want subtyping. *)
    have Hcond : Γ2 v⊢ₜ[ pAddStys pTypeRef fromPDotG ]
      tskip (tskip (tskip x0) @: "tpe") @: "isEmpty" : TBool. {
      tcrush.
      eapply (Subs_typed (i := 1)); first apply TLaterL_stp; stcrush.
      eapply (Subs_typed (i := 0)), Hopt''.
      mltcrush; eapply (Subs_typed (i := 0) (T1:=TBool)); tcrush.
    }

    (* Fails due to using optionModTInvBody. *)
    (* have Hcond : Γ2 v⊢ₜ[ pAddStys pTypeRef fromPDotG ]
      tskip (tskip (tskip x0) @: "tpe") : val "isEmpty" : TBool. {
      tcrush.
      eapply (Subs_typed (i := 1)); first apply TLaterL_stp; stcrush.
      eapply (Subs_typed (i := 0)), Hopt; rewrite /optionTy.
      lThis.
      eapply (SelU_stp (L := ⊥)).
      tcrush; varsub.
      mltcrush.
      (* Import hoasNotation. *)
      hideCtx.
      simplSubst.
      mltcrush.
      eapply (Subs_typed (i := 0) (T1:=TBool)); tcrush.
    } *)

    (* iPoseProof (fundamental_typed _ _ _ _ Hopt with "Hs") as "Hopt". *)
    (* XXX: Use pand_typed. On the path x0! *)
    iPoseProof (fundamental_typed _ _ _ _ Hopt'' with "Hs") as "Hopt".
    iPoseProof (fundamental_typed _ _ _ _ Hcond with "Hs") as "Hcond".
    iIntros "!>" (ρ) "#Hg !>".
  Tactic Notation "smart_wp_bind'" uconstr(ctxs) ident(v) constr(Hv) uconstr(Hp) :=
    iApply (wp_bind (ectx_language.fill ctxs));
    iApply (wp_wand with "[-]"); [iApply Hp; trivial|];
    iIntros (v) Hv.

    smart_wp_bind' [SkipCtx; ProjCtx _; IfCtx _ _] optV "#Ha" ("Hopt" with "Hg").
    iDestruct "Ha" as "[HF|HT]".
    iApply (wp_bind (fill [IfCtx _ _])).

    smart_wp_bind' [IfCtx _ _] v "#Ha" ("Hcond" with "Hg").
    iDestruct "Ha" as %[b Hbool]. simpl in b, Hbool; subst.
    destruct b.
    From D.pure_program_logic Require Import lifting.
    Import examples prelude.
    rewrite -wp_pure_step_later //.
    iApply wp_wand; [iApply loopSemT | iIntros "!>% []"].
    rewrite -wp_pure_step_later //.


    have: Γ2 v⊢ₜ[ pAddStys pTypeRef fromPDotG ]
      ν {@ val "symb" = x1 } : shift (x0 @; "TypeRef"). {
    apply (Subs_typed (i := 0) (T1 := {@ val "symb" : x2 @ "symbols" @; "Symbol"})); first last.
    - apply: (TMuE_typed (T :=
        {@ val "symb" : shift ((x2 @ "symbols") @; "Symbol")})); tcrush.
    - ettrans; first last.
      eapply LSel_stp'; first last.
      * constructor; varsub.
        ltcrush.
      * tcrush.
      * tcrush.
        eapply (Trans_stp (T2 := ⊤)); tcrush.
        eapply LSel_stp'; tcrush.
        varsub; tcrush.
        lThis.
        mltcrush.
        apply Subs_typed_nocoerce.
        tcrush.
    }

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
      eapply (Subs_typed (i := 0)), Hx0.
      (* ettrans; last apply TLaterL_stp. *)
      eapply SelU_stp.
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
    apply pself_typed.
    mltcrush.
    ettrans.
    apply Bind1; stcrush.
    mltcrush.
    varsub.
    asideLaters.
    mltcrush.
    ltcrush. *)
    (* eapply (Trans_stp (T2 := val "isEmpty" : TBool) (i2 := 3)); last admit.
    (* ettrans; first apply TAddLater_stp; stcrush.
    asideLaters. *)
    ettrans; last apply TLaterL_stp; stcrush. *)




    apply (Subs_typed (i := 0) (T1 := {@ val "symb" : x2 @ "symbols" @; "Symbol"})); first last.
    + apply: (TMuE_typed (T :=
        {@ val "symb" : shift ((x2 @ "symbols") @; "Symbol")})); tcrush.
    + ettrans; first last.
      eapply LSel_stp'; first last.
      * constructor; varsub.
        ltcrush.
      * tcrush.
      * tcrush.
        eapply (Trans_stp (T2 := ⊤)); tcrush.
        eapply LSel_stp'; tcrush.
        varsub; tcrush.
        admit.
  } *)
  iApply D_Cons; [done | iApply (fundamental_dm_typed with "Hs"); tcrush | ]. {
    set Γ' := x1 @; "TypeRef" :: fromPDotPaperTypesTBody ::
      (▶: fromPDotPaperAbsTBody x1)%ty :: optionModT :: Γ.
    (* have ?: Γ' v⊢ₜ[ pAddStys pTypeRef fromPDotG ] x0 : x1 @; "TypeRef"; first var. *)
    set T : ty := (▶: (shift typeRefTBody))%ty.
    unfold typeRefTBody in T.
    (* evar (T : ty). *)
    have : Γ' v⊢ₜ[ pAddStys pTypeRef fromPDotG ] x0 : T; rewrite {}/T. {
      varsub.
      ettrans.
      (* eapply (Trans_stp (T2 := ▶: TAnd (x1 @; "Type") (shift typeRefTBody))); last by tcrush. *)

      + eapply SelU_stp; typconstructor. varsub. ltcrush.
      + tcrush.
    }
    intros Hx.

    (* eapply (Subs_typed (i := 1)); last typconstructor; first last. *)
    (* eapply (Subs_typed (i := 0)); first last. *)
    eapply (Subs_typed (i := 1)), Hx.
    asideLaters.
    lThis.
    (* Throws away too much info! *)
    lNext.
    mltcrush.
    simplSubst.
    (* Sub_AddLater
    ettrans; last apply TLaterL_stp; stcrush. {
    (* var. *)
    ettrans; last apply TLaterL_stp. {
      eapply SelU_stp; typconstructor; varsub. ltcrush.
    }
    stcrush.
    lNext. lThis.
    typconstructor. stcrush.
    eapply Var_typed_sub.
    eapply LSel_stp'. first last. *)
    admit.
  }
  iApply D_Nil.
Admitted.

(* Example fromPDotPaperTypesTyp Γ :
  TLater (fromPDotPaperAbsTBody x1) :: optionModT :: Γ v⊢ₜ[fromPDotG]
    fromPDotPaperTypesV : μ fromPDotPaperTypesTBody.
Proof.
  (* tcrush; try by [eapply Dty_typed; tcrush; by_extcrush]. *)
  apply VObj_typed; last stcrush.
  apply dcons_typed; [tMember | | done].
  apply dcons_typed; [tMember | | done].
  apply dcons_typed; [tcrush| | done]. {
    eapply Subs_typed_nocoerce.
    + apply (TMuE_typed (T := TTop)); tcrush.
    + apply (LSel_stp' _ TTop); last (tcrush; varsub); stcrush. ltcrush.
  }
  apply dcons_typed; [ | | done]. {
    tMember. (* TypeRef. *)
  }
  apply dcons_typed; [tcrush | | done]. {
    eapply (Subs_typed_nocoerce (TMu ⊤)); first tcrush.
    eapply (Trans_stp (T2 := ⊤) (i2 := 0)); tcrush.
    eapply (Trans_stp (i2 := 1)); [exact: AddI_stp | ].
    asideLaters.
    eapply (LSel_stp' _ ⊤); tcrush.
    varsub; apply Sub_later_shift; tcrush.
  }
  apply dcons_typed; [tcrush | | done]. {
    eapply Subs_typed_nocoerce.
    + apply (TMuE_typed (T :=
        {@ val "symb" : shift ((x2 @ "symbols") @; "Symbol")})); tcrush.
    + ettrans; first last.
      eapply LSel_stp'; first last.
      * constructor; varsub.
        ltcrush.
      * tcrush.
      * tcrush.
        eapply (Trans_stp (T2 := ⊤)); tcrush.
        eapply LSel_stp'; tcrush.
        varsub; tcrush.
        ltcrush.
        admit.
  }
  apply dnil_typed.
Qed. *)

Example fromPDotPaperTypesAbsTyp Γ :
  TLater (fromPDotPaperAbsTBody x1) :: optionModT :: Γ ⊨[fromPDotGφ]
    fromPDotPaperTypesV : μ fromPDotPaperAbsTypesTBody.
Proof.
  iIntros "#Hs".
  iApply (T_Sub (i := 0)).
  iApply (semFromPDotPaperTypesTyp with "Hs").
  iApply (fundamental_subtype with "Hs").
  ltcrush.
  (* eapply Subs_typed_nocoerce; first exact: fromPDotPaperTypesTyp; ltcrush. *)
  eapply LSel_stp', (path_tp_delay (i := 0)); wtcrush.
  varsub; tcrush.
Qed.

Example fromPDotPaperSymbolsTyp Γ :
  TLater (fromPDotPaperAbsTBody x1) :: optionModT :: Γ v⊢ₜ[fromPDotG]
    fromPDotPaperSymbolsV : μ (fromPDotPaperSymbolsTBody x2).
Proof.
  tcrush.
  - tMember.
  - eapply (Subs_typed_nocoerce) => /=; hideCtx.
    + repeat first [var | typconstructor | tcrush].
    + ettrans; first last.
      eapply LSel_stp'; first last.
      * constructor; varsub; tcrush.
      * tcrush.
      * mltcrush.
Qed.

Example fromPDotPaperSymbolsAbsTyp Γ :
  TLater (fromPDotPaperAbsTBody x1) :: optionModT :: Γ v⊢ₜ[fromPDotG]
    fromPDotPaperSymbolsV : μ (fromPDotPaperAbsSymbolsTBody x2).
Proof.
  eapply Subs_typed_nocoerce; first exact: fromPDotPaperSymbolsTyp; tcrush.
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
    eapply stamped_typing_mut_ind with
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

Example fromPDotPaperTyp Γ : optionModT :: Γ ⊨[fromPDotGφ] fromPDotPaper : μ (fromPDotPaperAbsTBody x1).
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
  val "newTypeRef" : x0 @ "symbols" @; "Symbol" →: x0 @ "types" @; "TypeRef"
}.

Lemma fromPDotPSubst: fromPDotPaperAbsTypesTBody .Tp[ (p0 @ "types") /]~ fromPDotPaperAbsTypesTBodySubst.
Proof. exact: psubst_ty_rtc_sufficient. Qed.

Example getAnyTypeFunTyp Γ : μ (fromPDotPaperAbsTBody x2) :: optionModT :: Γ v⊢ₜ[fromPDotG] getAnyType : getAnyTypeT x1.
Proof.
  rewrite /getAnyType; tcrush.
  eapply (Subs_typed (T1 := TLater (x0 @ "types" @; "Type")) (i := 1)); tcrush.
  set Γ' := shift (μ (fromPDotPaperAbsTBody x2)) ::
    μ (fromPDotPaperAbsTBody x2) :: optionModT :: Γ.
  have Hpx: Γ' v⊢ₚ[fromPDotG] x0 @ "types" : μ fromPDotPaperAbsTypesTBody, 0
    by tcrush; eapply Subs_typed_nocoerce;
      [ by eapply TMuE_typed; first var; stcrush | tcrush].
  have HpxSubst: Γ' v⊢ₚ[fromPDotG] x0 @ "types" : fromPDotPaperAbsTypesTBodySubst, 0.
  by eapply (p_mu_e_typed (T := fromPDotPaperAbsTypesTBody)
    (p := x0 @ "types")), Hpx; tcrush; exact: fromPDotPSubst.
  eapply (Path_typed (p := x0)), pself_inv_typed, (p_subs_typed (i := 0)), HpxSubst.
  repeat lNext.
Qed.

Example getAnyTypeTyp0 Γ :
  μ (fromPDotPaperAbsTBody x2) :: optionModT :: Γ v⊢ₜ[fromPDotG]
    tapp getAnyType x0 : x0 @ "types" @; "Type".
Proof. eapply Appv_typed'; [exact: getAnyTypeFunTyp|var|tcrush..]. Qed.
End semExample.
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
