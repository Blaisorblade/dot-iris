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
Definition fromPDotPaperTypesVBody : dms := {@
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
    tskip (tskip (tskip (tskip (tskip x0 @: "symb")) @: "tpe" @: "get"))
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
  val "types" = ν fromPDotPaperTypesVBody;
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

(* Adapted from [typing_unstamped_derived.v]. *)
Lemma iAnd_Later_Sub_Distr Γ T1 T2 i g :
  is_stamped_ty (length Γ) g T1 →
  is_stamped_ty (length Γ) g T2 →
  Γ v⊢ₜ[ g ] TAnd (TLater T1) (TLater T2), i <: TLater (TAnd T1 T2), i.
Proof. intros; asideLaters; tcrush; [lThis|lNext]. Qed.

Lemma iP_Sub' {Γ p T1 T2 i g} :
  Γ v⊢ₜ[g] T1, i <: T2, i →
  Γ v⊢ₚ[g] p : T1, i →
  Γ v⊢ₚ[g] p : T2, i.
Proof.
  intros; rewrite -(plusnO i).
  by eapply (iP_Sub 0); rewrite ?plusnO.
Qed.

Lemma iP_Sngl_Sym Γ p q g i:
  is_stamped_path (length Γ) g q →
  Γ v⊢ₚ[g] p : TSing q, i →
  Γ v⊢ₚ[g] q : TSing p, i.
Proof.
  intros Hus Hpq. eapply iP_Sub'.
  eapply (iSngl_Sub_Sym Hpq). by apply iSngl_Sub_Self, Hpq.
  eapply iP_Sngl_Refl.
  by apply (iP_Sngl_Inv Hpq).
Qed.

Lemma iSngl_pq_Sub_inv {Γ i p q T1 T2 g}:
  T1 ~Tp[ p := q ]* T2 →
  is_stamped_ty   (length Γ) g T1 →
  is_stamped_ty   (length Γ) g T2 →
  is_stamped_path (length Γ) g p →
  Γ v⊢ₚ[g] q : TSing p, i →
  Γ v⊢ₜ[g] T1, i <: T2, i.
Proof. intros. by eapply iSngl_pq_Sub, iP_Sngl_Sym. Qed.


Lemma ty_sub_TAnd_TLater_TAnd_distr_inv T U :
  ⊢T TAnd (TLater T) (TLater U) <: TLater (TAnd T U).
Admitted.

Typeclasses Opaque pty_interp.

Lemma newTypeRef_semTyped Γ  :
  shift ((x1 @ "symbols") @; "Symbol") ::
    TAnd fromPDotPaperTypesTBody (TSing (x1 @ "types")) ::
    fromPDotPaperAbsTBody x1 :: optionModTInv :: Γ ⊨[ fromPDotGφ ]
    tif (tskip (tskip x0 @: "tpe") @: "isEmpty")
      (hclose hloopTm)
      (ν {@ val "symb" = x1 }) : shift (x0 @; "TypeRef").
Proof.
  set Γ2 :=
    x2 @ "symbols" @; "Symbol" ::
    TAnd fromPDotPaperTypesTBody (TSing (x1 @ "types")) ::
    fromPDotPaperAbsTBody x1 :: optionModTInv :: Γ.

  have Hx0 : Γ2 v⊢ₜ[ fromPDotG' ] x0 : x2 @ "symbols" @; "Symbol" by var.
  have Hsub0X0 :
    Γ2 v⊢ₜ[ fromPDotG' ] x2 @ "symbols" @; "Symbol", 0 <:
      val "tpe" : optionTy x3 x2 , 1. {
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
    Γ2 v⊢ₜ[ fromPDotG' ]
      val "tpe" : optionTy x3 x2, 1 <:
      val "tpe" : TLater (hoptionTyConcr1 hoasNotation.hx2), 1. {
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
  iIntros "#Hs !>" (ρ) "#Hg !>".
  iPoseProof (fundamental_typed _ _ _ _ Hx0T with "Hs Hg") as "Hx0".
  iDestruct (wp_value_inv with "Hx0") as "{Hx0} Hx0".
  (* iApply (wp_bind (fill [SkipCtx; ProjCtx _; SkipCtx; ProjCtx _; IfCtx _ _])).
  rewrite -wp_value. *)
  (* iApply (wp_bind (fill [SkipCtx; ProjCtx _; SkipCtx; ProjCtx _; IfCtx _ _])). *)
  iEval simplSubst; rewrite /of_val /vclose sem_later.
  iApply (wp_bind (fill [ProjCtx _; SkipCtx; ProjCtx _; IfCtx _ _])).
  rewrite -wp_pure_step_later -?wp_value; last done.
  iNext 1.
  iEval (cbv [pty_interp]) in "Hx0".
  iPoseProof "Hx0" as (d Hl p ->) "{Hx0} Hx0tpe".
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
  iEval (cbv [pty_interp]) in "HoptV".
  iDestruct "HoptV" as "[Hw|Hw]";
    [ have Hv: Γ2 v⊢ₜ[ fromPDotG' ] hnoneConcrT, 0 <:
        val "isEmpty" : TSing true, 0 by mltcrush
    | have Hv: Γ2 v⊢ₜ[ fromPDotG' ] hsomeType hoasNotation.hx2, 0 <:
        val "isEmpty" : TSing false, 0 by lThis; mltcrush ];
    iPoseProof (fundamental_subtype _ _ _ _ _ _ Hv with "Hs") as "Hv".
  all: iSpecialize ("Hv" $! _ optV with "Hg Hw");
    iEval (cbv [pty_interp]; cbn) in "Hv";
    iDestruct "Hv" as (? Hl' pb ->) "Hpb";
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
    iSimpl.
    iExists (dpt p); iFrame (Hl). iExists p; iSplit; first done.
    iApply path_wp_eq.
    iExists optV; iFrame (Hal).
    iEval (cbv [pty_interp]) in "Hw"; iDestruct "Hw" as "[$ _]".
  }

  iAssert (V⟦ TAnd ((x2 @ "symbols") @; "Symbol") (val "tpe" : hclose (hsomeConcrT ⊥ ⊤)) ⟧ vnil ρ (ρ 0)) as "#Hw1". {
    iDestruct "Hg" as "[_ H]".
    iEval (cbv [pty_interp]; cbn -[pty_interp]) in "H".
    iEval (cbv [pty_interp]; cbn -[pty_interp]).
    iFrame "H"; iApply "Hww".
  }
  iAssert (V⟦ shift typeRefTBody ⟧ vnil ρ (ν [val "symb" = rename (+1) (ρ 0)])) as "#Hw2". {
    iEval (cbv [pty_interp]; cbn -[pty_interp]).
    iSplit; last by [].
    iExists _; iSplit; first by eauto.
    iExists _; iSplit; first by [].
    rewrite path_wp_pv_eq.
    rewrite (_ : (rename (+1) (ρ 0)).[_] = ρ 0); last autosubst.
    iApply "Hw1".
  }
  have Hsublast : Γ2 v⊢ₜ[ fromPDotG' ] shift typeRefTBody, 0 <: x1 @; "TypeRef", 0. {
    eapply iSub_Sel'; tcrush.
    varsub; lThis.
    ltcrush.
    eapply iSub_Sel'; tcrush.
    varsub; lThis.
    ettrans; first apply iSub_Add_Later; stcrush.
    asideLaters.
    ltcrush.
  }

  iPoseProof (fundamental_subtype _ _ _ _ _ _ Hsublast with "Hs Hg") as "Hsub".
  iEval (cbv [pty_interp]) in "Hsub".
  iApply ("Hsub" with "Hw2").
Qed.

(*
Arguments iPPred_car : simpl never.
Arguments pty_interp : simpl never. *)
    (* cbn [iPPred_car pty_interp].


     *)


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

Lemma assoc_and {Γ S T U i g} :
  is_stamped_ty (length Γ) g S →
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (length Γ) g U →
  Γ v⊢ₜ[ g ] TAnd (TAnd S T) U, i <: TAnd S (TAnd T U), i.
Proof. intros. tcrush; lThis. Qed.
Lemma iP_And {Γ p T1 T2 i g}:
  Γ v⊢ₚ[g] p : T1, i →
  Γ v⊢ₚ[g] p : T2, i →
  Γ v⊢ₚ[g] p : TAnd T1 T2, i.
Proof.
  intros Hp1 Hp2. eapply iP_Sub', iP_Sngl_Refl, Hp1.
  constructor; exact: iSngl_Sub_Self.
Qed.

Lemma iLaterN_Sub {Γ T g i j} :
  is_stamped_ty (length Γ) g T →
  Γ v⊢ₜ[g] iterate TLater j T, i <: T, j + i.
Proof.
  elim: j T => /= [|j IHj] T HuT; rewrite ?iterate_0 ?iterate_Sr /=; tcrush.
  ettrans.
  - apply (IHj (TLater T)); stcrush.
  - exact: iLater_Sub.
Qed.

(* Argh, no aliasing here. *)
Example semFromPDotPaperTypesTyp Γ :
  (* TLater (fromPDotPaperAbsTBody x1) :: optionModTInv :: Γ ⊨
    ν fromPDotPaperTypesVBody : μ fromPDotPaperTypesTBody. *)
  TAnd (▶: fromPDotPaperTypesTBody) (TSing (x1 @ "types")) ::
  TLater (fromPDotPaperAbsTBody x1) :: optionModTInv :: Γ
  ⊨ds[ fromPDotGφ ] fromPDotPaperTypesVBody : fromPDotPaperTypesTBody.
Proof.
  set Γ' := TAnd fromPDotPaperTypesTBody (TSing (x1 @ "types")) ::
    fromPDotPaperAbsTBody x1 :: optionModTInv :: Γ.
  have Hctx:
    ⊢G TAnd (▶: fromPDotPaperTypesTBody) (TSing (x1 @ "types")) ::
    (▶: fromPDotPaperAbsTBody x1)%ty :: optionModTInv :: Γ <:* (TLater <$> Γ'). {
    constructor; last by ietp_weaken_ctx.
    eapply ty_trans_sub_syn, ty_sub_TAnd_TLater_TAnd_distr_inv.
    ietp_weaken_ctx.
  }

  iIntros "#Hs".
  iApply D_Cons; [done | semTMember 0 | ].
  iApply D_Cons; [done | semTMember 0 | ].
  iApply D_Cons; [done | iApply (fundamental_dm_typed with "Hs") | ]. {
    typconstructor.
    apply (iT_All_I_Strong (Γ' := Γ')); tcrush.
    eapply iT_Sub_nocoerce.
    + apply (iT_Mu_E (T := TTop)); tcrush.
    + apply (iSub_Sel' _ TTop); tcrush; varsub. lThis; ltcrush.
  }
  iApply D_Cons; [done | semTMember 2 | ].
  iApply D_Cons; [done | iApply (fundamental_dm_typed with "Hs")| ]. {
    tcrush.
    eapply (iT_Sub_nocoerce (TMu ⊤)); first tcrush.
    eapply (iSub_Trans (T2 := ⊤) (i2 := 0)); tcrush.
    eapply (iSub_Trans (i2 := 1)); [exact: iSub_AddI | ].
    asideLaters.
    eapply (iSub_Sel' _ ⊤); tcrush. varsub; lThis.
  }
  iApply D_Cons; [done | | ]. {
    iApply D_Val.
    iApply (T_All_I_Strong (Γ' := Γ')); first by rewrite /defCtxCons/=; ietp_weaken_ctx.
    iApply (newTypeRef_semTyped with "Hs").
  }

  iApply D_Cons; [done | iApply (fundamental_dm_typed with "Hs")| ]. {
    typconstructor.
    apply (iT_All_I_Strong (Γ' := Γ')); tcrush.
    set Γ1 := x1 @; "TypeRef" :: Γ'.
    (* have ?: Γ' v⊢ₜ[ pAddStys pTypeRef fromPDotG ] x0 : x1 @; "TypeRef"; first var. *)
    set T : ty := (▶: (shift typeRefTBody))%ty.
    unfold typeRefTBody in T.
    (* evar (T : ty). *)
    have : Γ1 v⊢ₜ[ fromPDotG' ] x0 : T; rewrite {}/T. {
      varsub.
      ettrans.
      (* eapply (iSub_Trans (T2 := ▶: TAnd (x1 @; "Type") (shift typeRefTBody))); last by tcrush. *)

      + eapply iSel_Sub; typconstructor. varsub. lThis. ltcrush.
      + tcrush.
    }
    intros Hx.

    (* The proper fix might be to use intersections introduction and Fld_I here.
    (A) on the one hand, show what x.T is.
    (B) on the other hand, thanks to hsomeConcr, we have a get method.
    *)
    (* suff Hx' : Γ1 v⊢ₜ[ fromPDotG' ] x0 : ▶: val "symb" : val "tpe" : val "get" : x1 @; "Type". {
      eapply (iT_Sub (i := 2)); first last.
      by typconstructor; eapply (iT_Sub (i := 1)), Hx'; asideLaters; ltcrush.
      ettrans; first apply iSub_Add_Later; tcrush.
      ettrans; first apply iSub_Add_Later; tcrush.
      asideLaters.
      tcrush.
    }
    (* eapply (iT_Path (p := pv _)).
    typconstructor.  *)
    (* iP_Val. *)

    (* have Hx0 : Γ1 v⊢ₜ[ fromPDotG' ] x0 : ▶: val "symb" : val "tpe" : μ (val "get" : ▶: x0 @; "T"). {
    (* have Hx0 : Γ1 v⊢ₜ[ fromPDotG' ] x0 : ▶: val "symb" : val "tpe" : val "get" : T. { *)
      eapply (iT_Sub (i := 0)), Hx.
      ltcrush.
      lNext.
      rewrite /hsomeConcrT/=; simplSubst.
      ltcrush.
    } *)

    eapply (iT_Sub (i := 0)), Hx.
    ltcrush.
    apply iSub_Skolem_P; tcrush.
    simplSubst; rewrite !iterate_S !iterate_0; hideCtx.
    varsub.
    lNext.
    ltcrush.

    constructor.

    (* varsub.
    eapply (iSub_Trans (T2 := ▶: (val "symb" : (val "tpe" : (val "get" : x2 @ "types" @; "Type" ))))),
    (iSngl_pq_Sub_inv (q := x1) (p := x2 @ "types")); stcrush; first 1 last.
    exact: psubst_ty_rtc_sufficient.
    by tcrush; varsub; lNext.




    eapply (iSel_Sub (L := ⊥)).
    tcrush.
    varsub.
    lThis.
    mltcrush. *) *)
    eapply (iT_Sub (i := 2)); first apply (iLaterN_Sub (j := 2)); tcrush.

    eapply (iT_Sub (i := 2) (T1 := (TLater (TAnd ((x2 @ "symbols") @; "Symbol")
      (TLater (val "tpe" : hclose (hsomeConcrT ⊥ ⊤))))))); first last. {
      typconstructor; eapply (iT_Sub (i := 1)), Hx. asideLaters. ltcrush.
      ettrans; first apply iSub_Add_Later; tcrush; lNext.
    }
    asideLaters.
    ettrans.
    apply iSub_And_split, iSub_Refl; stcrush.
    eapply (iSel_Sub (L := ⊥) (U := val "tpe" : optionTy x3 x2)).
    apply iP_Fld_E.
    tcrush.
    varsub.
    asideLaters.
    mltcrush.
    ettrans; first apply iSub_Add_Later; stcrush.
    asideLaters.
    by mltcrush.
    rewrite /optionTy; simplSubst.
    (* Next: try to use distributivity. *)
    ettrans; first apply iAnd_Later_Sub_Distr; stcrush.
    asideLaters.
    ettrans; first apply iAnd_Fld_Sub_Distr; stcrush.
    tcrush.
    eapply (iSub_Trans (T2 := val "get" : ▶: ▶: x2 @ "types" @; "Type")),
      (iSngl_pq_Sub_inv (q := x1) (p := x2 @ "types"));
      stcrush; [|exact: psubst_ty_rtc_sufficient|]; first last. {
      tcrush; varsub; asideLaters. lNext.
      by ettrans; first apply (iSub_AddIJ' (j := 2)); wtcrush.
    }
    ettrans; first apply assoc_and; stcrush.
    lNext.
    rewrite /hsomeConcrT; simplSubst.
    apply iSub_Skolem_P; stcrush.
    rewrite !iterate_S !iterate_0; hideCtx. simplSubst.
    eapply (iP_Sub' (T1 := (TAnd (val "get" : ▶: x0 @; "T")
      (type "T" >: ⊥ <: (x3 @ "types") @; "Type")))); first last.
    apply iP_And; last by tcrush; varsub; tcrush. {
      apply (iP_Mu_E (p := x0) (T := ((val "get" : ▶: x0 @; "T" )))).
      exact: psubst_ty_rtc_sufficient.
      stcrush.
      tcrush.
      varsub. asideLaters. lNext. ltcrush.
    }
    lThis.
    eapply (iSel_Sub (L := ⊥)); tcrush.
    varsub.
    mltcrush.
    lThis.
    (* mltcrush.

    apply iSub_Skolem_P; stcrush.
    mltcrush.
    hideCtx.
    simplSubst.
    tcrush.
    tcrush.

    have Hsub : Γ1 v⊢ₜ[ fromPDotG' ]
      val "get" : x2 @ "types" @; "Type" , 2 <: val "get" : x1 @; "Type" , 2. {
        admit.
    }
    eapply iSub_Trans, Hsub.
    lNext.
    mltcrush.
    eapply iSub_Sel.
    ltcrush. *)


    (* Very annoying distributivity. Prove this in the model? *)

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
  }
  iApply D_Nil.
Qed.

Lemma fromPDotPaperTypesSub Γ:
(▶: fromPDotPaperAbsTBody x1)%ty :: optionModTInv :: Γ ⊨[ fromPDotGφ
] μ fromPDotPaperTypesTBody, 0 <: μ fromPDotPaperAbsTypesTBody, 0.
Proof.
  iApply fundamental_subtype.
  ltcrush.
  (* eapply iT_Sub_nocoerce; first exact: fromPDotPaperTypesTyp; ltcrush. *)
  eapply iSub_Sel', (path_tp_delay (i := 0)); wtcrush.
  varsub; tcrush.
Qed.

(* Example fromPDotPaperTypesAbsTyp Γ :
  TLater (fromPDotPaperAbsTBody x1) :: optionModTInv :: Γ ⊨[fromPDotGφ]
    ν fromPDotPaperTypesVBody : μ fromPDotPaperAbsTypesTBody.
Proof.
  iIntros "#Hs".
  iApply (T_Sub (i := 0)).
  iApply (semFromPDotPaperTypesTyp with "Hs").
  iApply (fromPDotPaperTypesSub with "Hs").
Qed. *)

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
  iApply D_Cons; [done| |].
  iApply D_Path_Sub; [iApply (fromPDotPaperTypesSub with "Hs") | iApply D_Val_New].
  iApply (semFromPDotPaperTypesTyp with "Hs").

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
