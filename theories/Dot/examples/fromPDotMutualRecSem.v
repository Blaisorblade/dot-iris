(**
 *)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot.syn Require Import syn path_repl.
From D.Dot.typing Require Import typing_storeless.
From D.Dot Require Import exampleInfra typingExInfra examples.
(* From D.Dot Require Import typingExamples. *)
From D.Dot Require Import primOption.

From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr
  lr_lemmas lr_lemmasTSel lr_lemmasNoBinding lr_lemmasDefs lr_lemmasPrim.
From D.Dot Require Import typeExtractionSem.
From D.Dot Require Import fundamental.
From D Require Import swap_later_impl.
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
  val "symb" : x1 @ "symbols" @; "Symbol"
}.

Definition fromPDotPaperTypesTBody : ty := {@
  typeEq "Type" ⊤;
  typeEq "TypeTop" ⊤;
  val "newTypeTop" : ⊤ →: x0 @; "TypeTop";
  typeEq "TypeRef" $ TAnd (x0 @; "Type") typeRefTBody;
  val "AnyType" : ▶: (x0 @; "Type");
  val "newTypeRef" : x1 @ "symbols" @; "Symbol" →: x0 @; "TypeRef"
}.

Definition fromPDotPaperAbsTypesTBody : ty := {@
  type "Type" >: ⊥ <: TTop;
  type "TypeTop" >: ⊥ <: x0 @; "Type";
  val "newTypeTop" : ⊤ →: x0 @; "TypeTop";
  type "TypeRef" >: ⊥ <: TAnd (x0 @; "Type") typeRefTBody;
  val "AnyType" : ▶: (x0 @; "Type");
  val "newTypeRef" : x1 @ "symbols" @; "Symbol" →: x0 @; "TypeRef"
}.

Definition pTop : stampTy := MkTy 40 [] ⊤ 0.

Definition optionTy pOpt pCore := TAnd (pOpt @; "Option") (typeEq "T" (pCore @ "types" @; "Type")).

Definition pSymbol : stampTy := MkTy 50 [x0; x1; x2] {@
  val "tpe" : optionTy x2 x1;
  val "id" : TNat
} 3.

Definition pTypeRef : stampTy := MkTy 60 [x0; x1] (TAnd (x0 @; "Type") typeRefTBody) 2.

(* Definition fromPDotG : stys := psAddStys primOptionG [pTop; pSymbol; pTypeRef]. *)
Definition fromPDotG : stys := psAddStys primOptionG [pTop; pSymbol].
Definition fromPDotGφ := Vs⟦ pAddStys pTypeRef fromPDotG ⟧.

Import stamp_transfer.
Lemma transfer : allGs ∅ ==∗ wellMappedφ fromPDotGφ.
Proof. apply transfer_empty. Qed.
Opaque fromPDotG.

Lemma pTopStamp : TyMemStamp fromPDotG pTop. Proof. split; stcrush. Qed.
Lemma pTypeRefStamp : TyMemStamp fromPDotG pTypeRef. Proof. split; stcrush. Qed.
Lemma pSymbolStamp : TyMemStamp fromPDotG pSymbol. Proof. split; stcrush. Qed.
Lemma Htop : styConforms fromPDotG pTop. Proof. done. Qed.
Lemma Hsymbol : styConforms fromPDotG pSymbol. Proof. done. Qed.
(* Lemma HtypeRef : styConforms fromPDotG pTypeRef. Proof. done. Qed. *)

(* Import AssertPlain.
From D.Dot Require Import hoas. *)
Definition fromPDotPaperTypesV : vl := ν {@
  type "Type" =[ pTop ];
  type "TypeTop" =[ pTop ];
  val "newTypeTop" = vabs (ν {@ });
  type "TypeRef" =[ pTypeRef ];
  val "AnyType" = ν {@ };
  val "newTypeRef" = vabs (
    ν {@
      val "symb" = x1
    })
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

Ltac hideCtx := idtac.
Definition optionModT := hclose hoptionModT.

Ltac semTMember i := iApply D_Typ; iApply (extraction_to_leadsto_envD_equiv (n := i) with "Hs"); by_extcrush.
Import prelude.

Example semFromPDotPaperTypesTyp Γ :
  TLater (fromPDotPaperAbsTBody x1) :: optionModT :: Γ ⊨[ fromPDotGφ ]
    fromPDotPaperTypesV : μ fromPDotPaperTypesTBody.
Proof.
  iIntros "#Hs".
  iApply T_Obj_I.
  iApply D_Cons; [done | semTMember 0 | ].
  iApply D_Cons; [done | semTMember 0 | ].
  iApply D_Cons; [done | iApply (fundamental_dm_typed with "Hs") | ]. {
    tcrush.
    eapply Subs_typed_nocoerce.
    + apply (TMuE_typed (T := TTop)); tcrush.
    + apply (LSel_stp' _ TTop); last (tcrush; varsub); stcrush. ltcrush.
  }
  iApply D_Cons; [done | semTMember 2 | ].
  iApply (fundamental_dms_typed with "Hs").
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
  }
  apply dnil_typed.
Qed.

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
  eapply LSel_stp'; tcrush.
  varsub. tcrush.
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

Transparent wellMappedφ.
  iIntros "/= !>" (s φ Hl).
  iApply ("Hs" with "[%]").
Opaque wellMappedφ.
  rewrite /fromPDotGφ /pAddStys/=.
  move: Hl; destruct (fromPDotG !! s) eqn:Heqs;
    rewrite !lookup_fmap Heqs => Hl; simplify_eq/=.
  have Heq: ({[60%positive := TAnd (x0 @; "Type") typeRefTBody]} ∪ fromPDotG) !! s = Some t.
  eapply lookup_union_Some_r, Heqs. by apply map_disjoint_singleton_l.
  by simpl_map by exact Heq.
Qed.
  (* done.
  rewrite lookup_merge Heqs.
first last.
  case E: (fromPDotG !! s). => [T|]. first last.
  Import fin_maps gmap.
  About lookup_weaken.
  move: Hl.
  apply (lookup_weaken _ _ _ _ Hl) => {Hl}.
  set_solver-.

  Search _ (_ <$> (merge _ _)).
  cbn.
  tcrush. *)


(* Example fromPDotPaperTyp Γ : optionModT :: Γ v⊢ₜ[fromPDotG] fromPDotPaper : μ (fromPDotPaperAbsTBody x1).
Proof.
  pose proof fromPDotPaperTypesAbsTyp Γ.

  typconstructor.
  tcrush.
Qed. *)

Definition getAnyTypeT pOpt : ty :=
  TAll (μ fromPDotPaperAbsTBody (shift pOpt)) (x0 @ "types" @; "Type").
Definition getAnyType : vl := vabs (tskip (tproj (tproj x0 "types") "AnyType")).

Ltac simplSubst := rewrite /= /up/= /ids/ids_vl/=.

Definition fromPDotPaperAbsTypesTBodySubst : ty := {@
  type "Type" >: ⊥ <: ⊤;
  type "TypeTop" >: ⊥ <: x0 @ "types" @; "Type";
  val "newTypeTop" : ⊤ →: x0 @ "types" @; "TypeTop";
  type "TypeRef" >: ⊥ <: TAnd (x0 @ "types" @; "Type") {@
    val "symb" : x0 @ "symbols" @; "Symbol"
  };
  val "AnyType" : ▶: (x0 @ "types" @; "Type");
  val "newTypeRef" : x0 @ "symbols" @; "Symbol" →: x0 @ "types" @; "TypeRef"
}.

Lemma fromPDotPSubst: fromPDotPaperAbsTypesTBody .Tp[ (p0 @ "types") /]~ fromPDotPaperAbsTypesTBodySubst.
Proof. exact: psubst_ty_rtc_sufficient. Qed.

Example getAnyTypeFunTyp Γ : μ (fromPDotPaperAbsTBody x2) :: optionModT :: Γ v⊢ₜ[fromPDotG] getAnyType : getAnyTypeT x1.
Proof.
  rewrite /getAnyType -(iterate_S tskip 0); tcrush.
  eapply (Subs_typed (T1 := TLater (x0 @ "types" @; "Type"))); tcrush.
  set Γ' := shift (μ (fromPDotPaperAbsTBody (shiftV x1))) ::
    μ (fromPDotPaperAbsTBody x2) :: optionModT :: Γ.
  have Hpx: Γ' v⊢ₚ[fromPDotG] p0 @ "types" : μ fromPDotPaperAbsTypesTBody, 0
    by tcrush; eapply Subs_typed_nocoerce;
      [ by eapply TMuE_typed; first var; stcrush | tcrush].
  have HpxSubst: Γ' v⊢ₚ[fromPDotG] p0 @ "types" : fromPDotPaperAbsTypesTBodySubst, 0.
  by eapply (p_mu_e_typed (T := fromPDotPaperAbsTypesTBody)
    (p := p0 @ "types")), Hpx; tcrush; exact: fromPDotPSubst.
  eapply (Path_typed (p := p0)), pself_inv_typed, (p_subs_typed (i := 0)), HpxSubst.
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
