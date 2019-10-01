(**
WIP examples constructing syntactic typing derivations.
I am also experimenting with notations, but beware the current definitions are pretty bad.
 *)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn typingExInfra.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section examples.
(* From D Require Import typeExtraction *)
Context `{hasStampTable: stampTable}.

(********************)
(** MICRO-EXAMPLES **)
(********************)

Example ex0 e Γ T:
  Γ ⊢ₜ e : T →
  is_stamped_ty (length Γ) getStampTable T →
  Γ ⊢ₜ e : ⊤.
Proof. intros. apply (Subs_typed_nocoerce T TTop); tcrush. Qed.

Example ex1 Γ n T:
  Γ ⊢ₜ tv (ν {@ val "a" = vnat n}) : μ {@ val "a" : TNat }.
Proof.
  (* Help proof search: Avoid trying TMuI_typed, that's slow. *)
  apply VObj_typed; tcrush.
Qed.

Example ex2 Γ T
  (Hg: getStampTable !! s1 = Some (p0 @; "B")):
  Γ ⊢ₜ tv (ν {@ type "A" = (idsσ 1 ; s1) } ) :
    TMu (TAnd (TTMem "A" TBot TTop) TTop).
Proof.
  have Hs: (p0 @; "B") ~[ 1 ] (getStampTable, (s1, idsσ 1)).
  by_extcrush.
  have Hst: is_stamped_ty (1 + length Γ) getStampTable (p0 @; "B").
  by tcrush.
  apply VObj_typed; last tcrush. (* Avoid trying TMuI_typed, that's slow. *)
  eapply dcons_typed; trivial.
  eapply (dty_typed (p0 @; "B")); tcrush.
Qed.

(* Try out fixpoints. *)
Definition F3 T :=
  TMu (TAnd (TTMem "A" T T) TTop).

Example ex3 Γ T
  (Hg: getStampTable !! s1 = Some (F3 (p0 @; "A"))):
  Γ ⊢ₜ tv (ν {@ type "A" = (σ1 ; s1) } ) :
    F3 (F3 (TSel p0 "A")).
Proof.
  have Hs: F3 (p0 @; "A") ~[ 0 ] (getStampTable, (s1, σ1)).
  by_extcrush.
  have Hst: is_stamped_ty (1 + length Γ) getStampTable (F3 (p0 @; "A")).
  by stcrush.
  apply VObj_typed; last tcrush. (* Avoid trying TMuI_typed, that's slow. *)
  eapply dcons_typed; trivial.
  eapply (dty_typed (F3 (p0 @; "A"))); by tcrush.
Qed.

(********************)
(** SMALL EXAMPLES **)
(* (Ones we could start describing in text). *)
(********************)

(**
  First example from "The Essence of Dependent Object Types". Original code:

  trait Keys {
    type Key
    def key(data: String): Key
  }

  object HashKeys extends Keys {
    type Key = Int
    def key(s: String) = s.hashCode
  }

  Note we upcast Int to this.Key; as expected, no later is needed.
*)

(* This stands for type [String] in that example. *)
Notation HashableString := (μ {@ val "hashCode" : TAll TUnit TNat }).
Definition KeysT : ty := μ {@
  type "Key" >: ⊥ <: ⊤;
  val "key": TAll HashableString (p1 @; "Key")
}.
Definition hashKeys : vl := ν {@
  type "Key" = (σ1; s1);
  val "key" = vabs (tapp (tproj (tv x0) "hashCode") tUnit)
}.
Definition s1_is_tnat :=
  TNat ~[ 0 ] (getStampTable, (s1, σ1)).
Lemma get_s1_is_tnat : getStampTable !! s1 = Some TNat → s1_is_tnat.
Proof. intros; red. by_extcrush. Qed.

(* To typecheck the object body, we first typecheck it with a tighter type,
    and then widen it. *)
Definition KeysT' := μ {@
  type "Key" >: TNat <: ⊤;
  val "key": TAll HashableString (p1 @; "Key")
}.
(* IDEA for our work: use [(type "Key" >: TNat <: ⊤) ⩓ (type "Key" >: ⊥ <: ⊤)]. *)

Example hashKeys_typed Γ (Hs1 : s1_is_tnat):
  Γ ⊢ₜ tv hashKeys : KeysT.
Proof.
  cut (Γ ⊢ₜ tv hashKeys : KeysT').
  { intros H.
    apply (Subs_typed_nocoerce KeysT'); first done.
    apply Mu_stp_mu; last stcrush.
    tcrush.
    eapply Trans_stp; first apply TAnd1_stp; tcrush.
  }
  apply VObj_typed; cbn; last by tcrush.
  eapply dcons_typed; tcrush.
  by apply (dty_typed TNat); tcrush.
  cbn; apply (App_typed _ _ _ TUnit);
    last eapply (Subs_typed_nocoerce TNat); tcrush.
  tcrush; cbn.

  pose (T0 := μ {@ val "hashCode" : TAll ⊤ 𝐍 }).

  have Htp: ∀ Γ', T0 :: Γ' ⊢ₜ tv x0 : val "hashCode" : TAll ⊤ TNat. {
    intros. eapply Subs_typed_nocoerce.
    eapply TMuE_typed'; by [exact: Var_typed'|].
    by apply TAnd1_stp; tcrush.
  }
  apply (Subs_typed_nocoerce (val "hashCode" : TAll ⊤ 𝐍)). exact: Htp.
  tcrush.
  eapply LSel_stp'; tcrush.
  eapply Var_typed_sub; by [|tcrush].
Qed.

Section StringExamples.
(* new {
  val subSys1 : { z => type A <: Int } = new { type A = Int }
  val subSys2 : { z => type B } = new { type B = String }
} *)
Context (String : ty) (HclString : nclosed String 0).

(* Term *)
Definition systemVal := tv (ν {@
  val "subSys1" = ν {@ type "A" = (σ1; s1) } ;
  val "subSys2" = ν {@ type "B" = (σ2; s2) } }).
Definition s2_is_String :=
  String ~[ 0 ] (getStampTable, (s2, σ2)).
Lemma get_s2_is_String : getStampTable !! s2 = Some String → s2_is_String.
Proof. intros; red. by_extcrush. Qed.

(* Type *)
Definition systemValT := μ {@
  val "subSys1" : μ {@ type "A" >: ⊥ <: TNat};
  val "subSys2" : μ {@ type "B" >: ⊥ <: ⊤}}.

Example motivEx Γ (Hs1: s1_is_tnat) (Hs2: s2_is_String)
  (HsString: is_stamped_ty 0 getStampTable String):
  Γ ⊢ₜ systemVal : systemValT.
Proof.
  apply VObj_typed; last by tcrush.
  eapply dcons_typed; tcrush.
  all: [> apply (dty_typed TNat) | apply (dty_typed String) ]; tcrush.
Qed.

(* Uh, we can unfold recursive types during construction! Does that allow
us to encode mutual recursion? Write this up. *)
Definition systemValT' := μ {@
  val "subSys1" : type "A" >: ⊥ <: TNat;
  val "subSys2" : type "B" >: ⊥ <: ⊤}.
Example motivEx1 Γ (Hs1: s1_is_tnat) (Hs2: s2_is_String)
  (HsString: is_stamped_ty 0 getStampTable String):
  Γ ⊢ₜ systemVal : systemValT'.
Proof.
  apply VObj_typed; last tcrush.
  eapply dcons_typed; tcrush.
  - apply (Subs_typed_nocoerce (μ {@ type "A" >: ⊥ <: TNat})); tcrush.
    + apply (dty_typed TNat); tcrush.
    + eapply Trans_stp;
      [eapply (Mu_stp _ ({@ type "A" >: ⊥ <: TNat })%ty 0)|]; tcrush.
  - apply (Subs_typed_nocoerce (μ {@ type "B" >: ⊥ <: ⊤})); tcrush.
    + apply (dty_typed String); tcrush.
    + eapply Trans_stp;
      [eapply (Mu_stp _ ({@ type "B" >: ⊥ <: ⊤ })%ty 0)|]; tcrush.
Qed.
End StringExamples.

(* Sec. 5 of WadlerFest DOT.
IFTFun ≡ { if: ∀(x: {A: ⊥..⊤})∀(t: x.A)∀(f: x.A): x.A }
IFT ≡ { if: IFTFun }

let boolImpl =
ν (b: { Boolean: IFT..IFT } ∧ { true: IFT } ∧ { false: IFT })
{ Boolean = IFT } ∧
{ true = λ(x: {A: ⊥..⊤})λ(t: x.A)λ(f: x.A)t } ∧ { false = λ(x: {A: ⊥..⊤})λ(t: x.A)λ(f: x.A)f }

In fact, that code doesn't typecheck as given, and we fix it by setting.

IFT ≡ IFTFun
 *)
Definition IFT : ty :=
  TAll (type "A" >: ⊥ <: ⊤)
    (TAll (p0 @; "A") (TAll (p1 @; "A") (p2 @; "A"))).
(* Definition IFT : ty := {@ val "if" : IFTFun }. *)
Definition vabs' x := tv (vabs x).

Definition iftTrue := vabs (vabs' (vabs' (tv x1))).
Definition iftFalse := vabs (vabs' (vabs' (tv x0))).

Example iftTrueTyp Γ : Γ ⊢ₜ tv iftTrue : IFT.
Proof. tcrush. exact: Var_typed'. Qed.
Example iftFalseTyp Γ : Γ ⊢ₜ tv iftFalse : IFT.
Proof. tcrush. exact: Var_typed'. Qed.

Definition boolImplTDef1 :=
  IFT ~[ 0 ] (getStampTable, (s1, σ1)).
Arguments boolImplTDef1 /.

Definition boolImpl :=
  ν {@
    type "Boolean" = ( σ1; s1 );
    val "true" = iftTrue;
    val "false" = iftFalse
  }.
(* This type makes "Boolean" nominal by abstracting it. *)
Definition boolImplT : ty :=
  μ {@
    type "Boolean" >: ⊥ <: IFT;
    val "true" : (p0 @; "Boolean");
    val "false" : (p0 @; "Boolean")
  }.

Definition boolImplTConcr : ty :=
  μ {@
    type "Boolean" >: IFT <: IFT;
    val "true" : IFT;
    val "false" : IFT
  }.
Example boolImplTyp Γ (Hst : boolImplTDef1):
  Γ ⊢ₜ tv boolImpl : boolImplT.
Proof.
  apply (Subs_typed_nocoerce boolImplTConcr).
  tcrush; by [apply (dty_typed IFT); tcrush| exact: Var_typed'].
  tcrush.
  - eapply Trans_stp; first apply TAnd1_stp; tcrush.
  - eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd1_stp; tcrush.
    eapply LSel_stp'; tcrush.
    eapply Var_typed_sub; by [|tcrush].
  - eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd1_stp; tcrush.
    eapply LSel_stp'; tcrush.
    eapply Var_typed_sub; by [|tcrush].
Qed.

(* We can also use subtyping on the individual members to type this example. *)
Definition boolImplT0 : ty :=
  μ {@
    type "Boolean" >: IFT <: IFT;
    val "true" : (p0 @; "Boolean");
    val "false" : (p0 @; "Boolean")
  }.

Example boolImplTypAlt Γ (Hst : boolImplTDef1):
  Γ ⊢ₜ tv boolImpl : boolImplT.
Proof.
  apply (Subs_typed_nocoerce boolImplT0);
    last (tcrush; eapply Trans_stp; first apply TAnd1_stp; tcrush).
  tcrush; first (by (apply (dty_typed IFT); tcrush)).
  - eapply (Subs_typed_nocoerce); first apply iftTrueTyp.
    eapply LSel_stp'; tcrush.
    eapply Var_typed_sub; by [|tcrush].
  - eapply (Subs_typed_nocoerce); first apply iftFalseTyp.
    eapply LSel_stp'; tcrush.
    eapply Var_typed_sub; by [|tcrush].
Qed.

(* AND = λ a b. a b False. *)
Definition packBoolean := ν {@ type "A" = ( σ1; s1 ) }.

Definition boolImplTDef2 :=
  IFT ~[ 0 ] (getStampTable, (s1, σ1)).
Lemma packBooleanTyp0 Γ (Hst : boolImplTDef2) :
  Γ ⊢ₜ tv packBoolean : type "A" >: IFT <: IFT.
Proof.
  apply (Subs_typed_nocoerce (μ {@ type "A" >: IFT <: IFT })).
  apply VObj_typed; tcrush.
  eapply (dty_typed IFT); tcrush.
  eapply Trans_stp; first apply (Mu_stp _ ({@ type "A" >: IFT <: IFT }));
   tcrush.
Qed.

Lemma packBooleanTyp Γ (Hst : boolImplTDef2) :
  Γ ⊢ₜ tv packBoolean : type "A" >: ⊥ <: ⊤.
Proof.
  apply (Subs_typed_nocoerce (type "A" >: IFT <: IFT)).
  exact: packBooleanTyp0. tcrush.
Qed.

Definition iftAnd false : vl := vabs (vabs'
  (tapp (tapp (tapp (tv x1) (tv packBoolean)) (tv x0)) false)).

Lemma packBooleanLB Γ (Hst : boolImplTDef2) i :
  Γ ⊢ₜ ▶ IFT, i <: (pv packBoolean @; "A"), i.
Proof.
  apply AddIB_stp, (LSel_stp _ (pv _) IFT).
  tcrush. exact: packBooleanTyp0.
Qed.

Lemma packBooleanUB Γ (Hst : boolImplTDef2) i :
  Γ ⊢ₜ (pv packBoolean @; "A"), i <: ▶ IFT, i.
Proof. eapply AddIB_stp, SelU_stp; tcrush. exact: packBooleanTyp0. Qed.

(* XXX better statement *)
Lemma extr_dtysem_stamped {g s m} σ T n :
  T ~[ n ] (g, (s, σ)) →
  m = length σ →
  ∃ T' : ty, g !! s = Some T' ∧ nclosed T' m.
Proof.
  intros Hst ->. by rewrite /= /extraction in Hst |- *; ev; eauto 3.
Qed.

Example iftAndTyp Γ (Hst : boolImplTDef2) falseTm
  (HfalseTm : ∀ T1 T2, T1 :: T2 :: Γ ⊢ₜ falseTm : IFT):
  Γ ⊢ₜ tv (iftAnd falseTm) : TAll IFT (TAll IFT (▶IFT)).
Proof.
  unfold boolImplTDef1 in *; rewrite /iftAnd /vabs'.
  tcrush.
  econstructor. 2: exact: HfalseTm.
  econstructor. 2: exact: Var_typed'.
  rewrite lift0 hsubst_id /= -/IFT.
  eapply Subs_typed_nocoerce. {
    eapply Appv_typed'. 2: by apply: packBooleanTyp; eauto.
    exact: Var_typed'.
    by cbv; rewrite -/IFT.
  }
  rewrite -/packBoolean.
  (* XXX better statement *)
  have ?: ∃ T' : ty, getStampTable !! 1%positive = Some T' ∧ nclosed T' 0.
  exact: extr_dtysem_stamped.

  apply TAllConCov_stp; stcrush.
  { eapply Trans_stp. apply: packBooleanLB. by eauto 4. tcrush. }
  apply TLaterCov_stp, TAllConCov_stp; stcrush.
  - eapply Trans_stp.
    apply: packBooleanLB. by cbn; eauto 3.
    tcrush.
  - eapply TLaterCov_stp, Trans_stp.
    apply: packBooleanUB. by cbn; eauto 3.
    tcrush.
Qed.

(* Eta-expand to drop the later. *)
Definition etaExpAnd false := vabs (vabs'
    (tskip
      (tapp (tapp (tv (iftAnd false)) (tv x1)) (tv x0)))).
Example iftAndTyp' Γ (Hst : boolImplTDef2):
  Γ ⊢ₜ tv (etaExpAnd (tv iftFalse)) :
    TAll IFT (TAll IFT IFT).
Proof.
  tcrush; rewrite -(iterate_S tskip 0).
  eapply (Subs_typed _ _ (▶IFT)); first tcrush.
  eapply App_typed; last exact: Var_typed';
    eapply App_typed; last exact: Var_typed'; rewrite /= -/IFT.
  apply iftAndTyp; eauto. intros; exact: iftFalseTyp.
Qed.

Definition boolImplV2 :=
  ν {@
    type "Boolean" = ( σ1; s1 );
    val "true" = iftTrue;
    val "false" = iftFalse;
    (* One eta-expansion isn't enough? *)
    val "and" = etaExpAnd (tproj (tv x4) "false")
  }.

Definition boolImplV2T : ty :=
  μ {@
    type "Boolean" >: ⊥ <: IFT;
    val "true" : (p0 @; "Boolean");
    val "false" : (p0 @; "Boolean");
    val "and" : TAll (p0 @; "Boolean") (TAll (p1 @; "Boolean") (p2 @; "Boolean"))
  }.

Definition boolImplV2TMoreConcrBody : ty :=
  {@
    type "Boolean" >: IFT <: IFT;
    val "true" : IFT;
    val "false" : IFT;
    val "and" : TAll IFT (TAll IFT IFT)
  }.

Definition boolImplV2TConcrBody : ty :=
  {@
    type "Boolean" >: IFT <: IFT;
    val "true" : IFT;
    val "false" : IFT;
    val "and" : TAll (p0 @; "Boolean") (TAll (p1 @; "Boolean") (p2 @; "Boolean"))
    (* val "and" : TAll IFT (TAll IFT IFT) *)
  }.
Definition boolImplTDef2' :=
  (p0 @; "Boolean") ~[ 0 ] (getStampTable, (s2, σ2)).
Example boolImplV2Typ Γ
  (Hst1 : boolImplTDef1) (Hst2 : boolImplTDef2):
  Γ ⊢ₜ tv boolImplV2 : boolImplV2T.
Proof.
  apply (Subs_typed_nocoerce (μ boolImplV2TMoreConcrBody)).
  - tcrush; try by [apply (dty_typed IFT); tcrush| exact: Var_typed'].
    rewrite /= -/IFT.
    Abort.


Example boolImplV2Typ2 Γ
  (Hst1 : boolImplTDef1) (Hst2 : boolImplTDef2):
  Γ ⊢ₜ tv boolImplV2 : boolImplV2T.
Proof.
  apply (Subs_typed_nocoerce (μ boolImplV2TConcrBody)).
  - tcrush; try by [apply (dty_typed IFT); tcrush| exact: Var_typed'].
    rewrite /= -/IFT.
    tcrush; rewrite -(iterate_S tskip 0).
    eapply (Subs_typed _ _ (▶▶IFT)); first tcrush.
    eapply Trans_stp; first apply TLaterL_stp; tcrush.
    eapply (LSel_stp _ p2); tcrush.
    eapply Var_typed_sub; by [|tcrush].
    eapply App_typed; last exact: Var_typed';
      eapply App_typed; last exact: Var_typed'; rewrite /= -/IFT.
    tcrush.
    econstructor. 2: {
      tcrush; apply: Var_typed_sub => //.
      rewrite /= /up /= -/boolImplV2TConcrBody -/IFT
        -/p0 -/p1 -/p2 -/p3 -/p4 -/p5.
      eapply Trans_stp; first apply TAnd2_stp; tcrush.
      eapply Trans_stp; first apply TAnd2_stp; tcrush.
    }
    econstructor; last exact: Var_typed'.
    rewrite /= /up/= -/p0 -/IFT.
    Abort.
(*
  { eapply Trans_stp. apply: packBooleanLB. by eauto 4. tcrush. }
    (* Maybe we should pass p0.Boolean, not IFT, as type argument in iftAnd, but then we must patch iftAndTyp! *)
    econstructor. apply: Var_typed_sub => //=.
    rewrite /= -/IFT.
    eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd2_stp; tcrush.

  - have ?: boolImplV2TConcrBody :: Γ ⊢ₜ IFT, 0 <: p0 @; "Boolean", 0.
    eapply LSel_stp'; tcrush.
    eapply Var_typed_sub; by [|tcrush].

    tcrush; rewrite iterate_0.
  + eapply Trans_stp; first apply TAnd1_stp; tcrush.
  + eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd1_stp; tcrush.
  + eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd1_stp; tcrush.
  + eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd2_stp; tcrush.
    eapply Trans_stp; first apply TAnd1_stp; stcrush.
    tcrush; rewrite ?iterate_S ?iterate_0 /= -/IFT.
Abort. *)
    (*
    eapply Trans_stp.
    * eapply SelU_stp; tcrush; apply: Var_typed_sub => //.
      rewrite /= -/IFT.
      eapply Trans_stp; first apply TAnd1_stp; tcrush.
    * rewrite /iterate /=.

    cbn.
    apply SelU_stp.
    *)

End examples.
