(**
WIP examples constructing syntactic typing derivations.
I am also experimenting with notations, but beware the current definitions are pretty bad.
 *)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn typingExInfra stampedness_binding.

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
  apply dcons_typed; first tcrush; last done.
  by apply (dty_typed TNat); tcrush.
  apply dcons_typed; first apply dvabs_typed; tcrush.
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
Context (String : ty) (HclString : is_stamped_ty 0 getStampTable String).

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
Definition IFTBody := (TAll (p0 @; "A") (TAll (p1 @; "A") (p2 @; "A"))).
Definition IFT : ty :=
  TAll (type "A" >: ⊥ <: ⊤) IFTBody.
Lemma IFTStamped: is_stamped_ty 0 getStampTable IFT.
Proof. tcrush. Qed.
Hint Resolve IFTStamped : core.

(* Definition IFT : ty := {@ val "if" : IFTFun }. *)

Definition iftTrue := vabs (vabs' (vabs' (tv x1))).
Definition iftFalse := vabs (vabs' (vabs' (tv x0))).

Example iftTrueTyp Γ : Γ ⊢ₜ tv iftTrue : IFT.
Proof. tcrush. exact: Var_typed'. Qed.
Example iftFalseTyp Γ : Γ ⊢ₜ tv iftFalse : IFT.
Proof. tcrush. exact: Var_typed'. Qed.

Definition s1_is_ift := getStampTable !! s1 = Some IFT.

Definition s1_is_ift_ext := IFT ~[ 0 ] (getStampTable, (s1, σ1)).

Lemma get_s1_is_ift : s1_is_ift → s1_is_ift_ext.
Proof. intros; red. by_extcrush. Qed.
Hint Resolve get_s1_is_ift : core.

Definition p0Bool := (p0 @; "Boolean").
Lemma p0BoolStamped: is_stamped_ty 1 getStampTable p0Bool.
Proof. tcrush. Qed.
Hint Resolve p0BoolStamped : core.

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
    val "true" : p0Bool;
    val "false" : p0Bool
  }.

Definition boolImplTConcr : ty :=
  μ {@
    typeEq "Boolean" IFT;
    val "true" : IFT;
    val "false" : IFT
  }.
Example boolImplTyp Γ (Hst : s1_is_ift_ext):
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
    typeEq "Boolean" IFT;
    val "true" : p0Bool;
    val "false" : p0Bool
  }.

Lemma dvabs_sub_typed V T1 T2 e l:
    is_stamped_ty (S (length Γ)) getStampTable T1 →
    T1.|[ren (+1)] :: V :: Γ ⊢ₜ e : T2 →
    Γ |d V ⊢{ l := dvl (vabs e) } : TVMem l (TAll T1 T2)

Example boolImplTypAlt Γ (Hst : s1_is_ift_ext):
  Γ ⊢ₜ tv boolImpl : boolImplT.
Proof.
  apply (Subs_typed_nocoerce boolImplT0);
    last (tcrush; eapply Trans_stp; first apply TAnd1_stp; tcrush).
  tcrush; first (by (apply (dty_typed IFT); tcrush)).
  typconstructor; last tcrush.

  apply dcons_typed; first apply dvabs_typed; tcrush.
  apply dcons_typed; [apply (dty_typed IFT); tcrush | | done].
  apply dcons_typed; first apply dvabs_typed. tcrush.
  apply dcons_typed;
  tcrush
  - eapply (Subs_typed_nocoerce); first apply iftTrueTyp.
    eapply LSel_stp'; tcrush.
    eapply Var_typed_sub; by [|tcrush].
  - eapply (Subs_typed_nocoerce); first apply iftFalseTyp.
    eapply LSel_stp'; tcrush.
    eapply Var_typed_sub; by [|tcrush].
Qed.

(* AND = λ a b. a b False. *)
Definition packBoolean := packTV 0 s1.
Lemma packBooleanTyp0 Γ (Hst : s1_is_ift) :
  Γ ⊢ₜ tv packBoolean : typeEq "A" IFT.
Proof. apply (packTV_typed' s1 IFT); eauto 1. Qed.

Lemma packBooleanTyp Γ (Hst : s1_is_ift) :
  Γ ⊢ₜ tv packBoolean : type "A" >: ⊥ <: ⊤.
Proof.
  apply (Subs_typed_nocoerce (typeEq "A" IFT)); last tcrush.
  exact: packBooleanTyp0.
Qed.

Lemma packBooleanLB Γ (Hst : s1_is_ift) i :
  Γ ⊢ₜ ▶ IFT, i <: (pv packBoolean @; "A"), i.
Proof. by apply /val_LB /packBooleanTyp0. Qed.

Lemma packBooleanUB Γ (Hst : s1_is_ift) i :
  Γ ⊢ₜ (pv packBoolean @; "A"), i <: ▶ IFT, i.
Proof. by apply /val_UB /packBooleanTyp0. Qed.

Definition iftAnd false : vl := vabs (vabs'
  (tapp (tapp (tapp (tv x1) (tv packBoolean)) (tv x0)) false)).

Example iftAndTyp Γ (Hst : s1_is_ift):
  Γ ⊢ₜ tv (iftAnd (tv iftFalse)) : TAll IFT (TAll IFT (▶IFT)).
Proof.
  unfold s1_is_ift in *; rewrite /iftAnd /vabs'.
  tcrush.
  eapply App_typed; last exact: iftFalseTyp.
  eapply App_typed; last exact: Var_typed'.
  rewrite lift0 hsubst_id /= -/IFT.
  eapply Subs_typed_nocoerce. {
    eapply Appv_typed'. 2: by apply: packBooleanTyp; eauto.
    exact: Var_typed'.
    by change IFTBody.|[_] with IFTBody.
  }
  have Hs: is_stamped_dm 0 getStampTable (dtysem σ1 s1).
  apply /extr_dtysem_stamped; by [apply: get_s1_is_ift|].

  apply TAllConCov_stp; stcrush.
  { eapply Trans_stp. exact: packBooleanLB. tcrush. }
  apply TLaterCov_stp, TAllConCov_stp; stcrush.
  - eapply Trans_stp. exact: packBooleanLB. tcrush.
  - eapply TLaterCov_stp, Trans_stp.
    exact: packBooleanUB. tcrush.
Qed.

(* Eta-expand to drop the later. *)

Example iftAndTyp'1 Γ (Hst : s1_is_ift):
  Γ ⊢ₜ vabs' (vabs'
    (tskip
      (tapp (tapp (tv (iftAnd (tv iftFalse))) (tv x1)) (tv x0)))) :
    TAll IFT (TAll IFT IFT).
Proof.
  tcrush; rewrite -(iterate_S tskip 0).
  eapply (Subs_typed _ _ (▶IFT)); first tcrush.
  eapply App_typed; last exact: Var_typed';
    eapply App_typed; last exact: Var_typed'; rewrite /= -/IFT.
  apply iftAndTyp; eauto.
Qed.

Definition iftCoerce t :=
  lett t (vabs' (vabs' (tskip (tapp (tapp (tv x2) (tv x1)) (tv x0))))).

Lemma coerce_tAppIFT Γ t T :
  is_stamped_ty (length Γ) getStampTable T →
  Γ ⊢ₜ t : TAll T (TAll T.|[ren (+1)] (▶ T.|[ren (+2)])) →
  Γ ⊢ₜ iftCoerce t : TAll T (TAll T.|[ren (+1)] T.|[ren (+2)]).
Proof.
  move => HsT1 Ht.
  move: (HsT1) => /is_stamped_ren1_ty HsT2.
  move: (HsT2) => /is_stamped_ren1_ty; rewrite -hrenS => HsT3.
  move: (HsT3) => /is_stamped_ren1_ty; rewrite -hrenS => HsT4.
  eapply Let_typed; [exact: Ht| |tcrush].
  rewrite /= !(hren_upn_gen 1) (hren_upn_gen 2) /=.
  tcrush; rewrite -!hrenS -(iterate_S tskip 0).
  eapply (Subs_typed _ _ (▶T.|[_])); first tcrush.
  eapply App_typed; last exact: Var_typed';
    eapply App_typed; last exact: Var_typed'.
  apply: Var_typed' => //.
  rewrite /= !(hren_upn 1) (hren_upn_gen 1) (hren_upn_gen 2)
    !hsubst_comp !ren_ren_comp /=. done.
Qed.

Example iftAndTyp'2 Γ (Hst : s1_is_ift):
  Γ ⊢ₜ iftCoerce (tv (iftAnd (tv iftFalse))) : TAll IFT (TAll IFT IFT).
Proof. intros. apply /coerce_tAppIFT /iftAndTyp; tcrush. Qed.

Lemma subIFT i Γ T:
  is_stamped_ty (length Γ) getStampTable T.|[ren (+i)] →
  (typeEq "A" T.|[ren (+1+i)]) :: Γ ⊢ₜ IFTBody, 0 <:
    TAll T.|[ren (+1+i)] (TAll T.|[ren (+2+i)] (▶ T.|[ren (+3+i)])), 0.
Proof.
  rewrite /= -/IFTBody => HsT1.
  move: (HsT1) => /is_stamped_ren1_ty HsT2; rewrite -hrenS in HsT2.
  move: (HsT2) => /is_stamped_ren1_ty HsT3; rewrite -hrenS in HsT3.
  tcrush; rewrite ?iterate_S ?iterate_0 /=;
    first [apply: LSel_stp' | apply: SelU_stp]; tcrush; apply: Var_typed';
    rewrite ?hsubst_id //; by [| autosubst].
Qed.

Lemma tAppIFT_typed Γ T t s :
  is_stamped_ty (length Γ) getStampTable T →
  getStampTable !! s = Some T.|[ren (+1)] →
  Γ ⊢ₜ t : IFT →
  Γ ⊢ₜ tApp Γ t s :
    TAll T (TAll T.|[ren (+1)] (▶ T.|[ren (+2)])).
Proof.
  move => HsT1 Hl Ht; move: (HsT1) => /is_stamped_ren1_ty HsT2.
  intros; eapply typeApp_typed => //; tcrush.
  intros; asimpl. exact: (subIFT 1).
Qed.

Lemma tAppIFT_coerced_typed Γ T t s :
  is_stamped_ty (length Γ) getStampTable T →
  getStampTable !! s = Some T.|[ren (+1)] →
  Γ ⊢ₜ t : IFT →
  Γ ⊢ₜ iftCoerce (tApp Γ t s) :
    TAll T (TAll T.|[ren (+1)] T.|[ren (+2)]).
Proof. intros. by apply /coerce_tAppIFT /tAppIFT_typed. Qed.

Lemma tAppIFT_coerced_typed_IFT Γ t s :
  getStampTable !! s = Some IFT →
  Γ ⊢ₜ t : IFT →
  Γ ⊢ₜ iftCoerce (tApp Γ t s) :
    TAll IFT (TAll IFT IFT).
Proof. intros. apply tAppIFT_coerced_typed; eauto 2. Qed.

Definition IFTp0 := TAll p0Bool (TAll p0Bool.|[ren (+1)] (p0Bool.|[ren (+2)])).

Lemma tAppIFT_coerced_typed_p0Boolean Γ T t s :
  getStampTable !! s = Some p0Bool.|[ren (+1)] →
  T :: Γ ⊢ₜ t : IFT →
  T :: Γ ⊢ₜ iftCoerce (tApp (T :: Γ) t s) :
    TAll p0Bool (TAll p0Bool.|[ren (+1)] p0Bool.|[ren (+2)]).
Proof. intros. apply tAppIFT_coerced_typed; eauto 3. Qed.

Definition iftNot Γ t s :=
  tapp (tapp
      (iftCoerce (tApp Γ t s))
    (tv iftFalse))
  (tv iftTrue).

Lemma iftNotTyp Γ T t s :
  getStampTable !! s = Some IFT →
  Γ ⊢ₜ t : IFT →
  Γ ⊢ₜ iftNot Γ t s : IFT.
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

Lemma iftAndTyp2 Γ T t1 t2 s :
  getStampTable !! s = Some IFT →
  Γ ⊢ₜ t1 : IFT →
  Γ ⊢ₜ t2 : IFT →
  Γ ⊢ₜ iftAnd2 Γ t1 t2 s : IFT.
Proof.
  intros Hs Ht1 Ht2.
  eapply App_typed; last exact: iftFalseTyp.
  eapply App_typed; last exact: Ht2.
  exact: tAppIFT_coerced_typed_IFT.
Qed.

End examples.
