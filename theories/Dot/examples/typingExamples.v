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
Context {g : stys}.

(********************)
(** MICRO-EXAMPLES **)
(********************)

Example ex0 e Γ T:
  Γ v⊢ₜ[ g ] e : T →
  is_stamped_ty (length Γ) g T →
  Γ v⊢ₜ[ g ] e : ⊤.
Proof. intros. apply (Subs_typed_nocoerce T TTop); tcrush. Qed.

Example ex1 Γ n T:
  Γ v⊢ₜ[ g ] tv (ν {@ val "a" = pv (vnat n)}) : μ {@ val "a" : TNat }.
Proof.
  (* Help proof search: Avoid trying TMuI_typed, that's slow. *)
  apply VObj_typed; tcrush.
Qed.

Example ex2 Γ T
  (Hg: g !! s1 = Some (p0 @; "B")):
  Γ v⊢ₜ[ g ] tv (ν {@ type "A" = (idsσ 1 ; s1) } ) :
    TMu (TAnd (TTMem "A" TBot TTop) TTop).
Proof.
  have Hs: (p0 @; "B") ~[ 1 ] (g, (s1, idsσ 1)).
  by_extcrush.
  have Hst: is_stamped_ty (1 + length Γ) g (p0 @; "B").
  by tcrush.
  apply VObj_typed; tcrush. (* Avoid trying TMuI_typed, that's slow. *)
  apply (dty_typed (p0 @; "B")); cbn; by wtcrush.
Qed.

(* Try out fixpoints. *)
Definition F3 T :=
  TMu (TAnd (TTMem "A" T T) TTop).

Example ex3 Γ T
  (Hg: g !! s1 = Some (F3 (p0 @; "A"))):
  Γ v⊢ₜ[ g ] tv (ν {@ type "A" = (σ1 ; s1) } ) :
    F3 (F3 (TSel p0 "A")).
Proof.
  have Hs: F3 (p0 @; "A") ~[ 0 ] (g, (s1, σ1)).
  by_extcrush.
  have Hst: is_stamped_ty (1 + length Γ) g (F3 (p0 @; "A")).
  by stcrush.
  apply VObj_typed; tcrush. (* Avoid trying TMuI_typed, that's slow. *)
  apply (dty_typed (F3 (p0 @; "A"))); by wtcrush.
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
  val "key" = pv (vabs (tapp (tproj (tv x0) "hashCode") tUnit))
}.
Definition s1_is_tnat :=
  TNat ~[ 0 ] (g, (s1, σ1)).
Lemma get_s1_is_tnat : g !! s1 = Some TNat → s1_is_tnat.
Proof. intros; red. by_extcrush. Qed.

(* To typecheck the object body, we first typecheck it with a tighter type,
    and then widen it. *)
Definition KeysT' := μ {@
  type "Key" >: TNat <: ⊤;
  val "key": TAll HashableString (p1 @; "Key")
}.
(* IDEA for our work: use [(type "Key" >: TNat <: ⊤) ⩓ (type "Key" >: ⊥ <: ⊤)]. *)

Example hashKeys_typed Γ (Hs1 : s1_is_tnat):
  Γ v⊢ₜ[ g ] tv hashKeys : KeysT.
Proof.
  cut (Γ v⊢ₜ[ g ] tv hashKeys : KeysT').
  { intros H.
    apply (Subs_typed_nocoerce KeysT'); first done.
    apply Mu_stp_mu; last stcrush.
    tcrush.
    ettrans; first apply TAnd1_stp; tcrush.
  }
  apply VObj_typed; tcrush.
  by apply (dty_typed TNat); wtcrush.
  cbn; apply (App_typed (T1 := TUnit));
    last eapply (Subs_typed_nocoerce TNat); tcrush.
  tcrush; cbn.

  pose (T0 := μ {@ val "hashCode" : TAll ⊤ 𝐍 }).

  have Htp: ∀ Γ', T0 :: Γ' v⊢ₜ[ g ] tv x0 : val "hashCode" : TAll ⊤ TNat. {
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
Context (String : ty) (HclString : is_stamped_ty 0 g String).

(* Term *)
Definition systemVal := tv (ν {@
  val "subSys1" = pv (ν {@ type "A" = (σ1; s1) }) ;
  val "subSys2" = pv (ν {@ type "B" = (σ2; s2) }) }).
Definition s2_is_String :=
  String ~[ 0 ] (g, (s2, σ2)).
Lemma get_s2_is_String : g !! s2 = Some String → s2_is_String.
Proof. intros; red. by_extcrush. Qed.

(* Type *)
Definition systemValT := μ {@
  val "subSys1" : μ {@ type "A" >: ⊥ <: TNat};
  val "subSys2" : μ {@ type "B" >: ⊥ <: ⊤}}.

Example motivEx Γ (Hs1: s1_is_tnat) (Hs2: s2_is_String)
  (HsString: is_stamped_ty 0 g String):
  Γ v⊢ₜ[ g ] systemVal : systemValT.
Proof.
  apply VObj_typed; tcrush.
  all: [> apply (dty_typed TNat) | apply (dty_typed String) ]; wtcrush.
Qed.

(* Uh, we can unfold recursive types during construction! Does that allow
us to encode mutual recursion? Write this up. *)
Definition systemValT' := μ {@
  val "subSys1" : type "A" >: ⊥ <: TNat;
  val "subSys2" : type "B" >: ⊥ <: ⊤}.
Example motivEx1 Γ (Hs1: s1_is_tnat) (Hs2: s2_is_String)
  (HsString: is_stamped_ty 0 g String):
  Γ v⊢ₜ[ g ] systemVal : systemValT'.
Proof.
  apply VObj_typed; tcrush.
  - apply (Subs_typed_nocoerce (μ {@ type "A" >: ⊥ <: TNat})); tcrush.
    + apply (dty_typed TNat); wtcrush.
    + ettrans;
      [eapply (Mu_stp _ (T := {@ type "A" >: ⊥ <: TNat })%ty 0)|]; tcrush.
  - apply (Subs_typed_nocoerce (μ {@ type "B" >: ⊥ <: ⊤})); tcrush.
    + apply (dty_typed String); wtcrush.
    + ettrans;
      [eapply (Mu_stp _ (T := {@ type "B" >: ⊥ <: ⊤ })%ty 0)|]; tcrush.
Qed.
End StringExamples.

(* Sec. 5 of WadlerFest DOT.
IFTFun ≡ { if: ∀(x: {A: ⊥..⊤})∀(t: x.A)∀(f: x.A): x.A }
IFT ≡ { if: IFTFun }

let boolImplV =
ν (b: { Boolean: IFT..IFT } ∧ { true: IFT } ∧ { false: IFT })
{ Boolean = IFT } ∧
{ true = λ(x: {A: ⊥..⊤})λ(t: x.A)λ(f: x.A)t } ∧ { false = λ(x: {A: ⊥..⊤})λ(t: x.A)λ(f: x.A)f }

In fact, that code doesn't typecheck as given, and we fix it by setting.

IFT ≡ IFTFun
 *)
Definition IFTBody := (TAll (p0 @; "A") (TAll (p1 @; "A") (p2 @; "A"))).
Definition IFT : ty :=
  TAll (type "A" >: ⊥ <: ⊤) IFTBody.
Lemma IFTStamped: is_stamped_ty 0 g IFT.
Proof. tcrush. Qed.
Hint Resolve IFTStamped : core.

(* Definition IFT : ty := {@ val "if" : IFTFun }. *)

Definition iftTrue := vabs (vabs' (vabs' (tv x1))).
Definition iftFalse := vabs (vabs' (vabs' (tv x0))).

Example iftTrueTyp Γ : Γ v⊢ₜ[ g ] tv iftTrue : IFT.
Proof. tcrush. exact: Var_typed'. Qed.
Example iftFalseTyp Γ : Γ v⊢ₜ[ g ] tv iftFalse : IFT.
Proof. tcrush. exact: Var_typed'. Qed.

Definition s1_is_ift := g !! s1 = Some IFT.

Definition s1_is_ift_ext := IFT ~[ 0 ] (g, (s1, σ1)).

Lemma get_s1_is_ift : s1_is_ift → s1_is_ift_ext.
Proof. intros; red. by_extcrush. Qed.
Hint Resolve get_s1_is_ift : core.

Definition p0Bool := (p0 @; "Boolean").
Lemma p0BoolStamped: is_stamped_ty 1 g p0Bool.
Proof. tcrush. Qed.
Hint Resolve p0BoolStamped : core.

Definition boolImplV :=
  ν {@
    type "Boolean" = ( σ1; s1 );
    val "true" = pv iftTrue;
    val "false" = pv iftFalse
  }.
(* This type makes "Boolean" nominal by abstracting it. *)
Definition boolImplT : ty :=
  μ {@
    type "Boolean" >: ⊥ <: IFT;
    val "true" : TLater p0Bool;
    val "false" : TLater p0Bool
  }.

Definition boolImplTConcr : ty :=
  μ {@
    typeEq "Boolean" IFT;
    val "true" : IFT;
    val "false" : IFT
  }.

Example SubIFT_P0Bool Γ : {@
    typeEq "Boolean" IFT;
    val "true" : IFT;
    val "false" : IFT
  }%ty :: Γ v⊢ₜ[ g ] IFT, 0 <: p0Bool, 0.
Proof. eapply LSel_stp''; tcrush. varsub; tcrush. Qed.

Example SubIFT_LaterP0Bool' Γ : {@
    typeEq "Boolean" IFT;
    val "true" : IFT;
    val "false" : IFT
  }%ty :: Γ v⊢ₜ[ g ] IFT, 0 <: ▶: p0Bool, 0.
Proof. ettrans; first exact: SubIFT_P0Bool. tcrush. Qed.

Example SubIFT_LaterP0Bool Γ : TLater {@
    typeEq "Boolean" IFT;
    val "true" : TLater p0Bool;
    val "false" : TLater p0Bool
  } :: Γ v⊢ₜ[ g ] IFT, 0 <: ▶: p0Bool, 0.
Proof.
  asideLaters.
  ettrans; first (apply (AddI_stp _ _ 1); tcrush).
  eapply LSel_stp''; tcrush.
  varsub; tcrush.
Qed.

Example boolImplTyp Γ (Hst : s1_is_ift_ext):
  Γ v⊢ₜ[ g ] tv boolImplV : boolImplT.
Proof.
  apply (Subs_typed_nocoerce boolImplTConcr).
  tcrush; by [apply (dty_typed IFT); wtcrush| exact: Var_typed'].
  tcrush; rewrite iterate_0; ltcrush; apply SubIFT_LaterP0Bool'.
Qed.

(* We can also use subtyping on the individual members to type this example. *)
Definition boolImplT0 : ty :=
  μ {@
    typeEq "Boolean" IFT;
    val "true" : TLater p0Bool;
    val "false" : TLater p0Bool
  }.

Lemma dvabs_sub_typed {Γ} V T1 T2 e l L:
  shift T1 :: V :: Γ v⊢ₜ[ g ] e : T2 →
  TLater V :: Γ v⊢ₜ[ g ] TAll T1 T2, 0 <: L, 0 →
  is_stamped_ty (S (length Γ)) g T1 →
  Γ |L V v⊢[ g ]{ l := dpt (pv (vabs e)) } : TVMem l L.
Proof.
  intros He Hsub Hs. apply dpt_pv_typed.
  eapply (Subs_typed (i := 0)); first apply Hsub.
  by apply Lam_typed_strip1.
Qed.

Example boolImplTypAlt Γ (Hst : s1_is_ift_ext):
  Γ v⊢ₜ[ g ] tv boolImplV : boolImplT.
Proof.
  apply (Subs_typed_nocoerce boolImplT0);
    last (tcrush; ettrans; first apply TAnd1_stp; tcrush).
  tcrush; first by apply (dty_typed IFT); wtcrush.
  - eapply Subs_typed_nocoerce; [apply iftTrueTyp|apply SubIFT_LaterP0Bool].
  - eapply Subs_typed_nocoerce; [apply iftFalseTyp|apply SubIFT_LaterP0Bool].
Qed.

(* AND = λ a b. a b False. *)
Definition packBoolean := packTV 0 s1.
Lemma packBooleanTyp0 Γ (Hst : s1_is_ift) :
  Γ v⊢ₜ[ g ] tv packBoolean : typeEq "A" IFT.
Proof. apply (packTV_typed' s1 IFT); eauto 1. Qed.

Lemma packBooleanTyp Γ (Hst : s1_is_ift) :
  Γ v⊢ₜ[ g ] tv packBoolean : type "A" >: ⊥ <: ⊤.
Proof.
  apply (Subs_typed_nocoerce (typeEq "A" IFT)); last tcrush.
  exact: packBooleanTyp0.
Qed.

Lemma packBooleanLB Γ (Hst : s1_is_ift) i :
  Γ v⊢ₜ[ g ] ▶: IFT, i <: (pv packBoolean @; "A"), i.
Proof. by apply /val_LB /packBooleanTyp0. Qed.

Lemma packBooleanUB Γ (Hst : s1_is_ift) i :
  Γ v⊢ₜ[ g ] (pv packBoolean @; "A"), i <: ▶: IFT, i.
Proof. by apply /val_UB /packBooleanTyp0. Qed.

Definition iftAnd false : vl := vabs (vabs'
  (tapp (tapp (tapp (tv x1) (tv packBoolean)) (tv x0)) false)).

Example iftAndTyp Γ (Hst : s1_is_ift):
  Γ v⊢ₜ[ g ] tv (iftAnd (tv iftFalse)) : TAll IFT (TAll IFT (▶:IFT)).
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
  have Hs: is_stamped_dm 0 g (dtysem σ1 s1).
  apply /extr_dtysem_stamped; by [apply: get_s1_is_ift|].

  apply TAllConCov_stp; stcrush.
  { ettrans. exact: packBooleanLB. wtcrush. }
  apply Sub_later_shift; [wtcrush..|].
  apply TAllConCov_stp; stcrush.
  - ettrans. exact: packBooleanLB. wtcrush.
  - eapply Sub_later_shift; [wtcrush..|].
    ettrans. exact: packBooleanUB. tcrush.
Qed.

(* Eta-expand to drop the later. *)

Example iftAndTyp'1 Γ (Hst : s1_is_ift):
  Γ v⊢ₜ[ g ] vabs' (vabs'
    (tskip
      (tapp (tapp (tv (iftAnd (tv iftFalse))) (tv x1)) (tv x0)))) :
    TAll IFT (TAll IFT IFT).
Proof.
  tcrush; rewrite -(iterate_S tskip 0).
  eapply (Subs_typed (T1 := ▶:IFT)); first tcrush.
  eapply App_typed; last exact: Var_typed';
    eapply App_typed; last exact: Var_typed'; rewrite /= -/IFT.
  apply iftAndTyp; eauto.
Qed.

Definition iftCoerce t :=
  lett t (vabs' (vabs' (tskip (tapp (tapp (tv x2) (tv x1)) (tv x0))))).

Lemma coerce_tAppIFT Γ t T :
  is_stamped_ty (length Γ) g T →
  Γ v⊢ₜ[ g ] t : TAll T (TAll (shift T) (▶: shiftN 2 T)) →
  Γ v⊢ₜ[ g ] iftCoerce t : TAll T (TAll (shift T) (shiftN 2 T)).
Proof.
  move => HsT1 Ht.
  move: (HsT1) => /is_stamped_ren1_ty HsT2.
  move: (HsT2) => /is_stamped_ren1_ty; rewrite -hrenS => HsT3.
  move: (HsT3) => /is_stamped_ren1_ty; rewrite -hrenS => HsT4.
  eapply Let_typed; [exact: Ht| |tcrush].
  rewrite /= !(hren_upn_gen 1) (hren_upn_gen 2) /=.
  tcrush; rewrite -!hrenS -(iterate_S tskip 0).
  eapply (Subs_typed (T1 := ▶:T.|[_])); first tcrush.
  eapply App_typed; last exact: Var_typed';
    eapply App_typed; last exact: Var_typed'.
  apply: Var_typed' => //.
  rewrite /= !(hren_upn 1) (hren_upn_gen 1) (hren_upn_gen 2)
    !hsubst_comp !ren_ren_comp /=. done.
Qed.

Example iftAndTyp'2 Γ (Hst : s1_is_ift):
  Γ v⊢ₜ[ g ] iftCoerce (tv (iftAnd (tv iftFalse))) : TAll IFT (TAll IFT IFT).
Proof. intros. apply /coerce_tAppIFT /iftAndTyp; tcrush. Qed.

Lemma subIFT i Γ T:
  is_stamped_ty (length Γ) g (shiftN i T) →
  (typeEq "A" T.|[ren (+1+i)]) :: Γ v⊢ₜ[ g ] IFTBody, 0 <:
    TAll T.|[ren (+1+i)] (TAll T.|[ren (+2+i)] (▶: T.|[ren (+3+i)])), 0.
Proof.
  rewrite /= -/IFTBody => HsT1.
  move: (HsT1) => /is_stamped_ren1_ty HsT2; rewrite -hrenS in HsT2.
  move: (HsT2) => /is_stamped_ren1_ty HsT3; rewrite -hrenS in HsT3.
  tcrush; rewrite ?iterate_S ?iterate_0 /=;
    first [apply: LSel_stp' | apply: SelU_stp]; tcrush; apply: Var_typed';
    rewrite ?hsubst_id //; by autosubst.
Qed.

Lemma tAppIFT_typed Γ T t s :
  is_stamped_ty (length Γ) g T →
  g !! s = Some (shift T) →
  Γ v⊢ₜ[ g ] t : IFT →
  Γ v⊢ₜ[ g ] tApp Γ t s :
    TAll T (TAll (shift T) (▶: shiftN 2 T)).
Proof.
  move => HsT1 Hl Ht; move: (HsT1) => /is_stamped_ren1_ty HsT2.
  intros; eapply typeApp_typed => //; tcrush.
  intros; asimpl. exact: (subIFT 1).
Qed.

Lemma tAppIFT_coerced_typed Γ T t s :
  is_stamped_ty (length Γ) g T →
  g !! s = Some (shift T) →
  Γ v⊢ₜ[ g ] t : IFT →
  Γ v⊢ₜ[ g ] iftCoerce (tApp Γ t s) :
    TAll T (TAll (shift T) (shiftN 2 T)).
Proof. intros. by apply /coerce_tAppIFT /tAppIFT_typed. Qed.

Lemma tAppIFT_coerced_typed_IFT Γ t s :
  g !! s = Some IFT →
  Γ v⊢ₜ[ g ] t : IFT →
  Γ v⊢ₜ[ g ] iftCoerce (tApp Γ t s) :
    TAll IFT (TAll IFT IFT).
Proof. intros. apply tAppIFT_coerced_typed; eauto 2. Qed.

Definition IFTp0 := TAll p0Bool (TAll (shift p0Bool) ((shiftN 2 p0Bool))).

Lemma tAppIFT_coerced_typed_p0Boolean Γ T t s :
  g !! s = Some (shift p0Bool) →
  T :: Γ v⊢ₜ[ g ] t : IFT →
  T :: Γ v⊢ₜ[ g ] iftCoerce (tApp (T :: Γ) t s) :
    TAll p0Bool (TAll (shift p0Bool) (shiftN 2 p0Bool)).
Proof. intros. apply tAppIFT_coerced_typed; eauto 3. Qed.

Definition iftNot Γ t s :=
  tapp (tapp
      (iftCoerce (tApp Γ t s))
    (tv iftFalse))
  (tv iftTrue).

Lemma iftNotTyp Γ T t s :
  g !! s = Some IFT →
  Γ v⊢ₜ[ g ] t : IFT →
  Γ v⊢ₜ[ g ] iftNot Γ t s : IFT.
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
  g !! s = Some IFT →
  Γ v⊢ₜ[ g ] t1 : IFT →
  Γ v⊢ₜ[ g ] t2 : IFT →
  Γ v⊢ₜ[ g ] iftAnd2 Γ t1 t2 s : IFT.
Proof.
  intros Hs Ht1 Ht2.
  eapply App_typed; last exact: iftFalseTyp.
  eapply App_typed; last exact: Ht2.
  exact: tAppIFT_coerced_typed_IFT.
Qed.

End examples.
