(**
WIP examples constructing syntactic typing derivations.
I am also experimenting with notations, but beware the current definitions are pretty bad.
 *)

From D Require Import tactics.
From D.Dot Require Import syn storeless_typing_ex_utils
  unstampedness_binding stampedness_binding ast_stamping.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Notation HashableString := (μ {@ val "hashCode" : TAll TUnit TInt }).
Section examples.
(* From D Require Import typeExtraction *)
Context {g : stys}.

(********************)
(** MICRO-EXAMPLES **)
(********************)

Example ex0 e Γ T:
  Γ v⊢ₜ[ g ] e : T →
  is_unstamped_ty' (length Γ) T →
  Γ v⊢ₜ[ g ] e : ⊤.
Proof. intros. apply (iT_ISub_nocoerce T TTop); tcrush. Qed.

Example ex1 Γ (n : Z) T:
  Γ v⊢ₜ[ g ] ν {@ val "a" = n } : μ {@ val "a" : TInt }.
Proof.
  (* Help proof search: Avoid trying iT_Mu_I, that's slow. *)
  apply iT_Obj_I; tcrush.
Qed.

Example ex2 Γ T
  (Hg: g !! s1 = Some (x0 @; "B")):
  Γ v⊢ₜ[ g ] ν {@ type "A" = (idsσ 1 ; s1) } :
    TMu (TAnd (TTMem "A" TBot TTop) TTop).
Proof.
  have Hs: (x0 @; "B") ~[ 1 ] (g, (s1, idsσ 1)).
  by_extcrush.
  have Hst: is_stamped_ty (1 + length Γ) g (x0 @; "B").
  by tcrush.
  apply iT_Obj_I; tcrush. (* Avoid trying iT_Mu_I, that's slow. *)
  apply (iD_Typ_Abs (x0 @; "B")); cbn; by wtcrush.
Qed.

(* Try out fixpoints. *)
Definition F3 T :=
  TMu (TAnd (TTMemL "A" T T) TTop).

Example ex3 Γ T
  (Hg: g !! s1 = Some (F3 (x0 @; "A"))):
  Γ v⊢ₜ[ g ] ν {@ type "A" = (σ1 ; s1) } :
    F3 (F3 (TSel x0 "A")).
Proof.
  have Hs: F3 (x0 @; "A") ~[ 0 ] (g, (s1, σ1)).
  by_extcrush.
  have Hst: is_stamped_ty (1 + length Γ) g (F3 (x0 @; "A")).
  by stcrush.
  apply iT_Obj_I; tcrush. (* Avoid trying iT_Mu_I, that's slow. *)
  apply (iD_Typ_Abs (F3 (x0 @; "A"))); by wtcrush.
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
Definition KeysT : ty := μ {@
  type "Key" >: ⊥ <: ⊤;
  val "key": TAll HashableString (x1 @; "Key")
}.
Definition hashKeys : vl := ν {@
  type "Key" = (σ1; s1);
  val "key" = vabs (tapp (tproj x0 "hashCode") tUnit)
}.
Definition s1_is_tint :=
  TInt ~[ 0 ] (g, (s1, σ1)).
Lemma get_s1_is_tint : g !! s1 = Some TInt → s1_is_tint.
Proof. by_extcrush. Qed.

(* To typecheck the object body, we first typecheck it with a tighter type,
    and then widen it. *)
Definition KeysT' := μ {@
  type "Key" >: TInt <: ⊤;
  val "key": TAll HashableString (x1 @; "Key")
}.
(* IDEA for our work: use [(type "Key" >: TInt <: ⊤) ⩓ (type "Key" >: ⊥ <: ⊤)]. *)

Example hashKeys_typed Γ (Hs1 : s1_is_tint):
  Γ v⊢ₜ[ g ] hashKeys : KeysT.
Proof.
  cut (Γ v⊢ₜ[ g ] hashKeys : KeysT').
  { intros H.
    apply (iT_ISub_nocoerce KeysT'); first done.
    apply iMu_Sub_Mu; last stcrush.
    tcrush.
    ettrans; first apply iAnd1_Sub; tcrush.
  }
  apply iT_Obj_I; tcrush.
  by apply (iD_Typ_Abs TInt); wtcrush.
  cbn; apply (iT_All_E (T1 := TUnit));
    last eapply (iT_ISub_nocoerce TInt); tcrush.
  tcrush; cbn.

  pose (T0 := μ {@ val "hashCode" : TAll ⊤ 𝐙 }).

  have Htp: ∀ Γ', T0 :: Γ' v⊢ₜ[ g ] x0 : val "hashCode" : TAll ⊤ TInt. {
    intros. eapply iT_ISub_nocoerce.
    by eapply iT_Mu_E'; [exact: iT_Var'| |stcrush].
    by apply iAnd1_Sub; tcrush.
  }
  apply (iT_ISub_nocoerce (val "hashCode" : TAll ⊤ 𝐙)). exact: Htp.
  tcrush.
  eapply iSub_Sel', (path_tp_delay (i := 0)); wtcrush.
  varsub; tcrush.
Qed.

Section StringExamples.
(* new {
  val subSys1 : { z => type A <: Int } = new { type A = Int }
  val subSys2 : { z => type B } = new { type B = String }
} *)
Context (String : ty) (HclString : is_stamped_ty 0 g String).

(* Term *)
Definition systemVal := ν {@
  val "subSys1" = ν {@ type "A" = (σ1; s1) } ;
  val "subSys2" = ν {@ type "B" = (σ2; s2) } }.
Definition s2_is_String :=
  String ~[ 0 ] (g, (s2, σ2)).
Lemma get_s2_is_String : g !! s2 = Some String → s2_is_String.
Proof using HclString. by_extcrush. Qed.

(* Type *)
Definition systemValT := μ {@
  val "subSys1" : μ {@ type "A" >: ⊥ <: TInt};
  val "subSys2" : μ {@ type "B" >: ⊥ <: ⊤}}.

Example motivEx Γ (Hs1: s1_is_tint) (Hs2: s2_is_String)
  (HuString: is_unstamped_ty' 0 String):
  Γ v⊢ₜ[ g ] systemVal : systemValT.
Proof.
  apply iT_Obj_I; tcrush.
  all: [> apply (iD_Typ_Abs TInt) | apply (iD_Typ_Abs String) ]; wtcrush.
Qed.

(* Uh, we can unfold recursive types during construction! Does that allow
us to encode mutual recursion? Write this up. *)
Definition systemValT' := μ {@
  val "subSys1" : type "A" >: ⊥ <: TInt;
  val "subSys2" : type "B" >: ⊥ <: ⊤}.
Example motivEx1 Γ (Hs1: s1_is_tint) (Hs2: s2_is_String)
  (HuString: is_unstamped_ty' 0 String):
  Γ v⊢ₜ[ g ] systemVal : systemValT'.
Proof.
  apply iT_Obj_I; tcrush.
  - apply (iT_ISub_nocoerce (μ {@ type "A" >: ⊥ <: TInt})); tcrush.
    + apply (iD_Typ_Abs TInt); wtcrush.
    + ettrans;
      [apply: (iMu_Sub (T := {@ type "A" >: ⊥ <: TInt })%ty 0)|]; tcrush.
  - apply (iT_ISub_nocoerce (μ {@ type "B" >: ⊥ <: ⊤})); tcrush.
    + apply (iD_Typ_Abs String); wtcrush.
    + ettrans;
      [apply: (iMu_Sub (T := {@ type "B" >: ⊥ <: ⊤ })%ty 0)|]; tcrush.
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
Definition IFTBody := (TAll (x0 @; "A") (TAll (x1 @; "A") (x2 @; "A"))).
Definition IFT : ty :=
  TAll (type "A" >: ⊥ <: ⊤) IFTBody.
Lemma IFTUnstamped: is_unstamped_ty' 0 IFT.
Proof. tcrush. Qed.
Lemma IFTStamped: is_stamped_ty 0 g IFT.
Proof. tcrush. Qed.
Hint Resolve IFTUnstamped IFTStamped : core.

(* Definition IFT : ty := {@ val "if" : IFTFun }. *)

Definition iftTrue := vabs (vabs (vabs x1)).
Definition iftFalse := vabs (vabs (vabs x0)).

Example iftTrueTyp Γ : Γ v⊢ₜ[ g ] iftTrue : IFT.
Proof. tcrush. exact: iT_Var'. Qed.
Example iftFalseTyp Γ : Γ v⊢ₜ[ g ] iftFalse : IFT.
Proof. tcrush. exact: iT_Var'. Qed.

Definition s1_is_ift := g !! s1 = Some IFT.

Definition s1_is_ift_ext := IFT ~[ 0 ] (g, (s1, σ1)).

Lemma get_s1_is_ift : s1_is_ift → s1_is_ift_ext.
Proof. intros; red. by_extcrush. Qed.
Hint Resolve get_s1_is_ift : core.

Definition p0Bool := x0 @; "Boolean".
Lemma p0BoolStamped: is_stamped_ty 1 g p0Bool.
Proof. tcrush. Qed.
Hint Resolve p0BoolStamped : core.

Definition boolImplV :=
  ν {@
    type "Boolean" = ( σ1; s1 );
    val "true" = iftTrue;
    val "false" = iftFalse
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
Proof. eapply iSub_Sel''; tcrush. varsub; tcrush. Qed.

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
  ettrans; first (apply (iSub_AddI _ _ 1); tcrush).
  eapply iSub_Sel''; tcrush.
  varsub; tcrush.
Qed.

Example boolImplTyp Γ (Hst : s1_is_ift_ext):
  Γ v⊢ₜ[ g ] boolImplV : boolImplT.
Proof.
  apply (iT_ISub_nocoerce boolImplTConcr).
  tcrush; by [apply (iD_Typ_Abs IFT); wtcrush| exact: iT_Var'].
  tcrush; rewrite iterate_0; ltcrush; apply SubIFT_LaterP0Bool'.
Qed.

(* We can also use subtyping on the individual members to type this example. *)
Definition boolImplT0 : ty :=
  μ {@
    typeEq "Boolean" IFT;
    val "true" : TLater p0Bool;
    val "false" : TLater p0Bool
  }.

Lemma iD_Lam_Sub {Γ} V T1 T2 e l L:
  shift T1 :: V :: Γ v⊢ₜ[ g ] e : T2 →
  TLater V :: Γ v⊢ₜ[ g ] TAll T1 T2, 0 <: L, 0 →
  is_stamped_ty (S (length Γ)) g T1 →
  Γ |L V v⊢[ g ]{ l := dpt (pv (vabs e)) } : TVMem l L.
Proof.
  intros He Hsub Hs. apply iD_Val.
  eapply (iT_ISub (i := 0)); first apply Hsub.
  by apply iT_All_I_strip1.
Qed.

Example boolImplTypAlt Γ (Hst : s1_is_ift_ext):
  Γ v⊢ₜ[ g ] boolImplV : boolImplT.
Proof.
  apply (iT_ISub_nocoerce boolImplT0);
    last (tcrush; ettrans; first apply iAnd1_Sub; tcrush).
  tcrush; first by apply (iD_Typ_Abs IFT); wtcrush.
  - eapply iT_ISub_nocoerce; [apply iftTrueTyp|apply SubIFT_LaterP0Bool].
  - eapply iT_ISub_nocoerce; [apply iftFalseTyp|apply SubIFT_LaterP0Bool].
Qed.

(* AND = λ a b. a b False. *)
Definition packBoolean := packTV 0 s1.
Lemma packBooleanTyp0 Γ (Hst : s1_is_ift) :
  Γ v⊢ₜ[ g ] packBoolean : typeEq "A" IFT.
Proof. apply (packTV_typed' s1 IFT); eauto 1. Qed.

Lemma packBooleanTyp Γ (Hst : s1_is_ift) :
  Γ v⊢ₜ[ g ] packBoolean : type "A" >: ⊥ <: ⊤.
Proof.
  apply (iT_ISub_nocoerce (typeEq "A" IFT)); last tcrush.
  exact: packBooleanTyp0.
Qed.

Lemma is_stamped_dm_s1 (Hst : s1_is_ift) : is_stamped_dm 0 g (dtysem σ1 s1).
Proof.
  (* apply /extr_dtysem_stamped; by [apply: get_s1_is_ift|]. *)
  eapply is_stamped_dtysem with (m := 0); tcrush.
Qed.
Hint Resolve is_stamped_dm_s1 : core.

Definition iftCoerce t :=
  lett t (vabs (vabs (tskip (x2 $: x1 $: x0)))).

Hint Immediate unstamped_stamped_type : core.
Lemma coerce_tAppIFT Γ t T :
  is_unstamped_ty' (length Γ) T →
  Γ v⊢ₜ[ g ] t : TAll T (TAll (shift T) (▶: shiftN 2 T)) →
  Γ v⊢ₜ[ g ] iftCoerce t : TAll T (TAll (shift T) (shiftN 2 T)).
Proof.
  move => HuT1 Ht.
  move: (HuT1) => /is_unstamped_ren1_ty HuT2.
  move: (HuT2) => /is_unstamped_ren1_ty; rewrite -hrenS => HuT3.
  move: (HuT3) => /is_unstamped_ren1_ty; rewrite -hrenS => HuT4.
  eapply iT_Let; [exact: Ht| |tcrush].
  rewrite /= !(hren_upn_gen 1) (hren_upn_gen 2) /=.
  tcrush; [exact: unstamped_stamped_type..|];
    rewrite -!hrenS -!(iterate_S tskip 0).
  eapply (iT_ISub (T1 := ▶:T.|[_])); first tcrush.
  eapply iT_All_E; last exact: iT_Var';
    eapply iT_All_E; last exact: iT_Var'.
  apply: iT_Var' => //.
  rewrite /= !(hren_upn 1) (hren_upn_gen 1) (hren_upn_gen 2)
    !hsubst_comp !ren_ren_comp /=. done.
Qed.

Lemma subIFT i Γ T:
  is_unstamped_ty' (length Γ) (shiftN i T) →
  (typeEq "A" T.|[ren (+1+i)]) :: Γ v⊢ₜ[ g ] IFTBody, 0 <:
    TAll T.|[ren (+1+i)] (TAll T.|[ren (+2+i)] (▶: T.|[ren (+3+i)])), 0.
Proof.
  rewrite /= -/IFTBody => HuT1.
  move: (HuT1) => /is_unstamped_ren1_ty HuT2; rewrite -hrenS in HuT2.
  move: (HuT2) => /is_unstamped_ren1_ty HuT3; rewrite -hrenS in HuT3.
  move: (HuT3) => /is_unstamped_ren1_ty HuT4; rewrite -hrenS in HuT4.
  tcrush; rewrite ?iterate_S ?iterate_0 /=; tcrush;
    first [eapply iSub_Sel', (path_tp_delay (i := 0)) |
      eapply iSel_Sub, (path_tp_delay (i := 0))];
      try apply: iP_Var';
    rewrite ?hsubst_id -?hrenS //; try autosubst; wtcrush.
Qed.

Lemma tAppIFT_typed Γ T t s :
  is_unstamped_ty' (length Γ) T →
  g !! s = Some (shift T) →
  Γ v⊢ₜ[ g ] t : IFT →
  Γ v⊢ₜ[ g ] tApp Γ t s :
    TAll T (TAll (shift T) (▶: shiftN 2 T)).
Proof.
  move => HsT1 Hl Ht; move: (HsT1) => /is_unstamped_ren1_ty HsT2.
  intros; eapply typeApp_typed => //; tcrush.
  intros; asimpl. exact: (subIFT 1).
Qed.

Lemma tAppIFT_coerced_typed Γ T t s :
  is_unstamped_ty' (length Γ) T →
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
Proof. intros. apply tAppIFT_coerced_typed; tcrush. Qed.

Definition iftNot Γ t s :=
  tapp (tapp
      (iftCoerce (tApp Γ t s))
    iftFalse)
  iftTrue.

Lemma iftNotTyp Γ T t s :
  g !! s = Some IFT →
  Γ v⊢ₜ[ g ] t : IFT →
  Γ v⊢ₜ[ g ] iftNot Γ t s : IFT.
Proof.
  intros.
  eapply iT_All_E; last exact: iftTrueTyp.
  eapply iT_All_E; last exact: iftFalseTyp.
  exact: tAppIFT_coerced_typed_IFT.
Qed.

Definition iftAnd2 Γ t1 t2 s :=
  iftCoerce (tApp Γ t1 s) $: t2 $:
  iftFalse.

Lemma iftAndTyp2 Γ T t1 t2 s :
  g !! s = Some IFT →
  Γ v⊢ₜ[ g ] t1 : IFT →
  Γ v⊢ₜ[ g ] t2 : IFT →
  Γ v⊢ₜ[ g ] iftAnd2 Γ t1 t2 s : IFT.
Proof.
  intros Hs Ht1 Ht2.
  eapply iT_All_E; last exact: iftFalseTyp.
  eapply iT_All_E; last exact: Ht2.
  exact: tAppIFT_coerced_typed_IFT.
Qed.

End examples.
