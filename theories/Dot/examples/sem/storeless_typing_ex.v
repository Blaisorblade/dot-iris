(**
WIP examples constructing syntactic typing derivations.
I am also experimenting with notations, but beware the current definitions are pretty bad.
 *)

From D Require Import tactics.
From D.Dot Require Import syn storeless_typing_ex_utils
  unstampedness_binding.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Notation HashableString := (μ {@ val "hashCode" : TAll TUnit TInt }).
(* From D Require Import typeExtraction *)

(********************)
(** MICRO-EXAMPLES **)
(********************)

Example ex0 e Γ T:
  Γ v⊢ₜ e : T →
  is_unstamped_ty' (length Γ) T →
  Γ v⊢ₜ e : ⊤.
Proof. intros. apply (iT_ISub_nocoerce T TTop); tcrush. Qed.

Example ex1 Γ (n : Z) T:
  Γ v⊢ₜ ν {@ val "a" = n } : μ {@ val "a" : TInt }.
Proof.
  (* Help proof search: Avoid trying iT_Mu_I, that's slow. *)
  apply iT_Obj_I; tcrush.
Qed.

Example ex2 Γ T :
  Γ v⊢ₜ ν {@ type "A" = (idsσ 1 ; s1) } :
    TMu (TAnd (TTMem "A" TBot TTop) TTop).
Proof.
  apply iT_Obj_I; tcrush. (* Avoid trying iT_Mu_I, that's slow. *)
  apply (iD_Typ_Abs_old (x0 @; "B")); cbn; wtcrush. tcrush_nclosed.
Qed.

(* Try out fixpoints. *)
Definition F3 T :=
  TMu (TAnd (TTMemL "A" T T) TTop).

Example ex3 Γ T :
  Γ v⊢ₜ ν {@ type "A" = (σ1 ; s1) } :
    F3 (F3 (TSel x0 "A")).
Proof.
  apply iT_Obj_I; tcrush. (* Avoid trying iT_Mu_I, that's slow. *)
  apply (iD_Typ_Abs_old (F3 (x0 @; "A"))); by wtcrush.
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

(* To typecheck the object body, we first typecheck it with a tighter type,
    and then widen it. *)
Definition KeysT' := μ {@
  type "Key" >: TInt <: ⊤;
  val "key": TAll HashableString (x1 @; "Key")
}.
(* IDEA for our work: use [(type "Key" >: TInt <: ⊤) ⩓ (type "Key" >: ⊥ <: ⊤)]. *)

Example hashKeys_typed Γ :
  Γ v⊢ₜ hashKeys : KeysT.
Proof.
  cut (Γ v⊢ₜ hashKeys : KeysT').
  { intros H.
    apply (iT_ISub_nocoerce KeysT'); first done.
    apply iMu_Sub_Mu; last stcrush.
    tcrush.
    ettrans; first apply iAnd1_Sub; tcrush.
  }
  apply iT_Obj_I; tcrush.
  by apply (iD_Typ_Abs_old TInt); wtcrush.
  cbn; apply (iT_All_E (T1 := TUnit));
    last eapply (iT_ISub_nocoerce TInt); tcrush.
  tcrush; cbn.

  pose (T0 := μ {@ val "hashCode" : TAll ⊤ 𝐙 }).

  have Htp: ∀ Γ', T0 :: Γ' v⊢ₜ x0 : val "hashCode" : TAll ⊤ TInt. {
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
Context (String : ty).

(* Term *)
Definition systemVal := ν {@
  val "subSys1" = ν {@ type "A" = (σ1; s1) } ;
  val "subSys2" = ν {@ type "B" = (σ2; s2) } }.

(* Type *)
Definition systemValT := μ {@
  val "subSys1" : μ {@ type "A" >: ⊥ <: TInt};
  val "subSys2" : μ {@ type "B" >: ⊥ <: ⊤}}.

Example motivEx Γ
  (HuString: is_unstamped_ty' 0 String):
  Γ v⊢ₜ systemVal : systemValT.
Proof.
  apply iT_Obj_I; tcrush.
  all: [> apply (iD_Typ_Abs_old TInt) | apply (iD_Typ_Abs_old String) ]; wtcrush.
Qed.

(* Uh, we can unfold recursive types during construction! Does that allow
us to encode mutual recursion? Write this up. *)
Definition systemValT' := μ {@
  val "subSys1" : type "A" >: ⊥ <: TInt;
  val "subSys2" : type "B" >: ⊥ <: ⊤}.
Example motivEx1 Γ
  (HuString: is_unstamped_ty' 0 String):
  Γ v⊢ₜ systemVal : systemValT'.
Proof.
  apply iT_Obj_I; tcrush.
  - apply (iT_ISub_nocoerce (μ {@ type "A" >: ⊥ <: TInt})); tcrush.
    + apply (iD_Typ_Abs_old TInt); wtcrush.
    + ettrans;
      [apply: (iMu_Sub _ {@ type "A" >: ⊥ <: TInt } 0)|]; tcrush.
  - apply (iT_ISub_nocoerce (μ {@ type "B" >: ⊥ <: ⊤})); tcrush.
    + apply (iD_Typ_Abs_old String); wtcrush.
    + ettrans;
      [apply: (iMu_Sub _ {@ type "B" >: ⊥ <: ⊤ } 0)|]; tcrush.
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
Hint Resolve IFTUnstamped : core.

(* Definition IFT : ty := {@ val "if" : IFTFun }. *)

Definition iftTrue := vabs (vabs (vabs x1)).
Definition iftFalse := vabs (vabs (vabs x0)).

Example iftTrueTyp Γ : Γ v⊢ₜ iftTrue : IFT.
Proof. tcrush. exact: iT_Var'. Qed.
Example iftFalseTyp Γ : Γ v⊢ₜ iftFalse : IFT.
Proof. tcrush. exact: iT_Var'. Qed.

Definition p0Bool := x0 @; "Boolean".

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
  }%ty :: Γ v⊢ₜ IFT, 0 <: p0Bool, 0.
Proof. eapply iSub_Sel''; tcrush. varsub; tcrush. Qed.

Example SubIFT_LaterP0Bool' Γ : {@
    typeEq "Boolean" IFT;
    val "true" : IFT;
    val "false" : IFT
  }%ty :: Γ v⊢ₜ IFT, 0 <: ▶: p0Bool, 0.
Proof. ettrans; first exact: SubIFT_P0Bool. tcrush. Qed.

Example SubIFT_LaterP0Bool Γ : TLater {@
    typeEq "Boolean" IFT;
    val "true" : TLater p0Bool;
    val "false" : TLater p0Bool
  } :: Γ v⊢ₜ IFT, 0 <: ▶: p0Bool, 0.
Proof.
  asideLaters.
  ettrans; first (apply (iSub_AddI _ _ 1); tcrush).
  eapply iSub_Sel''; tcrush.
  varsub; tcrush.
Qed.

Example boolImplTyp Γ :
  Γ v⊢ₜ boolImplV : boolImplT.
Proof.
  apply (iT_ISub_nocoerce boolImplTConcr).
  tcrush; by [apply (iD_Typ_Abs_old IFT); wtcrush| exact: iT_Var'].
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
  shift T1 :: V :: Γ v⊢ₜ e : T2 →
  TLater V :: Γ v⊢ₜ TAll T1 T2, 0 <: L, 0 →
  Γ |L V v⊢{ l := dpt (pv (vabs e)) } : TVMem l L.
Proof.
  intros He Hsub. apply iD_Val.
  eapply (iT_ISub (i := 0)); first apply Hsub.
  by apply iT_All_I_strip1.
Qed.

Example boolImplTypAlt Γ :
  Γ v⊢ₜ boolImplV : boolImplT.
Proof.
  apply (iT_ISub_nocoerce boolImplT0);
    last (tcrush; ettrans; first apply iAnd1_Sub; tcrush).
  tcrush; first by apply (iD_Typ_Abs_old IFT); wtcrush.
  - eapply iT_ISub_nocoerce; [apply iftTrueTyp|apply SubIFT_LaterP0Bool].
  - eapply iT_ISub_nocoerce; [apply iftFalseTyp|apply SubIFT_LaterP0Bool].
Qed.

(* AND = λ a b. a b False. *)
Definition packBoolean := packTV 0 s1.
Lemma packBooleanTyp0 Γ :
  Γ v⊢ₜ packBoolean : typeEq "A" IFT.
Proof. eapply (packTV_typed' s1 IFT); eauto 1. Qed.

Lemma packBooleanTyp Γ :
  Γ v⊢ₜ packBoolean : type "A" >: ⊥ <: ⊤.
Proof.
  apply (iT_ISub_nocoerce (typeEq "A" IFT)); last tcrush.
  exact: packBooleanTyp0.
Qed.

Definition iftCoerce t :=
  lett t (vabs (vabs (tskip (x2 $: x1 $: x0)))).

Lemma coerce_tAppIFT Γ t T :
  is_unstamped_ty' (length Γ) T →
  Γ v⊢ₜ t : TAll T (TAll (shift T) (▶: shiftN 2 T)) →
  Γ v⊢ₜ iftCoerce t : TAll T (TAll (shift T) (shiftN 2 T)).
Proof.
  move => HuT1 Ht.
  move: (HuT1) => /is_unstamped_ren1_ty HuT2.
  move: (HuT2) => /is_unstamped_ren1_ty; rewrite -hrenS => HuT3.
  move: (HuT3) => /is_unstamped_ren1_ty; rewrite -hrenS => HuT4.
  eapply iT_Let; [exact: Ht|].
  rewrite /= !(hren_upn_gen 1) (hren_upn_gen 2) /=.
  tcrush;
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
  (typeEq "A" T.|[ren (+1+i)]) :: Γ v⊢ₜ IFTBody, 0 <:
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
  Γ v⊢ₜ t : IFT →
  Γ v⊢ₜ tApp Γ t s :
    TAll T (TAll (shift T) (▶: shiftN 2 T)).
Proof.
  move => HsT1 Ht; move: (HsT1) => /is_unstamped_ren1_ty HsT2.
  intros; eapply typeApp_typed => //; tcrush.
  intros; asimpl. exact: (subIFT 1).
Qed.

Lemma tAppIFT_coerced_typed Γ T t s :
  is_unstamped_ty' (length Γ) T →
  Γ v⊢ₜ t : IFT →
  Γ v⊢ₜ iftCoerce (tApp Γ t s) :
    TAll T (TAll (shift T) (shiftN 2 T)).
Proof. intros. by apply /coerce_tAppIFT /tAppIFT_typed. Qed.

Lemma tAppIFT_coerced_typed_IFT Γ t s :
  Γ v⊢ₜ t : IFT →
  Γ v⊢ₜ iftCoerce (tApp Γ t s) :
    TAll IFT (TAll IFT IFT).
Proof. intros. apply tAppIFT_coerced_typed; eauto 2. Qed.

Definition IFTp0 := TAll p0Bool (TAll (shift p0Bool) ((shiftN 2 p0Bool))).

Lemma tAppIFT_coerced_typed_p0Boolean Γ T t s :
  T :: Γ v⊢ₜ t : IFT →
  T :: Γ v⊢ₜ iftCoerce (tApp (T :: Γ) t s) :
    TAll p0Bool (TAll (shift p0Bool) (shiftN 2 p0Bool)).
Proof. intros. apply tAppIFT_coerced_typed; tcrush. Qed.

Definition iftNot Γ t s :=
  tapp (tapp
      (iftCoerce (tApp Γ t s))
    iftFalse)
  iftTrue.

Lemma iftNotTyp Γ T t s :
  Γ v⊢ₜ t : IFT →
  Γ v⊢ₜ iftNot Γ t s : IFT.
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
  Γ v⊢ₜ t1 : IFT →
  Γ v⊢ₜ t2 : IFT →
  Γ v⊢ₜ iftAnd2 Γ t1 t2 s : IFT.
Proof.
  intros Ht1 Ht2.
  eapply iT_All_E; last exact: iftFalseTyp.
  eapply iT_All_E; last exact: Ht2.
  exact: tAppIFT_coerced_typed_IFT.
Qed.
