(**
WIP examples constructing _unstamped_ syntactic typing derivations.
 *)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn unstampedness_binding.
From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived.
From D.Dot Require Import exampleInfra hoas scalaLib.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Import DBNotation.

Example ex0 e Γ T:
  Γ u⊢ₜ e : T →
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ e : ⊤.
Proof. intros. apply (Subs_typed_nocoerce T TTop); tcrush. Qed.

Example ex1 Γ n T:
  Γ u⊢ₜ tv (ν {@ val "a" = pv (vnat n)}) : μ {@ val "a" : TNat }.
Proof.
  (* Help proof search: Avoid trying TMuI_typed, that's slow. *)
  apply VObj_typed; tcrush.
Qed.

Example ex2 Γ T :
  Γ u⊢ₜ tv (ν {@ type "A" = p0 @; "B" } ) : TMu (TAnd (TTMem "A" TBot TTop) TTop).
Proof. apply VObj_typed; tcrush. Qed.

(* Try out fixpoints. *)
Definition F3 T :=
  TMu (TAnd (TTMem "A" T T) TTop).

Example ex3 Γ T:
  Γ u⊢ₜ tv (ν {@ type "A" = F3 (p0 @; "A") } ) : F3 (F3 (TSel p0 "A")).
Proof. apply VObj_typed; tcrush. Qed.

Definition KeysT : ty := μ {@
  type "Key" >: ⊥ <: ⊤;
  val "key": HashableString →: p0 @; "Key"
}.
Definition hashKeys : vl := ν {@
  type "Key" = TNat;
  val "key" = pv (vabs (tapp (tproj (tv x0) "hashCode") tUnit))
}.

Definition KeysTConcr := μ {@
  type "Key" >: TNat <: ⊤;
  val "key" : HashableString →: p0 @; "Key"
}.

(* IDEA for our work: use [(type "Key" >: TNat <: ⊤) ⩓ (type "Key" >: ⊥ <: ⊤)]. *)
Example hashKeys_typed Γ:
  Γ u⊢ₜ tv hashKeys : KeysT.
Proof.
  apply (Subs_typed_nocoerce KeysTConcr); first last. {
    apply Mu_stp_mu; last stcrush.
    tcrush.
    lThis.
  }
  tcrush.
  apply App_typed with (T1 := TUnit);
    last eapply (Subs_typed_nocoerce TNat); tcrush.

  apply (Subs_typed_nocoerce (val "hashCode" : ⊤ →: 𝐍)).
  by eapply Subs_typed_nocoerce; [eapply TMuE_typed'; by [var||stcrush] | tcrush].
  tcrush.
  eapply LSel_stp', (path_tp_weaken (i := 0)); wtcrush.
  varsub; tcrush.
Qed.

(* We can also use subtyping on the individual members to type this example. *)
Definition boolImplT0 : ty :=
  μ {@
    typeEq "Boolean" IFT;
    val "true" : TLater p0Bool;
    val "false" : TLater p0Bool
  }.

Example boolImplTypAlt Γ :
  Γ u⊢ₜ tv boolImplV : boolImplT.
Proof.
  apply (Subs_typed_nocoerce boolImplT0);
    last (tcrush; lThis).
  tcrush.
  - eapply Subs_typed_nocoerce; [apply iftTrueTyp|apply SubIFT_LaterP0Bool].
  - eapply Subs_typed_nocoerce; [apply iftFalseTyp|apply SubIFT_LaterP0Bool].
Qed.

(* Utilities needed for not. *)
Lemma subIFT i Γ T:
  is_unstamped_ty' (length Γ) (shiftN i T) →
  (typeEq "A" T.|[ren (+1+i)]) :: Γ u⊢ₜ IFTBody, 0 <:
    TAll T.|[ren (+1+i)] (TAll T.|[ren (+2+i)] (▶: T.|[ren (+3+i)])), 0.
Proof.
  rewrite /= -/IFTBody => HsT1.
  move: (HsT1) => /is_unstamped_ren1_ty HsT2; rewrite -hrenS in HsT2.
  move: (HsT2) => /is_unstamped_ren1_ty HsT3; rewrite -hrenS in HsT3.
  move: (HsT3) => /is_unstamped_ren1_ty HsT4; rewrite -hrenS in HsT4.
  tcrush; rewrite ?iterate_S ?iterate_0 /=; tcrush;
    first [eapply LSel_stp', (path_tp_weaken (i := 0)) |
      eapply SelU_stp, (path_tp_weaken (i := 0))];
       try (typconstructor; apply: Var_typed');
    rewrite ?hsubst_id //; try autosubst; wtcrush.
Qed.

Lemma tyAppIFT_typed Γ T t :
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ t : IFT →
  Γ u⊢ₜ tyApp t "A" T : T →: T →: ▶: T.
Proof.
  move => HsT1 Ht; move: (HsT1) => /is_unstamped_ren1_ty HsT2.
  intros; eapply tyApp_typed => //; last stcrush.
  intros; rewrite /= !(hren_upn_gen 1) !(hren_upn_gen 2) /up /=.
  exact: (subIFT 1).
Qed.

(** Adds a skip needed for booleans. *)
(* Beware: we could inline the [lett t], but then we'd need to use a weakening lemma
to prove [iftCoerce_typed]. *)
Definition iftCoerce t :=
  lett t (vabs' (vabs' (tskip (tapp (tapp (tv x2) (tv x1)) (tv x0))))).

Lemma iftCoerce_typed Γ t T :
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ t: T →: T →: ▶: T →
  Γ u⊢ₜ iftCoerce t : T →: T →: T.
Proof.
  move => HsT1 Ht.
  move: (HsT1) => /is_unstamped_ren1_ty HsT2.
  move: (HsT2) => /is_unstamped_ren1_ty; rewrite -hrenS => HsT3.
  move: (HsT3) => /is_unstamped_ren1_ty; rewrite -hrenS => HsT4.
  eapply Let_typed; [exact: Ht| |rewrite /= !(hren_upn 1); tcrush].
  rewrite /= !(hren_upn_gen 1) (hren_upn_gen 2) /=.
  tcrush; rewrite -!hrenS -(iterate_S tskip 0).
  eapply (Subs_typed (T1 := ▶:T.|[_])); first tcrush.
  repeat (eapply App_typed; last var).
  apply: Var_typed' => //.
  rewrite /= !(hren_upn 1) (hren_upn_gen 1) (hren_upn_gen 2)
    !hsubst_comp !ren_ren_comp /=. done.
Qed.

Lemma iftCoerce_tyAppIFT_typed Γ T t :
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ t : IFT →
  Γ u⊢ₜ iftCoerce (tyApp t "A" T) : T →: T →: T.
Proof. intros. by apply /iftCoerce_typed /tyAppIFT_typed. Qed.

Lemma iftCoerce_tyAppIFT_typed_IFT Γ t :
  Γ u⊢ₜ t : IFT →
  Γ u⊢ₜ iftCoerce (tyApp t "A" IFT) : IFT →: IFT →: IFT.
Proof. intros. apply iftCoerce_tyAppIFT_typed; tcrush. Qed.

Definition iftNotBody t T true false :=
  tapp (tapp
      (iftCoerce (tyApp t "A" T))
    false)
  true.

(* XXX Beware that false and true are inlined here. *)
Lemma iftNotBodyTyp Γ t :
  Γ u⊢ₜ t : IFT →
  Γ u⊢ₜ iftNotBody t IFT (tv iftTrue) (tv iftFalse) : IFT.
Proof.
  intros.
  eapply App_typed; last exact: iftTrueTyp.
  eapply App_typed; last exact: iftFalseTyp.
  exact: iftCoerce_tyAppIFT_typed_IFT.
Qed.

(* We'd want NOT = λ a. a False True. *)
(* This is NOT0 = λ a. a (λ t f. f) (λ t f. t). *)
Definition iftNot0 := vabs' (iftNotBody (tv x0) IFT (tv iftTrue) (tv iftFalse)).
Lemma iftNotTyp Γ T :
  Γ u⊢ₜ iftNot0 : TAll IFT IFT.
Proof. apply Lam_typed; first stcrush. apply iftNotBodyTyp. var. Qed.

(* AND = λ a b. a b False. *)
Definition iftAndBody t1 t2 T false :=
  tapp (tapp
      (iftCoerce (tyApp t1 "A" T))
    t2)
  false.

Lemma iftAndBodyTyp Γ t1 t2 :
  Γ u⊢ₜ t1 : IFT →
  Γ u⊢ₜ t2 : IFT →
  Γ u⊢ₜ iftAndBody t1 t2 IFT (tv iftFalse) : IFT.
Proof.
  intros Ht1 Ht2.
  eapply App_typed; last exact: iftFalseTyp.
  eapply App_typed; last exact: Ht2.
  exact: iftCoerce_tyAppIFT_typed_IFT.
Qed.

Lemma iftAndTyp Γ T :
  Γ u⊢ₜ vabs' (vabs' (iftAndBody (tv x1) (tv x0) IFT (tv iftFalse))) : IFT →: IFT →: IFT.
Proof. tcrush. apply iftAndBodyTyp; var. Qed.

(*
let bool = boolImplV :
  μ { Boolean: IFT..IFT; true : b.Boolean; false : b.Boolean;
      and : p.Boolean →: p.Boolean →: p.Boolean }
*)

Definition IFTp0 : ty := p0Bool →: p0Bool →: p0Bool.

Lemma iftCoerce_tyAppIFT_typed_p0Boolean Γ T t :
  T :: Γ u⊢ₜ t : IFT →
  T :: Γ u⊢ₜ iftCoerce (tyApp t "A" p0Bool) : p0Bool →: p0Bool →: p0Bool.
Proof. intros. apply iftCoerce_tyAppIFT_typed; tcrush. Qed.

Import hoasNotation.

(* Not typeable *)
Definition hcircular_init : hvl := ν: x, {@
  val "v" = hpv x @ "v"
}.

Lemma circular_init_typed Γ : Γ u⊢ₜ hclose (htv hcircular_init) : hclose (μ: x, {@ val "v" : ⊤}).
Proof. tcrush; cbv; hideCtx. varsub. asideLaters. ltcrush. Abort.

Definition hcircular_init2 : hvl := ν: x, {@
  val "v" = hpv x
}.

Lemma circular_init_typed Γ : Γ u⊢ₜ hclose (htv hcircular_init2) : hclose (μ: x, {@ val "v" : ⊤}).
Proof. tcrush; cbv; hideCtx. varsub. ltcrush. Qed.
