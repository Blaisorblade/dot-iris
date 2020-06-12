(**
WIP examples constructing _unstamped_ syntactic typing derivations.
 *)

From D Require Import tactics.
From D.Dot Require Import syn unstampedness_binding.
From D.Dot Require Import old_unstamped_typing old_unstamped_typing_derived_rules.
From D.Dot Require Import ex_utils hoas scala_lib.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Import DBNotation.

Example ex0 e Γ T:
  Γ u⊢ₜ e : T →
  Γ u⊢ₜ e : ⊤.
Proof. intros. apply (iT_ISub_nocoerce T TTop); tcrush. Qed.

Example ex1 Γ (n : Z) T:
  Γ u⊢ₜ ν {@ val "a" = n} : μ {@ val "a" : TInt }.
Proof.
  (* Help proof search: Avoid trying iT_Mu_I, that's slow. *)
  apply iT_Obj_I; tcrush.
Qed.

Example ex2 Γ T :
  Γ u⊢ₜ ν {@ type "A" = x0 @; "B" } : TMu (TAnd (TTMem "A" TBot TTop) TTop).
Proof. apply iT_Obj_I; tcrush. Qed.

(* Try out fixpoints. *)
Definition F3 T :=
  TMu (TAnd (TTMemL "A" T T) TTop).

Example ex3 Γ T:
  Γ u⊢ₜ ν {@ type "A" = F3 (x0 @; "A") } : F3 (F3 (TSel x0 "A")).
Proof. apply iT_Obj_I; tcrush. Qed.

Definition KeysT : ty := μ {@
  type "Key" >: ⊥ <: ⊤;
  val "key": HashableString →: x0 @; "Key"
}.
Definition hashKeys : vl := ν {@
  type "Key" = TInt;
  val "key" = vabs (tapp (tproj x0 "hashCode") tUnit)
}.

Definition KeysTConcr := μ {@
  type "Key" >: TInt <: ⊤;
  val "key" : HashableString →: x0 @; "Key"
}.

(* IDEA for our work: use [(type "Key" >: TInt <: ⊤) ⩓ (type "Key" >: ⊥ <: ⊤)]. *)
Example hashKeys_typed Γ:
  Γ u⊢ₜ hashKeys : KeysT.
Proof.
  apply (iT_ISub_nocoerce KeysTConcr); first last. {
    apply iMu_Sub_Mu; last stcrush.
    tcrush.
    lThis.
  }
  tcrush.
  apply iT_All_E with (T1 := TUnit);
    last eapply (iT_ISub_nocoerce TInt); tcrush.

  apply (iT_ISub_nocoerce (val "hashCode" : ⊤ →: 𝐙)).
  by eapply iT_ISub_nocoerce; [eapply iT_Mu_E'; by [var||stcrush] | tcrush].
  tcrush.
  eapply iSub_Sel', (path_tp_delay (i := 0)); wtcrush.
  varsub; tcrush.
Qed.

(* We can also use subtyping on the individual members to type this example. *)
Definition boolImplT0 : ty :=
  μ {@
    typeEq "Boolean" hIFT;
    val "true" : TLater p0Bool;
    val "false" : TLater p0Bool
  }.

Example boolImplTypAlt Γ :
  Γ u⊢ₜ boolImplV : boolImplT.
Proof.
  apply (iT_ISub_nocoerce boolImplT0);
    last (tcrush; lThis).
  tcrush.
  - eapply iT_ISub_nocoerce; [apply iftTrueTyp|apply SubIFT_LaterP0Bool].
  - eapply iT_ISub_nocoerce; [apply iftFalseTyp|apply SubIFT_LaterP0Bool].
Qed.

(* Utilities needed for not. *)
Lemma subIFT i Γ T:
  (typeEq "A" T.|[ren (+1+i)]) :: Γ u⊢ₜ IFTBody, 0 <:
    TAll T.|[ren (+1+i)] (TAll T.|[ren (+2+i)] (▶: T.|[ren (+3+i)])), 0.
Proof.
  rewrite /= -/IFTBody.
  tcrush; rewrite ?iterate_S ?iterate_0 /=; tcrush;
    first [eapply iSub_Sel', (path_tp_delay (i := 0)) |
      eapply iSel_Sub, (path_tp_delay (i := 0))];
       try (typconstructor; apply: iT_Var');
    rewrite ?hsubst_id //; try autosubst; wtcrush.
Qed.

Lemma tyAppIFT_typed Γ T t :
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ t : hIFT →
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
  lett t (vabs (vabs (tskip (x2 $: x1 $: x0)))).

Lemma iftCoerce_typed Γ t T :
  Γ u⊢ₜ t: T →: T →: ▶: T →
  Γ u⊢ₜ iftCoerce t : T →: T →: T.
Proof.
  move => Ht.
  eapply iT_Let; [exact: Ht|rewrite /= !(hren_upn 1); tcrush].
  rewrite /= (hren_upn_gen 2) /=.
  tcrush; rewrite -!hrenS -(iterate_S tskip 0).
  eapply (iT_ISub (T1 := ▶:T.|[_])); first tcrush.
  repeat (eapply iT_All_E; last var).
  apply: iT_Var' => //.
  rewrite /= !(hren_upn 1) (hren_upn_gen 1) (hren_upn_gen 2)
    !hsubst_comp !ren_ren_comp /=. done.
Qed.

Lemma iftCoerce_tyAppIFT_typed Γ T t :
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₜ t : hIFT →
  Γ u⊢ₜ iftCoerce (tyApp t "A" T) : T →: T →: T.
Proof. intros. by apply /iftCoerce_typed /tyAppIFT_typed. Qed.

Lemma iftCoerce_tyAppIFT_typed_IFT Γ t :
  Γ u⊢ₜ t : hIFT →
  Γ u⊢ₜ iftCoerce (tyApp t "A" hIFT) : IFT →: IFT →: IFT.
Proof. intros. apply iftCoerce_tyAppIFT_typed; tcrush. Qed.

Definition iftNotBody t T true false :=
  iftCoerce (tyApp t "A" T) $: false $: true.

(* Beware that false and true are inlined here. *)
Lemma iftNotBodyTyp Γ t :
  Γ u⊢ₜ t : hIFT →
  Γ u⊢ₜ iftNotBody t hIFT hiftTrue hiftFalse : hIFT.
Proof.
  intros.
  eapply iT_All_E; last exact: iftTrueTyp.
  eapply iT_All_E; last exact: iftFalseTyp.
  exact: iftCoerce_tyAppIFT_typed_IFT.
Qed.

(* We'd want NOT = λ a. a False True. *)
(* This is NOT0 = λ a. a (λ t f. f) (λ t f. t). *)
Definition iftNot0 := vabs (iftNotBody x0 hIFT hiftTrue hiftFalse).
Lemma iftNotTyp Γ T :
  Γ u⊢ₜ iftNot0 : TAll hIFT hIFT.
Proof. apply iT_All_I; first stcrush. apply iftNotBodyTyp. var. Qed.

(* AND = λ a b. a b False. *)
Definition iftAndBody t1 t2 T false :=
  iftCoerce (tyApp t1 "A" T) $: t2 $: false.

Lemma iftAndBodyTyp Γ t1 t2 :
  Γ u⊢ₜ t1 : hIFT →
  Γ u⊢ₜ t2 : hIFT →
  Γ u⊢ₜ iftAndBody t1 t2 hIFT hiftFalse : hIFT.
Proof.
  intros Ht1 Ht2.
  eapply iT_All_E; last exact: iftFalseTyp.
  eapply iT_All_E; last exact: Ht2.
  exact: iftCoerce_tyAppIFT_typed_IFT.
Qed.

Lemma iftAndTyp Γ T :
  Γ u⊢ₜ vabs (vabs (iftAndBody x1 x0 hIFT hiftFalse)) : IFT →: IFT →: IFT.
Proof. tcrush. apply iftAndBodyTyp; var. Qed.

(*
let bool = boolImplV :
  μ { Boolean: IFT..IFT; true : b.Boolean; false : b.Boolean;
      and : p.Boolean →: p.Boolean →: p.Boolean }
*)

Definition IFTp0 : ty := p0Bool →: p0Bool →: p0Bool.

Lemma iftCoerce_tyAppIFT_typed_p0Boolean Γ T t :
  T :: Γ u⊢ₜ t : hIFT →
  T :: Γ u⊢ₜ iftCoerce (tyApp t "A" p0Bool) : p0Bool →: p0Bool →: p0Bool.
Proof. intros. apply iftCoerce_tyAppIFT_typed; tcrush. Qed.

Import hoasNotation.

(* Not typeable *)
Definition hcircular_init : hvl := ν: x, {@
  val "v" = x @ "v"
}.

Lemma circular_init_typed Γ : Γ u⊢ₜ hcircular_init : μ: x, {@ val "v" : ⊤}.
Proof. tcrush; cbv; hideCtx. varsub. asideLaters. ltcrush. Abort.

Definition hcircular_init2 : hvl := ν: x, {@
  val "v" = x
}.

Lemma circular_init_typed Γ : Γ u⊢ₜ hcircular_init2 : μ: x, {@ val "v" : ⊤}.
Proof. tcrush; cbv; hideCtx. varsub. ltcrush. Qed.
