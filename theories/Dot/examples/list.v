From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra unstampedness_binding scalaLib.
From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section listLib.

Definition trueTm := tskip (tproj (tv x0) "true").
Definition falseTm := tskip (tproj (tv x0) "false").

Context Γ.
(* bool : boolImplT *)
Let Γ' := boolImplT :: Γ.

Lemma trueTyp Γ'' : Γ'' ++ Γ' u⊢ₜ trueTm.|[ren (+length Γ'')] : p0.|[ren (+length Γ'')] @; "Boolean".
Proof.
  have ?: length Γ'' < length (Γ'' ++ Γ') by rewrite app_length /Γ'/=; lia.
  rewrite /trueTm /= -(iterate_S tskip 0).
  apply (Subs_typed (T1 := ▶ pv (ids (length Γ'')) @; "Boolean"));
    rewrite plusnO; tcrush.
  eapply Subs_typed_nocoerce.
  - eapply TMuE_typed'; first eapply Var_typed'; by [rewrite lookup_app_r ?Nat.sub_diag|].
  - repeat lNext.
Qed.

Lemma falseTyp Γ'' : Γ'' ++ Γ' u⊢ₜ falseTm.|[ren (+length Γ'')] : p0.|[ren (+length Γ'')] @; "Boolean".
Proof.
  have ?: length Γ'' < length (Γ'' ++ Γ') by rewrite app_length /Γ'/=; lia.
  rewrite /falseTm /= -(iterate_S tskip 0).
  apply (Subs_typed (T1 := ▶ pv (ids (length Γ'')) @; "Boolean"));
    rewrite plusnO; tcrush.
  eapply Subs_typed_nocoerce.
  - eapply TMuE_typed'; first eapply Var_typed'; by [rewrite lookup_app_r ?Nat.sub_diag|].
  -
    (* Optional tactic, just for seeing what happens: *)
    lNext; rewrite -(decomp_s _ (ids _ .: ren _)) /=.
    (* Needed: *)
    repeat lNext.
Qed.


Definition nilV : vl := ν {@ (* self => *)
  type "A" = ⊥;
  val "isEmpty" = vabs (* d => *) (trueTm.|[ren (+2)]); (* for self and d *)
  val "head" = vabs loopTm;
  val "tail" = vabs loopTm
}.

(*
  λ(x: {A})λ(hd: x.A)λ(tl: sci.List∧{A <: x.A}) let result = ν(self) {
    A = x.A; isEmpty = bool.false; head = hd; tail = tl } in result *)
Definition consV : vl :=
  vabs (* x => *) $ vabs' (* hd => *) $ vabs' (* tl => *) $ tv $ ν {@ (* self => *)
    type "A" = p3 @; "T";
    val "isEmpty" = vabs (* d => *) falseTm.|[ren (+5)];
    val "head" = vabs (* d => *) (tv x3);
    val "tail" = vabs (* d => *) (tv x2)
  }.

Definition listTBodyGen L U := μ {@ (* self => *)
  type "A" >: shift L <: shift U;
  val "isEmpty" : ⊤ →: p2 @; "Boolean"; (* bool.Boolean *)
  val "head" : ⊤ →: p0 @; "A"; (* self.A *)
  val "tail" : ⊤ →: TAnd (p1 @; "List") (type "A" >: ⊥ <: p0 @; "A" )
}.

Definition listTBody := listTBodyGen ⊥ ⊤.

Definition listV : vl := ν {@ (* sci => *)
  type "List" = listTBody; (* [shift] is for [sci] *)
  val "nil" = shiftV nilV;
  val "cons" = shiftV consV
}.

Definition nilT := TAnd listTBody (typeEq "A" ⊥).

(** ∀(x: {A})∀(hd: x.A)∀(tl: sci.List∧{A <: x.A})sci.List∧{A <: x.A} *)
Definition consT sci : ty :=
  TAll (tparam "T")
    (p0 @; "T" →:
    (TAnd (shift sci @; "List") (type "A" >: ⊥ <: p0 @; "T")) →:
    TAnd (shift sci @; "List") (type "A" >: ⊥ <: p0 @; "T")).

Definition listT : ty := μ {@ (* sci => *)
  type "List" >: ⊥ <: listTBody; (* [shift] is for [sci] *)
  val "nil" : nilT;
  val "cons" : consT p0
}.

Definition consTResConcr U : ty := listTBodyGen U U.
Definition consTConcr sci : ty :=
  TAll (tparam "T")
    (p0 @; "T" →:
      TAnd (shift sci @; "List") (type "A" >: ⊥ <: p0 @; "T") →:
      (* This renaming is needed because I'm inserting a local variable that isn't expected by
      [consTResConcr] *and I'm using it in the argument*. I could also just clone *)
      (consTResConcr (p2 @; "T")).|[ids 1 .: ids 2 .: ids 0 .: ids]).

      (* (consTResConcr (p2 @; "T")).|[∞ [ids 1 ; ids 2 ; ids 0]]). *)
Definition listTConcrBody : ty := {@ (* sci => *)
  typeEq "List" $ listTBody; (* [shift] is for [sci] *)
  val "nil" : nilT;
  val "cons" : consTConcr p0
}.

Definition listTConcr : ty := μ listTConcrBody.

Definition nilTConcr : ty := listTBodyGen ⊥ ⊥.

Example nilTyp : (▶ listTConcrBody)%ty :: Γ' u⊢ₜ shift (tv nilV) : nilT.
Proof.
  apply (Subs_typed_nocoerce nilTConcr).
  - evar (T : ty).
    have := trueTyp [⊤; T; ▶ listTConcrBody]%ty.
    have := loopTyp (⊤ :: T :: ▶ listTConcrBody :: Γ')%ty.
    rewrite {}/T/= => Ht Hl.
    tcrush; apply (Subs_typed_nocoerce ⊥); tcrush.
  - tcrush.
    lThis.
    apply Bind1; tcrush.
Qed.

Example consTyp :
  (▶ listTConcrBody)%ty :: Γ' u⊢ₜ shift (tv consV) : consTConcr p0.
Proof.
  epose proof falseTyp [_; _; _; _; _; _] as Ht; cbn in Ht.
  tcrush; clear Ht; first by varsub; eapply (LSel_stp' _ (p4 @; "T")); tcrush; varsub; lThis.
  hideCtx. varsub. cbn. tcrush. lNext.
  eapply LSel_stp'; tcrush. varsub. lThis.
Qed.

Lemma consTSub : listTConcrBody :: Γ' u⊢ₜ consTConcr p0, 0 <: consT p0, 0.
Proof.
  tcrush; rewrite !iterate_S !iterate_0; hideCtx.
  eapply LSel_stp'; tcrush. varsub. tcrush. lThis.
  by lThis.
  apply Bind1; stcrush. by lThis.
Qed.

Example listTypConcr : Γ' u⊢ₜ tv listV : listTConcr.
Proof.
  have := nilTyp => *.
  (* Without the call to [dvl_typed], Coq would (smartly) default to [dvabs_typed] *)
  have := consTyp => /(dvl_typed "cons") *.
  tcrush.
Qed.

Example listTyp : Γ' u⊢ₜ tv listV : listT.
Proof.
  have Hv := listTypConcr.
  have Hsub := consTSub.
  apply (Subs_typed_nocoerce listTConcr); tcrush.
  lThis.
  lNext.
  do 2 lNext; lThis.
Qed.

End listLib.
