From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn unstampedness_binding.
From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived.
From D.Dot.examples Require Import exampleInfra scalaLib hoas.

Import DBNotation hoasNotation.

Implicit Types (L T U: hty) (Γ : list ty).
 (* (v: vl) (e: tm) (d: dm) (ds: dms) . *)

Definition htrueTm bool := htskip (htproj (htv bool) "true").
Definition hfalseTm bool := htskip (htproj (htv bool) "false").

(* bool : boolImplT *)
(* Let Γ' := boolImplT :: Γ. *)

Lemma trueTyp Γ Γ'' : Γ'' ++ boolImplT :: Γ u⊢ₜ
  hclose (htrueTm (hx (length Γ''))) : hclose (hpx (length Γ'') @; "Boolean").
Proof.
  have ?: length Γ'' < length (Γ'' ++ boolImplT :: Γ) by rewrite app_length /=; lia.
  rewrite /htrueTm/= -(iterate_S tskip 0).
  apply (Subs_typed (T1 := hclose (▶ hpx (length Γ'') @; "Boolean")));
    rewrite /= plusnO; tcrush.
    eapply Subs_typed_nocoerce.
  - eapply TMuE_typed'; first eapply Var_typed'; by [rewrite lookup_app_r ?Nat.sub_diag|].
  - repeat lNext.
Qed.

Lemma falseTyp Γ Γ'' : Γ'' ++ boolImplT :: Γ u⊢ₜ
  hclose (hfalseTm (hx (length Γ''))) : hclose (hpx (length Γ'') @; "Boolean").
Proof.
  have ?: length Γ'' < length (Γ'' ++ boolImplT :: Γ) by rewrite app_length /=; lia.
  rewrite /hfalseTm /= -(iterate_S tskip 0).
  apply (Subs_typed (T1 := hclose (▶ hpx (length Γ'') @; "Boolean")));
    rewrite /= plusnO; tcrush.
  eapply Subs_typed_nocoerce.
  - eapply TMuE_typed'; first eapply Var_typed'; by [rewrite lookup_app_r ?Nat.sub_diag|].
  -
    (* Optional tactic, just for seeing what happens: *)
    lNext; rewrite -(decomp_s _ (ids _ .: ren _)) /=.
    (* Needed: *)
    repeat lNext.
Qed.

Definition hnilV bool : hvl := ν: self, {@
  type "A" = ⊥;
  val "isEmpty" = λ: _, htrueTm bool;
  val "head" = λ: _, pureS loopTm;
  val "tail" = λ: _, pureS loopTm
}.

(*
  λ(x: {A})λ(hd: x.A)λ(tl: sci.List∧{A <: x.A}) let result = ν(self) {
    A = x.A; isEmpty = bool.false; head = hd; tail = tl } in result *)
Program Definition hconsV bool : hvl :=
  λ: x, λ:: hd tl, htv $ ν: self, {@
    type "A" = hpv x @; "T";
    val "isEmpty" = λ: _, hfalseTm bool;
    val "head" = λ: _, htv hd;
    val "tail" = λ: _, htv tl
  }.

Definition hlistTBodyGen bool sci (L U : hty) : hty := μ: self, {@
  type "A" >: L <: U;
  val "isEmpty" : ⊤ →: hpv bool @; "Boolean";
  val "head" : ⊤ →: hpv self @; "A";
  val "tail" : ⊤ →: hTAnd (hpv sci @; "List") (type "A" >: ⊥ <: hpv self @; "A" )
}.

Definition hlistTBody bool sci := hlistTBodyGen bool sci ⊥ ⊤.

Definition hlistV bool : hvl := ν: self, {@
  type "List" = hlistTBody bool self;
  val "nil" = hnilV bool;
  val "cons" = hconsV bool
}.

Definition hnilT sci := hTAnd (▶ hpv sci @; "List") (typeEq "A" ⊥).

(** ∀(x: {A})∀(hd: x.A)∀(tl: sci.List∧{A <: x.A})sci.List∧{A <: x.A} *)
Definition hconsT sci : hty :=
  ∀: x : (tparam "T"),
    hpv x @; "T" →:
    (hTAnd (hpv sci @; "List") (type "A" >: ⊥ <: hpv x @; "T")) →:
    hTAnd (hpv sci @; "List") (type "A" >: ⊥ <: hpv x @; "T").

Definition hlistT bool : hty := μ: sci, {@
  type "List" >: ⊥ <: hlistTBody bool sci;
  val "nil" : hnilT sci;
  val "cons" : hconsT sci
}.

Definition hconsTResConcr bool sci U := hlistTBodyGen bool sci U U.

Definition hconsTConcr bool sci : hterm ty :=
  ∀: x: tparam "T",
    hpv x @; "T" →:
      hTAnd (hpv sci @; "List") (type "A" >: ⊥ <: hpv x @; "T") →:
      (hconsTResConcr bool sci (hpv x @; "T")).

Definition hlistTConcrBody bool sci : hty := {@
  typeEq "List" $ hlistTBody bool sci;
  val "nil" : hnilT sci;
  val "cons" : hconsTConcr bool sci
}.

Definition hlistTConcr bool : hty := μ: sci, hlistTConcrBody bool sci.

Definition hnilTConcr bool sci : hty := hlistTBodyGen bool sci ⊥ ⊥.

Example nilTyp Γ : hclose (▶ hlistTConcrBody hx1 hx0) :: boolImplT :: Γ u⊢ₜ
  hclose (htv (hnilV hx1)) : hclose (hnilT hx0).
Proof.
  apply (Subs_typed_nocoerce $ hclose $ hnilTConcr hx1 hx0).
  - evar (T : ty).
    set L :=  hclose (▶ hlistTConcrBody hx1 hx0).
    have := trueTyp Γ [hclose ⊤; T; L].
    have := loopTyp (hclose ⊤ :: T :: L :: boolImplT :: Γ).
    rewrite {}/T/= => Ht Hl.
    tcrush; apply (Subs_typed_nocoerce (hclose ⊥)); cbn; tcrush.
  - tcrush; last (apply Bind1; tcrush).
    ettrans; first eapply TAddLater_stp; stcrush.
    asideLaters.
    eapply LSel_stp'; tcrush. varsub.
    asideLaters.
    lThis. lThis.
Qed.

Example consTyp Γ : hclose (▶ hlistTConcrBody hx1 hx0) :: boolImplT :: Γ u⊢ₜ
  hclose (htv (hconsV hx1)) : hclose (hconsTConcr hx1 hx0).
Proof.
  epose proof falseTyp Γ [_; _; _; _; _; _] as Ht; cbn in Ht.
  tcrush; clear Ht; first by varsub; eapply (LSel_stp' _ (hclose (hp4 @; "T"))); tcrush; varsub; lThis.
  hideCtx. varsub. tcrush. lNext.
  eapply LSel_stp'; tcrush. varsub. lThis.
Qed.

Lemma consTSub Γ : hclose (hlistTConcrBody hx1 hx0) :: boolImplT :: Γ u⊢ₜ
  hclose (hconsTConcr hx1 hx0), 0 <: hclose (hconsT hx0), 0.
Proof.
  tcrush; rewrite !iterate_S !iterate_0; hideCtx.
  eapply LSel_stp'; tcrush. varsub. tcrush. lThis.
  by lThis.
  apply Bind1; stcrush. by lThis.
Qed.

Example listTypConcr Γ : boolImplT :: Γ u⊢ₜ hclose (htv (hlistV hx0)) : hclose (hlistTConcr hx0).
Proof.
  have Hn := nilTyp Γ.
  (* Without the call to [dvl_typed], Coq would (smartly) default to [dvabs_typed] *)
  have := consTyp Γ => /(dvl_typed "cons") Hc /=.
  tcrush.
Qed.

Example listTyp Γ : boolImplT :: Γ u⊢ₜ hclose (htv (hlistV hx0)) : hclose (hlistT hx0).
Proof.
  have Hv := listTypConcr Γ.
  have Hsub := consTSub Γ.
  eapply Subs_typed_nocoerce; first exact Hv; tcrush.
  lThis.
  lNext.
  do 2 lNext; lThis.
Qed.


(** Link lists with booleans. *)

(* Naive attempt; this fails avoidance. *)
(*
Definition clListV := lett (tv boolImpl) (tv listV).
Example clListTyp Γ : Γ u⊢ₜ clListV : listT.
  eapply Let_typed. apply boolImplTyp.
  Fail change (shift listT) with (listT).
  Fail apply listTyp.
Abort. *)
Definition hvabs' x := htv (hvabs x).
Definition hlett t u := htapp (hvabs' u) t.
Arguments hvabs' /.
Arguments hlett /.
(* Notation "hlett: x := t in u" := (htapp (λ: x, u) t) (at level 200). *)

(* Try1, working well? *)
Definition clListV' body := hlett (htv (pureS boolImpl)) (λ bool, hlett (htv (hlistV bool)) (λ list, pureS body)).
Example clListTyp' Γ (T : ty) body
  (Ht : shift (hclose (hlistT hx0)) :: boolImplT :: Γ u⊢ₜ body : shift (shift T)) :
  Γ u⊢ₜ hclose (clListV' body) : T.
Proof.
  eapply Let_typed; first apply boolImplTyp.
  eapply Let_typed; first apply listTyp.
  all: tcrush.
Qed.

Example clListTypNat Γ :
  Γ u⊢ₜ hclose (clListV' (hclose (htv (hvnat 1)))) : hclose 𝐍.
Proof. apply clListTyp'. tcrush. Qed.



(* Try2. Try taking a HOAS body. Works less well. *)

(* Argh. Variable by de Bruijn level. Not good. *)
Definition hxm i : hvl := λ j, var_vl (j - i).
Definition hxm' i : hvl := ren (λ j, j - i).
Goal hxm = hxm'. done. Qed.

Definition clListV'2 body := hlett (htv (pureS boolImpl)) (λ bool, hlett (htv (hlistV bool)) (λ list, body bool list)).
(* Definition clListV' body := hlett: bool := (htv (pureS boolImpl)), hlett (htv (hlistV bool)) body. *)
Example clListTyp'2 Γ (T : ty) body
  (* (Ht : hclose (hlistT hx1) :: boolImplT :: Γ u⊢ₜ hclose (body hx1 hx0) : shift (shift T)) : *)
  (Ht : shift (hclose (hlistT hx0)) :: boolImplT :: Γ u⊢ₜ (body (hxm 1) (hxm 2)) 2 : shift (shift T)) :
  (* (Ht : shift (hclose (hlistT hx0)) :: boolImplT :: Γ u⊢ₜ hclose (body (hx (-1)) (hx (-2)) 2 : shift (shift T)) : *)
  Γ u⊢ₜ hclose (clListV'2 body) : T.
Proof.
  eapply Let_typed; first apply boolImplTyp.
  eapply Let_typed; first apply listTyp.
  all: tcrush.
Qed.

Example clListTypNat2 Γ :
  Γ u⊢ₜ hclose (clListV'2 (λ _ _, htv (hvnat 1))) : hclose 𝐍.
Proof. apply clListTyp'2. tcrush. Qed.

(* Try recursive linking? *)
