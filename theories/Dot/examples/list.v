From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn unstampedness_binding.
From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived.
From D.Dot.examples Require Import exampleInfra scalaLib hoas.

(* Import DBNotation. *)
Import hoasNotation.

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
  apply (Subs_typed (T1 := hclose (▶ hpx (length Γ'') @; "Boolean"))%ty);
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

Definition hlistModTBody bool sci : hty := {@
  type "List" >: ⊥ <: hlistTBody bool sci;
  val "nil" : hnilT sci;
  val "cons" : hconsT sci
}.
Definition hlistModT bool : hty := μ: sci, hlistModTBody bool sci.
(* XXX deprecated. *)
Definition hlistT := hlistModT.

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
    have := trueTyp Γ [hclose ⊤; T; L]%ty.
    have := loopTyp (hclose ⊤ :: T :: L :: boolImplT :: Γ)%ty.
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

Infix "$:" := htapp (at level 68, left associativity).
Definition hpackTV l T := ν: self, {@ type l = T }.
Definition htyApp l t T :=
  hlett t (λ x, hlett (htv (hpackTV l T)) (λ a, htv x $: htv a)).

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
  (Ht : hclose (hlistT hx1) :: boolImplT :: Γ u⊢ₜ (body (hxm 1) (hxm 2)) 2 : shift (shift T)) :
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

Notation "a @: b" := (htproj a b) (at level 59, b at next level).
Definition hheadCons (bool list : hvl) :=
  htskip (htproj (htskip
    (htyApp "T" (htv list @: "cons") 𝐍
      $: htv (hvnat 0)
      $: (htv list @: "nil"))) "head" $: htv (hvnat 0)).
(* Invoking a method from an abstract type (here, [list @; "List"] needs a skip. *)

Ltac ttrans := eapply Trans_stp.

Example hheadConsTypFake Γ :
  hclose (hlistT hx1) :: boolImplT :: Γ u⊢ₜ (hheadCons (hxm 1) (hxm 2)) 2 : hclose 𝐍.
Admitted.

Example clListTypNat3 Γ :
  Γ u⊢ₜ hclose (clListV'2 hheadCons): hclose 𝐍.
Proof. apply clListTyp'2, hheadConsTypFake. Qed.

Example hheadConsTyp Γ :
  hclose (hlistT hx1) :: boolImplT :: Γ u⊢ₜ (hheadCons (hxm 1) (hxm 2)) 2 : hclose 𝐍.
Proof.
  match goal with
    |- ?Γ u⊢ₜ _ : _ =>
    have HL : Γ u⊢ₜ tv (ids 0): hclose (hlistModTBody hx1 hx0) by apply: TMuE_typed'; first var
  end.

  tcrush.
  Import hterm_lifting.
  Arguments hlistTBody /.
  Arguments hconsT /.
  (* rewrite /hlistT ![hclose _]/= /liftBind. *)

  eapply (Subs_typed (i := 1) (T1 := hclose (▶ 𝐍))). tcrush.
  eapply (App_typed (T1 := hclose ⊤)); last (eapply Subs_typed_nocoerce; tcrush).
  tcrush.
(* (hp1 @; "A"). *)
  apply (Subs_typed_nocoerce (hclose (hlistTBodyGen hx1 hx0 ⊥ 𝐍))); first last.
  (* apply (Subs_typed (T1 := hclose (hlistTBodyGen hx1 hx0 ⊥ 𝐍))). *)
  (* cbv. hideCtx. *)
  {
    (* ttrans; last apply TLaterL_stp; stcrush. *)
    apply Bind1; tcrush.
    do 2 lNext.
    lThis.
    (* eapply Trans_stp; first apply TAnd1_stp; stcrush.
    (* Import DBNotation.
    cbv. *)
    (* asideLaters. *)
    tcrush. *)
    eapply SelU_stp. tcrush. varsub.
    lThis.
  }
  hideCtx.
  (* have ? : Γ0 u⊢ₜ tv (ids 0): hclose (hlistT hx1) by var. *)

  have Ht: shiftN 1 (hclose (hlistT hx0)) :: boolImplT :: Γ u⊢ₜ
    (htyApp "T" (htv (hxm 2) @: "cons") 𝐍 $: htv (hvnat 0) $: htv (hxm 2) @: "nil") 2 :
    hclose (hTAnd (hpx 0 @; "List") (type "A" >: ⊥ <: ▶ 𝐍)).
  eapply (App_typed (T1 := hclose (hnilT hx0))); first last. {
    tcrush.
    (* eapply TMuE_typed' with (T1 := hclose (val "nil" : hTAnd (▶ hp0 @; "List") (type "A" >: ⊥ <: ⊥))); last done.
    varsub. apply Mu_stp_mu; tcrush.
    lNext. *)
    eapply Subs_typed_nocoerce; [ exact: HL | lNext ].
  }

  eapply (App_typed (T1 := hclose 𝐍)); last tcrush. {
  (* Perform avoidance on the type application. Argh. *)
  eapply (tyApp_typed) with (T := hclose 𝐍)
    (U := shiftN 1 (TAll (hclose (hp0 @; "T")) ((TAll (hclose (hnilT hx1))
      (hclose (hTAnd (hp0 @; "List") (type "A" >: ⊥ <: ▶ 𝐍))))))).
    3,4: intros; tcrush.
    1: intros; tcrush.
    all: intros; tcrush.
    eapply Subs_typed_nocoerce; first exact: HL.
    lNext.
    lNext. {
    Import DBNotation.
    lThis; cbv.
    }
    cbv.

    Import DBNotation. hideCtx.
    ttrans; first apply TAnd1_stp; stcrush.
    cbv.
    tcrush.
    lThis.
    (* typconstructor.
    typconstructor. *)
    Timeout 1 asimpl.
    cbv.
     first eapply App_typed; first last. {
    }
    - eapply (tyApp_typed) with (T := hclose 𝐍).
    cbv.
  cbv.
  Import DBNotation.
  hideCtx.


  (* apply (Subs_typed_nocoerce (TAnd (TSel (pv (ids 0)) "List") (TTMem "A" TBot TNat))). *)
  rewrite [htskip _ _]/= -(iterate_S tskip 0).

  apply (Subs_typed (T1 := (TSel (pv (ids 0)) "List"))).
  (* apply (Subs_typed (T1 := TAnd (TSel (pv (ids 0)) "List") (TTMem "A" TBot TNat))). *)
  tcrush.
  {
    eapply Trans_stp.
    {
      (* Argh. XXX *)
      eapply SelU_stp with (L := hclose ⊥%ty) (U := hclose (hlistTBody (hx 1) (λ _, var_vl 2))%ty); tcrush.
      eapply TMuE_typed' with (T1 := hclose (type "List" >: ⊥ <: (hlistTBody hx2 hx0))%ty); last done.
      varsub; apply Mu_stp_mu; tcrush.
    }
    Import DBNotation.
    lazy.
    asideLaters.
    apply Bind1; stcrush.
    do 2 lNext.
    lThis.
    cbv.
    hideCtx.

    lNext.
    time cbv.
    tcrush.
  (* rewrite /hlistT. ![hclose _]/= /liftBind. *)
    cbv.
    first eapply Var_typed_sub. done.
    rewrite hsubst_id /=.
    3: done.
    by [rewrite lookup_app_r ?Nat.sub_diag|].
    varsub.
    eapply TMuE_typed'.
    last done.
    lazy.
    varsub.
    lazy.
    apply Bind1; stcrush.
    rewrite iterate_0.
    lazy.
    lThis.
    asideLaters.
    eapply AddI_stp. hvar_vl.
    hideCtx.

    3: lThis. stcrush.
  lNext.
  eapply (Subs_typed_nocoerce (TSel (ids 0) "List")); first last.
  eapply App_typed; tcrush.

  2: {
    varsub.
  }
  econstructor.
  tcrush.
Print hbody.



(* Try recursive linking? *)
