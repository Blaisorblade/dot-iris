(** * Encoding covariant lists.

Here, the main lemma is [listTyp], saying that [hlistModV hx0] (the code shown
in the paper) has type [hlistModT hx0] in a context offering a boolean
implementation.
Subsequent examples demonstrate how to link lists with the boolean
implementation we provide, and how to _use_ lists.
 *)

From D Require Import tactics.
From D.Dot Require Import syn unstampedness_binding.
From D.Dot.typing Require Import unstamped_typing unstamped_typing_derived_rules.
From D.Dot.examples Require Import ex_utils scala_lib hoas.

Import DBNotation hoasNotation.

Implicit Types (L T U: hty) (Γ : list ty).
 (* (v: vl) (e: tm) (d: dm) (ds: dms) . *)

Definition htrueTm (bool : hvl) := htskip (bool @: "true").
Definition hfalseTm (bool : hvl) := htskip (bool @: "false").

(* bool : boolImplT *)
(* Let Γ' := boolImplT :: Γ. *)

Lemma trueTyp Γ Γ'' : Γ'' ++ boolImplT :: Γ u⊢ₜ
  htrueTm (hx (length Γ'')) : hpx (length Γ'') @; "Boolean".
Proof.
  have ?: length Γ'' < length (Γ'' ++ boolImplT :: Γ) by rewrite app_length /=; lia.
  apply (iT_Sub (i := 1) (T1 := ▶: hpx (length Γ'') @; "Boolean"));
    rewrite /= plusnO; tcrush.
    eapply iT_Sub_nocoerce.
  - eapply iT_Mu_E'; first eapply iT_Var'; try by [rewrite lookup_app_r ?Nat.sub_diag|]; stcrush.
  - ltcrush.
Qed.

Lemma falseTyp Γ Γ'' : Γ'' ++ boolImplT :: Γ u⊢ₜ
  hfalseTm (hx (length Γ'')) : hpx (length Γ'') @; "Boolean".
Proof.
  have ?: length Γ'' < length (Γ'' ++ boolImplT :: Γ) by rewrite app_length /=; lia.
  apply (iT_Sub (i := 1) (T1 := ▶: hpx (length Γ'') @; "Boolean"));
    rewrite /= plusnO; tcrush.
  eapply iT_Sub_nocoerce.
  - eapply iT_Mu_E'; first eapply iT_Var'; try by [rewrite lookup_app_r ?Nat.sub_diag|]; stcrush.
  - ltcrush.
Qed.

(** ** Interface of the list module. *)

(* [sci] stands for [scala.collection.immutable], following the example in WadlerFest DOT. *)
Definition hlistTGen (bool sci : hpath) L U : hty := μ: self, {@
  type "A" >: L <: U;
  val "isEmpty" : ⊤ →: bool @; "Boolean";
  val "head" : ⊤ →: self @; "A";
  val "tail" : ⊤ →: hTAnd (sci @; "List") (type "A" >: ⊥ <: self @; "A" )
}.

(** *** The list type itself. *)
Definition hlistT bool sci := hlistTGen bool sci ⊥ ⊤.

(** This ▶: Later is needed because
- [hnilT] types a value member "nil" (which can't use skips), and
- this value member has abstract type [sci @; "List"], and
- when we initialize "nil", [sci] has type [▶:(type "List" >: ... <: ...], so
  we can't deduce anything about [sci@;"List"], only something about
  [▶:(sci@; "List")]. *)
Definition hnilT sci := hTAnd (▶: sci @; "List") (typeEq "A" ⊥).

(** ∀(x: {A})∀(hd: x.A)∀(tl: sci.List∧{A <: x.A})sci.List∧{A <: x.A} *)
Definition hconsT sci : hty :=
  ∀: x : (tparam "T"),
    x @; "T" →:
    (hTAnd (sci @; "List") (type "A" >: ⊥ <: x @; "T")) →:
    hTAnd (sci @; "List") (type "A" >: ⊥ <: x @; "T").

(** mod stands for module. *)
Definition hlistModTBody bool sci : hty := {@
  type "List" >: ⊥ <: hlistT bool sci;
  val "nil" : hnilT sci;
  val "cons" : hconsT sci
}.
Definition hlistModT bool : hty := μ: sci, hlistModTBody bool sci.


(** ** Implementation of the list module. *)
Definition hnilV bool : hvl := ν: self, {@
  type "A" = ⊥;
  val "isEmpty" = λ: _, htrueTm bool;
  val "head" = λ: _, hloopTm;
  val "tail" = λ: _, hloopTm
}.

(*
  λ(x: {A})λ(hd: x.A)λ(tl: sci.List∧{A <: x.A}) let result = ν(self) {
    A = x.A; isEmpty = bool.false; head = hd; tail = tl } in result *)
Program Definition hconsV bool : hvl :=
  λ: x, λ:: hd tl, htv $ ν: self, {@
    type "A" = x @; "T";
    val "isEmpty" = λ: _, hfalseTm bool;
    val "head" =    λ: _, hd;
    val "tail" =    λ: _, tl
  }.

Definition hlistModV (bool : hvl) : hvl := ν: self, {@
  type "List" = hlistT bool self;
  val "nil"  = hnilV bool;
  val "cons" = hconsV bool
}.


(** ** Auxiliary types, needed in derivations of typing judgments. *)
Definition hconsTResConcr bool sci U := hlistTGen bool sci U U.

Definition hconsTConcr (bool sci : hpath) : hty :=
  ∀: x: tparam "T",
    x @; "T" →:
      hTAnd (sci @; "List") (type "A" >: ⊥ <: x @; "T") →:
      (hconsTResConcr bool sci (x @; "T")).

Definition hlistModTConcrBody bool sci : hty := {@
  typeEq "List" $ hlistT bool sci;
  val "nil" : hnilT sci;
  val "cons" : hconsTConcr bool sci
}.

Definition hlistModTConcr bool : hty := μ: sci, hlistModTConcrBody bool sci.

(** ** Lemmas for proof that [hlistModV] has type [hlistModT]. *)
Example nilTyp Γ : (▶: hlistModTConcrBody hx1 hx0)%ty :: boolImplT :: Γ u⊢ₜ
  hnilV hx1 : hnilT hx0.
Proof.
  apply (iT_Sub_nocoerce $ hclose $ hlistTGen hx1 hx0 ⊥ ⊥ ).
  - evar (T : ty).
    set L := (▶: hlistModTConcrBody hx1 hx0)%ty.
    have := !! trueTyp Γ [⊤; T; L].
    have := !! loopTyp (⊤ :: T :: L :: boolImplT :: Γ).
    rewrite {}/T/= => Ht Hl.
    tcrush; apply (iT_Sub_nocoerce ⊥); tcrush.
  - tcrush; last mltcrush.
    ettrans; first eapply iSub_Add_Later; stcrush.
    asideLaters.
    eapply iSub_Sel'; tcrush. varsub.
    asideLaters.
    ltcrush.
Qed.

Example consTyp Γ : (▶: hlistModTConcrBody hx1 hx0)%ty :: boolImplT :: Γ u⊢ₜ
  hconsV hx1 : hconsTConcr hx1 hx0.
Proof.
  epose proof falseTyp Γ [_; _; _; _; _; _] as Ht; cbn in Ht.
  tcrush; clear Ht.
  (** Typecheck returned head: *)
  by varsub; eapply (iSub_Sel' _ (hp4 @; "T")); tcrush; varsub; ltcrush.
  (**
    Typecheck returned tail. Recall [cons] starts with

      [λ: x, λ:: hd tl, htv $ ν: self, ...].

    Hence, [x.A] is the type argument to [cons], and [tl] has type
    [List & {A = x.A}].

    Since [cons] constructs a new object, [hconsTConcr] types it against
    a *copy* of the list body, whose element type [self.A] is a copy of [x.A]. *)
  (** Hence, we must show that [tl] has type [List & {A = self.A}]. *)
  (** It suffices to show that [List & {A = x.A} <: List & {A = self.A}]: *)
  varsub.
  (** It suffices to show that [x.A <: self.A]: *)
  tcrush; lNext.

  (** We do it using [iSub_Sel'] on [self.A], and looking up [A] on [self]'s type. *)
  eapply iSub_Sel', (path_tp_delay (i := 0)); wtcrush. varsub; ltcrush.
Qed.

Ltac norm := cbv; hideCtx.
Lemma consTSub Γ : (hlistModTConcrBody hx1 hx0 : ty) :: boolImplT :: Γ u⊢ₜ
  hconsTConcr hx1 hx0, 0 <: hconsT hx0, 0.
Proof.
  tcrush; rewrite !iterate_S !iterate_0; hideCtx; last mltcrush.
  eapply iSub_Sel', (path_tp_delay (i := 0)); wtcrush; varsub; by ltcrush.
Qed.

Example listTypConcr Γ : boolImplT :: Γ u⊢ₜ hlistModV hx0 : hlistModTConcr hx0.
Proof.
  have Hn := nilTyp Γ.
  (* Without the call to [iD_Val], Coq would (smartly) default to [iD_All] *)
  have := consTyp Γ => /(iD_Val "cons") Hc /=.
  tcrush.
Qed.

(** ** Proof that [hlistModV] has type [hlistModT]. *)
Example listTyp Γ : boolImplT :: Γ u⊢ₜ hlistModV hx0 : hlistModT hx0.
Proof.
  have Hv := listTypConcr Γ.
  have Hsub := consTSub Γ.
  eapply iT_Sub_nocoerce; first exact Hv; ltcrush.
Qed.


(** ** Link lists with booleans. *)

(*
Naive attempt; this fails, because the return type mentions a local variable.
Inferring return types that avoid mentioning local variables is called the
avoidance problem, a term going back to the ML module literature. *)
(*
Definition clListV := lett (tv boolImplV) (tv listV).
Example clListTyp Γ : Γ u⊢ₜ clListV : listT.
  eapply iT_Let. apply boolImplTyp.
  Fail change (shift listT) with (listT).
  Fail apply listTyp.
Abort. *)

Definition hclListV' (hbody : hvl → hvl → htm) :=
  hlett: bool := pureS boolImplV in:
  hlett: list := hlistModV bool in:
    hbody bool list.

(** Have [clListV'] take an open de BruijN [tm]. *)
Definition clListV' (body : tm) := hclListV' (λ _ _, pureS body).

Example clListTyp' Γ (T : ty) body
  (Ht : shift (hlistModT hx0 : ty) :: boolImplT :: Γ u⊢ₜ body : shift (shift T)) :
  Γ u⊢ₜ clListV' body : T.
Proof.
  eapply iT_Let; first apply boolImplTyp.
  eapply iT_Let; first apply listTyp.
  all: tcrush.
Qed.

Example clListTypNat Γ :
  Γ u⊢ₜ clListV' (hvint 1) : hclose 𝐙.
Proof. apply clListTyp'. tcrush. Qed.

(** This typing lemma generalizes over an arbitrary body [hbody], taken as open HOAS terms. To close it,
we must turn it into a concrete term exactly as [hclListV'] would, which exposes implementation details
I'd rather not. *)
Example clListTyp'2 Γ (T : ty) hbody
  (Ht : (hlistModT hx1 : ty) :: boolImplT :: Γ u⊢ₜ hbody (hxm 1) (hxm 2) 2 : shift (shift T)) :
  Γ u⊢ₜ hclListV' hbody : T.
Proof.
  eapply iT_Let; first apply boolImplTyp.
  eapply iT_Let; first apply listTyp.
  all: tcrush.
Qed.

Example clListTypNat2 Γ :
  Γ u⊢ₜ hclListV' (λ _ _, hvint 1) : 𝐙.
Proof. apply clListTyp'2. tcrush. Qed.

(** ** Link lists with booleans and with a client using the list API. *)
Definition hheadCons (list : hvl) :=
  htskip $ htskip (
    (hAnfBind $ htskip
      (htyApp (list @: "cons") "T" 𝐙
        $: 0
        $: htskip (list @: "nil")))
    @: "head" $: 0).
(* Invoking a method from an abstract type (here, [list @; "List"] needs a skip. *)

Program Example hheadConsTyp Γ :
  hlistModT hx1 :: boolImplT :: Γ u⊢ₜ hheadCons (hxm 2) 2 : 𝐙.
Proof.
  hideCtx; set Γ' := Γ0.
  have HL : Γ' u⊢ₜ x0: hlistModTBody hx1 hx0 by apply: iT_Mu_E'; first var; stcrush.

  (* The result of "head" has one more later than the list. *)
  eapply (iT_Sub (i := 2) (T1 := ▶: ▶: 𝐙)).
  asideLaters. tcrush.
  eapply (iT_All_E (T1 := ⊤)); last (eapply iT_Sub_nocoerce); tcrush.
  have Hnil: Γ' u⊢ₜ (hxm 2 @: "nil") 2 : hclose (hnilT hx0)
    by tcrush; eapply iT_Sub_nocoerce; ltcrush.
  have Hsnil: Γ' u⊢ₜ htskip (hxm 2 @: "nil") 2
    : hclose $ hTAnd (hp0 @; "List") (typeEq "A" ⊥). {
    eapply (iT_Sub (i := 1)), Hnil.
    by tcrush; [lThis | lNext; apply iSub_AddI; tcrush].
  }
  have Hcons: Γ' u⊢ₜ (hxm 2 @: "cons") 2 : hconsT hx0. {
    tcrush.
    eapply iT_Sub_nocoerce; by [| ltcrush].
  }

  (* Here we produce a list of later nats, since we produce a list of p.A where p is the
  "type" argument and p : { A <: Nat} so p.A <: ▶: Nat. *)
  set U := (type "A" >: ⊥ <: ▶: 𝐙)%HT.
  set V := (hTAnd (hlistT hx1 hx0) U).
  apply AnfBind_typed with (T := V); stcrush; first last.
  {
    eapply iT_Sub_nocoerce; first
      eapply (iT_Mu_E' (T1 := (val "head" : ⊤ →: hp0 @; "A")%HT));
      [ | done | tcrush ..].
      - varsub; asideLaters; lThis; ltcrush.
      - by apply (iSel_Sub (L := ⊥)), (path_tp_delay (i := 0)); wtcrush; varsub; ltcrush.
  }
  eapply (iT_Sub (i := 1) (T1 := hTAnd (hp0 @; "List") U)).
  (******)
  (* We seem stuck here. The problem is that *we* wrote
  x.List & { A <: Nat }, and that's <: (▶: ListBody) & { A <: Nat }, and we have no
  rule to deal with that Later *in the syntax* *yet*.
  But we know that (▶: ListBody) & { A <: Nat } <: (▶: ListBody) & ▶: { A <: Nat }.
  Next, [Distr_TLater_And] gets us to
  (▶: (ListBody & { A <: Nat }), and we're back in business!
   *)
  {
    ettrans; last apply iLater_Sub; stcrush.
    ettrans; [|apply: iAnd_Later_Sub_Distr; stcrush].
    tcrush; [lThis | lNext].
    eapply iSel_Sub; tcrush.
    eapply iT_Sub_nocoerce; ltcrush.
  }

  eapply iT_All_E, Hsnil.
  eapply (iT_All_E (T1 := 𝐙)); last tcrush.
  (* Perform avoidance on the type application. *)
  eapply tyApp_typed with (T := 𝐙%HT); first done; intros; ltcrush; cbv -[Γ'].
  by eapply iSub_Sel', (path_tp_delay (i := 0)); try (typconstructor; var); wtcrush.
  by lNext.
  lNext; by eapply iSel_Sub, (path_tp_delay (i := 0)); try (typconstructor; var); wtcrush.
Qed.

Example clListTypNat3 Γ :
  Γ u⊢ₜ hclListV' (λ bool, hheadCons) : 𝐙.
Proof. apply clListTyp'2, hheadConsTyp. Qed.
