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
  apply (Subs_typed (i := 1) (T1 := hclose (▶: hpx (length Γ'') @; "Boolean")));
    rewrite /= plusnO; tcrush.
    eapply Subs_typed_nocoerce.
  - eapply TMuE_typed'; first eapply Var_typed'; try by [rewrite lookup_app_r ?Nat.sub_diag|]; stcrush.
  - ltcrush.
Qed.

Lemma falseTyp Γ Γ'' : Γ'' ++ boolImplT :: Γ u⊢ₜ
  hclose (hfalseTm (hx (length Γ''))) : hclose (hpx (length Γ'') @; "Boolean").
Proof.
  have ?: length Γ'' < length (Γ'' ++ boolImplT :: Γ) by rewrite app_length /=; lia.
  apply (Subs_typed (i := 1) (T1 := hclose (▶: hpx (length Γ'') @; "Boolean")));
    rewrite /= plusnO; tcrush.
  eapply Subs_typed_nocoerce.
  - eapply TMuE_typed'; first eapply Var_typed'; try by [rewrite lookup_app_r ?Nat.sub_diag|]; stcrush.
  - ltcrush.
Qed.

(** * Interface of the list module. *)

(* [sci] stands for [scala.collection.immutable], following the example in WadlerFest DOT. *)
Definition hlistTGen bool sci L U : hty := μ: self, {@
  type "A" >: L <: U;
  val "isEmpty" : ⊤ →: hpv bool @; "Boolean";
  val "head" : ⊤ →: hpv self @; "A";
  val "tail" : ⊤ →: hTAnd (hpv sci @; "List") (type "A" >: ⊥ <: hpv self @; "A" )
}.

(** ** The list type itself. *)
Definition hlistT bool sci := hlistTGen bool sci ⊥ ⊤.

(** This ▶: Later is needed because
- [hnilT] types a value member "nil" (which can't use skips), and
- this value member has abstract type [sci @; "List"], and
- when we initialize "nil", [sci] has type [▶:(type "List" >: ... <: ...], so
  we can't deduce anything about [sci@;"List"], only something about
  [▶:(sci@; "List")]. *)
Definition hnilT sci := hTAnd (▶: hpv sci @; "List") (typeEq "A" ⊥).

(** ∀(x: {A})∀(hd: x.A)∀(tl: sci.List∧{A <: x.A})sci.List∧{A <: x.A} *)
Definition hconsT sci : hty :=
  ∀: x : (tparam "T"),
    hpv x @; "T" →:
    (hTAnd (hpv sci @; "List") (type "A" >: ⊥ <: hpv x @; "T")) →:
    hTAnd (hpv sci @; "List") (type "A" >: ⊥ <: hpv x @; "T").

(** mod stands for module. *)
Definition hlistModTBody bool sci : hty := {@
  type "List" >: ⊥ <: hlistT bool sci;
  val "nil" : hnilT sci;
  val "cons" : hconsT sci
}.
Definition hlistModT bool : hty := μ: sci, hlistModTBody bool sci.


(** * Implementation of the list module. *)
Definition hnilV bool : hvl := ν: self, {@
  type "A" = ⊥;
  val "isEmpty" = hpv (λ: _, htrueTm bool);
  val "head" = hpv (λ: _, hloopTm);
  val "tail" = hpv (λ: _, hloopTm)
}.

(*
  λ(x: {A})λ(hd: x.A)λ(tl: sci.List∧{A <: x.A}) let result = ν(self) {
    A = x.A; isEmpty = bool.false; head = hd; tail = tl } in result *)
Program Definition hconsV bool : hvl :=
  λ: x, λ:: hd tl, htv $ ν: self, {@
    type "A" = hpv x @; "T";
    val "isEmpty" = hpv (λ: _, hfalseTm bool);
    val "head" =    hpv (λ: _, htv hd);
    val "tail" =    hpv (λ: _, htv tl)
  }.

Definition hlistModV bool : hvl := ν: self, {@
  type "List" = hlistT bool self;
  val "nil"  = hpv (hnilV bool);
  val "cons" = hpv (hconsV bool)
}.


(** * Auxiliary types, needed in derivations of typing judgments. *)
Definition hconsTResConcr bool sci U := hlistTGen bool sci U U.

Definition hconsTConcr bool sci : hterm ty :=
  ∀: x: tparam "T",
    hpv x @; "T" →:
      hTAnd (hpv sci @; "List") (type "A" >: ⊥ <: hpv x @; "T") →:
      (hconsTResConcr bool sci (hpv x @; "T")).

Definition hlistModTConcrBody bool sci : hty := {@
  typeEq "List" $ hlistT bool sci;
  val "nil" : hnilT sci;
  val "cons" : hconsTConcr bool sci
}.

Definition hlistModTConcr bool : hty := μ: sci, hlistModTConcrBody bool sci.

(** * Proofs that [hlistModV] has type [hlistModT]. *)

Example nilTyp Γ : hclose (▶: hlistModTConcrBody hx1 hx0) :: boolImplT :: Γ u⊢ₜ
  hclose (htv (hnilV hx1)) : hclose (hnilT hx0).
Proof.
  apply (Subs_typed_nocoerce $ hclose $ hlistTGen hx1 hx0 ⊥ ⊥ ).
  - evar (T : ty).
    set L :=  hclose (▶: hlistModTConcrBody hx1 hx0).
    have := trueTyp Γ [hclose ⊤; T; L].
    have := loopTyp (hclose ⊤ :: T :: L :: boolImplT :: Γ).
    rewrite {}/T/= => Ht Hl.
    tcrush; apply (Subs_typed_nocoerce (hclose ⊥)); cbn; tcrush.
  - tcrush; last mltcrush.
    ettrans; first eapply TAddLater_stp; stcrush.
    asideLaters.
    eapply LSel_stp'; tcrush. varsub.
    asideLaters.
    ltcrush.
Qed.

Example consTyp Γ : hclose (▶: hlistModTConcrBody hx1 hx0) :: boolImplT :: Γ u⊢ₜ
  hclose (htv (hconsV hx1)) : hclose (hconsTConcr hx1 hx0).
Proof.
  epose proof falseTyp Γ [_; _; _; _; _; _] as Ht; cbn in Ht.
  tcrush; clear Ht.
  (** Typecheck returned head: *)
  by varsub; eapply (LSel_stp' _ (hclose (hp4 @; "T"))); tcrush; varsub; ltcrush.
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

  (** We do it using [LSel_stp'] on [self.A], and looking up [A] on [self]'s type. *)
  eapply LSel_stp'; ltcrush. varsub; ltcrush.
Qed.

Ltac norm := cbv; hideCtx.
Lemma consTSub Γ : hclose (hlistModTConcrBody hx1 hx0) :: boolImplT :: Γ u⊢ₜ
  hclose (hconsTConcr hx1 hx0), 0 <: hclose (hconsT hx0), 0.
Proof.
  tcrush; rewrite !iterate_S !iterate_0; hideCtx; last mltcrush.
  eapply LSel_stp'; tcrush; varsub; by ltcrush.
Qed.

Example listTypConcr Γ : boolImplT :: Γ u⊢ₜ hclose (htv (hlistModV hx0)) : hclose (hlistModTConcr hx0).
Proof.
  have Hn := nilTyp Γ.
  (* Without the call to [dvl_typed], Coq would (smartly) default to [dvabs_typed] *)
  have := consTyp Γ => /(dvl_typed "cons") Hc /=.
  tcrush.
Qed.

Example listTyp Γ : boolImplT :: Γ u⊢ₜ hclose (htv (hlistModV hx0)) : hclose (hlistModT hx0).
Proof.
  have Hv := listTypConcr Γ.
  have Hsub := consTSub Γ.
  eapply Subs_typed_nocoerce; first exact Hv; ltcrush.
Qed.


(** * Link lists with booleans. *)

(* Naive attempt; this fails avoidance. *)
(*
Definition clListV := lett (tv boolImplV) (tv listV).
Example clListTyp Γ : Γ u⊢ₜ clListV : listT.
  eapply Let_typed. apply boolImplTyp.
  Fail change (shift listT) with (listT).
  Fail apply listTyp.
Abort. *)

Definition hclListV' (hbody : hvl → hvl → htm) :=
  hlett: bool := htv (pureS boolImplV) in:
  hlett: list := htv (hlistModV bool) in:
    hbody bool list.

(** Have [clListV'] take an open de BruijN [tm]. *)
Definition clListV' (body : tm) := hclListV' (λ _ _, pureS body).

Example clListTyp' Γ (T : ty) body
  (Ht : shift (hclose (hlistModT hx0)) :: boolImplT :: Γ u⊢ₜ body : shift (shift T)) :
  Γ u⊢ₜ hclose (clListV' body) : T.
Proof.
  eapply Let_typed; first apply boolImplTyp.
  eapply Let_typed; first apply listTyp.
  all: tcrush.
Qed.

Example clListTypNat Γ :
  Γ u⊢ₜ hclose (clListV' (hclose (htv (hvnat 1)))) : hclose 𝐍.
Proof. apply clListTyp'. tcrush. Qed.

(* Argh. Variable by de Bruijn level. Not good. *)
Definition hxm i : hvl := λ j, var_vl (j - i).
Goal hxm = λ i, ren (λ j, j - i). done. Abort.

(** This typing lemma generalizes over an arbitrary body [hbody], taken as open HOAS terms. To close it,
we must turn it into a concrete term exactly as [hclListV'] would, which exposes implementation details
I'd rather not. *)
Example clListTyp'2 Γ (T : ty) hbody
  (Ht : hclose (hlistModT hx1) :: boolImplT :: Γ u⊢ₜ hbody (hxm 1) (hxm 2) 2 : shift (shift T)) :
  Γ u⊢ₜ hclose (hclListV' hbody) : T.
Proof.
  eapply Let_typed; first apply boolImplTyp.
  eapply Let_typed; first apply listTyp.
  all: tcrush.
Qed.

Example clListTypNat2 Γ :
  Γ u⊢ₜ hclose (hclListV' (λ _ _, htv (hvnat 1))) : hclose 𝐍.
Proof. apply clListTyp'2. tcrush. Qed.

(** XXX: try recursive linking? Probably not. *)

(** * Link lists with booleans and with a client using the list API. *)
Definition hheadCons (list : hvl) :=
  htskip $ htskip (
    (hAnfBind $ htskip
      (htyApp (htv list @: "cons") "T" 𝐍
        $: htv (hvnat 0)
        $: htskip (htv list @: "nil")))
    @: "head" $: htv (hvnat 0)).
(* Invoking a method from an abstract type (here, [list @; "List"] needs a skip. *)

Example hheadConsTyp Γ :
  hclose (hlistModT hx1) :: boolImplT :: Γ u⊢ₜ (hheadCons (hxm 2)) 2 : hclose 𝐍.
Proof.
  match goal with
    |- ?Γ u⊢ₜ _ : _ =>
    set Γ' := Γ
  end.
  have HL : Γ' u⊢ₜ tv (ids 0): hclose (hlistModTBody hx1 hx0) by apply: TMuE_typed'; first var; stcrush.

  (* The result of "head" has one more later than the list. *)
  eapply (Subs_typed (i := 2) (T1 := hclose (▶: (▶: 𝐍)))).
  asideLaters. tcrush.
  eapply (App_typed (T1 := hclose ⊤)); last (eapply Subs_typed_nocoerce); tcrush.
  have Hnil: Γ' u⊢ₜ (htv (hxm 2) @: "nil") 2 : hclose (hnilT hx0)
    by tcrush; eapply Subs_typed_nocoerce; ltcrush.
  have Hsnil: Γ' u⊢ₜ htskip (htv (hxm 2) @: "nil") 2
    : hclose $ hTAnd (hp0 @; "List") (typeEq "A" ⊥). {
    eapply (Subs_typed (i := 1)), Hnil.
    by tcrush; [lThis | lNext; apply AddI_stp; tcrush].
  }
  have Hcons: Γ' u⊢ₜ (htv (hxm 2) @: "cons") 2 : hclose $ hconsT hx0. {
    tcrush.
    eapply Subs_typed_nocoerce; by [| ltcrush].
  }

  (* Here we produce a list of later nats, since we produce a list of p.A where p is the
  "type" argument and p : { A <: Nat} so p.A <: ▶: Nat. *)
  set U := (type "A" >: ⊥ <: ▶: 𝐍)%HT.
  set V := (hclose (hTAnd (hlistT hx1 hx0) U)).
  apply AnfBind_typed with (T := V); stcrush; first last.
  {
    eapply Subs_typed_nocoerce; first
      eapply TMuE_typed' with (T1 := hclose (val "head" : ⊤ →: hp0 @; "A"));
      [ | done | tcrush ..].
      - varsub; asideLaters; lThis; ltcrush.
      - by apply (SelU_stp (L := hclose ⊥)); tcrush; varsub; ltcrush.
  }
  eapply (Subs_typed (i := 1) (T1 := hclose (hTAnd (hp0 @; "List") U))).
  (******)
  (* We seem stuck here. The problem is that *we* wrote
  x.List & { A <: Nat }, and that's <: (▶: ListBody) & { A <: Nat }, and we have no
  rule to deal with that Later *in the syntax* *yet*.
  But we know that (▶: ListBody) & { A <: Nat } <: (▶: ListBody) & ▶: { A <: Nat }.
  Next, [Distr_TLater_And] gets us to
  (▶: (ListBody & { A <: Nat }), and we're back in business!
   *)
  {
    ettrans; last apply TLaterL_stp; stcrush.
    ettrans; [|apply: TDistr_TLater_And_stp; stcrush].
    tcrush; [lThis | lNext].
    eapply SelU_stp; tcrush.
    eapply Subs_typed_nocoerce; ltcrush.
  }

  eapply App_typed, Hsnil.
  eapply (App_typed (T1 := hclose 𝐍)); last tcrush.
  (* Perform avoidance on the type application. *)
  eapply tyApp_typed with (T := hclose 𝐍); first done; intros; ltcrush; cbv -[Γ'].
  by eapply LSel_stp'; tcrush; var.
  by lNext.
  lNext; by eapply SelU_stp; tcrush; var.
Qed.

Example clListTypNat3 Γ :
  Γ u⊢ₜ hclose (hclListV' (λ bool, hheadCons)) : hclose 𝐍.
Proof. apply clListTyp'2, hheadConsTyp. Qed.
