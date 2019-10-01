(**
WIP examples constructing syntactic typing derivations.
I am also experimenting with notations, but beware the current definitions are pretty bad.
 *)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn typingExInfra.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section examples.
(* From D Require Import typeExtraction *)
Context `{hasStampTable: stampTable}.

(********************)
(** MICRO-EXAMPLES **)
(********************)

Example ex0 e Γ T:
  Γ ⊢ₜ e : T →
  is_stamped_ty (length Γ) getStampTable T →
  Γ ⊢ₜ e : ⊤.
Proof. intros. apply (Subs_typed_nocoerce T TTop); tcrush. Qed.

Example ex1 Γ n T:
  Γ ⊢ₜ tv (ν {@ val "a" = vnat n}) : μ {@ val "a" : TNat }.
Proof.
  (* Help proof search: Avoid trying TMuI_typed, that's slow. *)
  apply VObj_typed; tcrush.
Qed.

Example ex2 Γ T
  (Hs: (p0 @; "B") ~[ 0 ] (getStampTable, (s1, σ1))):
  Γ ⊢ₜ tv (ν {@ type "A" = (σ1 ; s1) } ) :
    TMu (TAnd (TTMem "A" TBot TTop) TTop).
Proof.
  have Hst: is_stamped_ty (1 + length Γ) getStampTable (p0 @; "B").
  by tcrush.
  apply VObj_typed; last tcrush. (* Avoid trying TMuI_typed, that's slow. *)
  eapply dcons_typed; trivial.
  eapply (dty_typed (p0 @; "B")); tcrush.
Qed.

(* Try out fixpoints. *)
Definition F3 T :=
  TMu (TAnd (TTMem "A" T T) TTop).

Example ex3 Γ T
  (Hs: F3 (p0 @; "A") ~[ 0 ] (getStampTable, (s1, σ1))):
  Γ ⊢ₜ tv (ν {@ type "A" = (σ1 ; s1) } ) :
    F3 (F3 (TSel p0 "A")).
Proof.
  have Hst: is_stamped_ty (1 + length Γ) getStampTable (F3 (p0 @; "A")).
  by stcrush.
  apply VObj_typed; last tcrush. (* Avoid trying TMuI_typed, that's slow. *)
  eapply dcons_typed; trivial.
  eapply (dty_typed (F3 (p0 @; "A"))); by tcrush.
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
  val "key" = vabs (tapp (tproj (tv x0) "hashCode") tUnit)
}.
(* To typecheck the object body, we first typecheck it with a tighter type,
    and then widen it. *)
Definition KeysT' := μ {@
  type "Key" >: TNat <: ⊤;
  val "key": TAll HashableString (p1 @; "Key")
}.
(* IDEA for our work: use [(type "Key" >: TNat <: ⊤) ⩓ (type "Key" >: ⊥ <: ⊤)]. *)

Example hashKeys_typed Γ
  (Hs1: TNat ~[ 0 ] (getStampTable, (s1, σ1))) :
  Γ ⊢ₜ tv hashKeys : KeysT.
Proof.
  cut (Γ ⊢ₜ tv hashKeys : KeysT').
  { intros H.
    apply (Subs_typed_nocoerce KeysT'); first done.
    apply Mu_stp_mu; last stcrush.
    tcrush.
    eapply Trans_stp; first apply TAnd1_stp; tcrush.
  }
  apply VObj_typed; cbn; last by tcrush.
  eapply dcons_typed; tcrush.
  by apply (dty_typed TNat); tcrush.
  cbn; apply (App_typed _ _ _ TUnit);
    last eapply (Subs_typed_nocoerce TNat); tcrush.
  tcrush; cbn.

  pose (T0 := μ {@ val "hashCode" : TAll ⊤ 𝐍 }).

  have Htp: ∀ Γ', T0 :: Γ' ⊢ₜ tv x0 : val "hashCode" : TAll ⊤ TNat. {
    intros. eapply Subs_typed_nocoerce.
    eapply TMuE_typed'; by [exact: Var_typed'|].
    by apply TAnd1_stp; tcrush.
  }
  apply (Subs_typed_nocoerce (val "hashCode" : TAll ⊤ 𝐍)). exact: Htp.
  tcrush.
  eapply LSel_stp'; tcrush.
  eapply Var_typed_sub; by [|tcrush].
Qed.

(* new {
  val subSys1 : { z => type A <: Int } = new { type A = Int }
  val subSys2 : { z => type B } = new { type B = String }
} *)
Context (String : ty).

(* Term *)
Definition systemVal := tv (ν {@
  val "subSys1" = ν {@ type "A" = (σ1; s1) } ;
  val "subSys2" = ν {@ type "B" = (σ2; s2) } }).
Definition systemValTDef1 :=
  TNat ~[ 0 ] (getStampTable, (s1, σ1)).
Definition systemValTDef2 :=
  String ~[ 0 ] (getStampTable, (s2, σ2)).

(* Type *)
Definition systemValT := μ {@
  val "subSys1" : μ {@ type "A" >: ⊥ <: TNat};
  val "subSys2" : μ {@ type "B" >: ⊥ <: ⊤}}.

Example motivEx Γ (Hs1: systemValTDef1) (Hs2: systemValTDef2)
  (HsString: is_stamped_ty (2 + length Γ) getStampTable String):
  Γ ⊢ₜ systemVal : systemValT.
Proof.
  apply VObj_typed; last by tcrush.
  eapply dcons_typed; tcrush.
  all: [> apply (dty_typed TNat) | apply (dty_typed String) ]; tcrush.
Qed.

(* Uh, we can unfold recursive types during construction! Does that allow
us to encode mutual recursion? Write this up. *)
Definition systemValT' := μ {@
  val "subSys1" : type "A" >: ⊥ <: TNat;
  val "subSys2" : type "B" >: ⊥ <: ⊤}.
Example motivEx1 Γ (Hs1: systemValTDef1) (Hs2: systemValTDef2)
  (HsString: is_stamped_ty (2 + length Γ) getStampTable String):
  Γ ⊢ₜ systemVal : systemValT'.
Proof.
  apply VObj_typed; last tcrush.
  eapply dcons_typed; tcrush.
  - apply (Subs_typed_nocoerce (μ {@ type "A" >: ⊥ <: TNat})); tcrush.
    + apply (dty_typed TNat); tcrush.
    + eapply Trans_stp;
      [eapply (Mu_stp _ ({@ type "A" >: ⊥ <: TNat })%ty 0)|]; tcrush.
  - apply (Subs_typed_nocoerce (μ {@ type "B" >: ⊥ <: ⊤})); tcrush.
    + apply (dty_typed String); tcrush.
    + eapply Trans_stp;
      [eapply (Mu_stp _ ({@ type "B" >: ⊥ <: ⊤ })%ty 0)|]; tcrush.
Qed.

End examples.
