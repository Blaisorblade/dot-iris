(**
WIP examples constructing syntactic typing derivations.
I am also experimenting with notations, but beware the current definitions are pretty bad.
 *)
From D Require Import tactics.
From D.Dot Require Import syn.
From stdpp Require Import strings.
From D.Dot Require Import traversals.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

(****************)
(** NOTATIONS  **)
(****************)

(** First, let's maybe start defining some nicer notation. I have little clue what I'm doing tho.
    *)

(* Beware that "Bind Scope" just presets the scope of arguments for *new* definitions. *)

(** Notation for object values. *)
Bind Scope dms_scope with dms.
Open Scope dms_scope.
Notation " {@ } " := (@nil (string * dm)) (format "{@ }") : dms_scope.
Notation " {@ x } " := ( x :: {@} ) (format "{@  x  }"): dms_scope.
Notation " {@ x ; y ; .. ; z } " := (cons x (cons y .. (cons z nil) ..)) (format "{@  x ;  y ;  .. ;  z  }"): dms_scope.
Close Scope dms_scope.
Arguments vobj _%dms_scope.

Notation "'ν' ds " := (vobj ds) (at level 60, ds at next level).
Notation "'val' l = v" := (l, dvl v) (at level 60, l at level 50).
Notation "'type' l = ( σ ; s )" := (l, dtysem σ s) (at level 60, l at level 50).

(** Notation for object types. *)
Bind Scope ty_scope with ty.
Open Scope ty_scope.
Notation "⊤" := TTop : ty_scope.
Notation "⊥" := TBot : ty_scope.
Notation " {@ } " := TTop (format "{@ }") : ty_scope.
Notation " {@ T1 } " := ( TAnd T1 {@} ) (format "{@  T1  }"): ty_scope.
Notation " {@ T1 ; T2 ; .. ; Tn } " := (TAnd T1 (TAnd T2 .. (TAnd Tn {@})..))
                                       (format "{@  T1  ;  T2  ;  ..  ;  Tn  }") : ty_scope.
(* Notation " {@ T1 ; .. ; T2 ; Tn } " := (TAnd (TAnd .. (TAnd {@} T1) .. T2) Tn) *)
(*                                          (format "{@  T1  ;  ..  ;  T2  ;  Tn  }"): ty_scope. *)
Close Scope ty_scope.
Delimit Scope ty_scope with ty.

Notation "'μ' Ts " := (TMu Ts) (at level 60, Ts at next level).
Notation "'type' l >: L <: U" := (TTMem l L U) (at level 60, l, L, U at level 50).
Notation "'val' l : T" := (TVMem l T) (at level 60, l, T at level 50).

Notation σ1 := ([] : vls).
Notation s1 := (1 % positive).

Notation σ2 := ([] : vls).
Notation s2 := (2 % positive).

Check ν {@ val "a" = vnat 0 }.

Check ν {@ type "A" = (σ1 ; s1) }.
Check ν {@ val "a" = vnat 0; type "A" = (σ1 ; s1) }.
Check μ {@ type "A" >: TNat <: TTop }.
Check μ {@ val "a" : TNat }.

Check vobj {@}.
Check ν {@ }.
Check ν {@ val "a" = vnat 0 }.
Check ν {@ val "a" = vnat 0 ; val "b" = vnat 1 }.
Check ν {@ val "a" = vnat 0 ; type "A" = (σ1 ; s1) }.

(* Notation "v @ l1 @ .. @ l2 ; l" := (TSel (pself .. (pself (pv v) l1) .. l2) l) *)
(*                                      (format "v  @  l1  @  ..  @  l2  ;  l", at level 69, l1, l2 at level 60). *)
(* Check (TSel (pself (pself p0 1) 2) 3). *)
(* Check (x0 @ 1 @ 2 ; 3). *)

Notation "v @ l1 @ .. @ l2" := (pself .. (pself (pv v) l1) .. l2)
                                     (format "v  @  l1  @  ..  @  l2", at level 69, l1, l2 at level 60).

Notation "p @; l" := (TSel p l) (at level 71).
Notation x0 := (var_vl 0).
Notation x1 := (var_vl 1).
Notation p0 := (pv x0).
Notation p1 := (pv x1).

Check (p0 @; "A").
Check (pself (pself p0 "A") "B" @; "C").
Check (x0 @ "A").
Check (x0 @ "A" @ "B" @; "C").

Notation TUnit := (⊤ % ty : ty).
Notation tUnit := (tv (vnat 0) : tm).

(****************)
(** AUTOMATION **)
(****************)
From D.Dot Require Import typing.

(* Deterministic crush. *)
Ltac dcrush := repeat constructor.
Ltac by_dcrush := by dcrush.

Import Trav1.

Ltac stcrush := try ((progress repeat
  match goal with
  | |- forall_traversal_tm   _ _ _ => constructor
  | |- forall_traversal_vl   _ _ _ => constructor
  | |- forall_traversal_dm   _ _ _ => constructor
  | |- forall_traversal_path _ _ _ => constructor
  | |- forall_traversal_ty   _ _ _ => constructor
  end); eauto).


Local Hint Extern 10 (_ ≤ _) => lia : core.

Hint Constructors typed subtype dms_typed dm_typed path_typed.
Remove Hints Trans_stp.
Hint Extern 10 => try_once Trans_stp.

Hint Extern 5 => try_once is_stamped_mono_ty.
Hint Extern 0 (dms_hasnt _ _) => done.

Hint Immediate Nat.lt_0_succ.

Section examples_lemmas.
(* From D Require Import typeExtraction *)
Context `{hasStampTable: stampTable}.

Lemma Var_typed' Γ x T1 T2 :
  Γ !! x = Some T1 →
  T2 = T1.|[ren (+x)] →
  (*──────────────────────*)
  Γ ⊢ₜ tv (var_vl x) : T2 .
Proof. intros; subst; by_dcrush. Qed.

Lemma TMuE_typed' Γ v T1 T2:
  Γ ⊢ₜ tv v: TMu T1 →
  T2 = T1.|[v/] →
  (*──────────────────────*)
  Γ ⊢ₜ tv v: T2.
Proof. intros; subst; auto. Qed.

Lemma Subs_typed_nocoerce T1 T2 {Γ e} :
  Γ ⊢ₜ e : T1 →
  Γ ⊢ₜ T1, 0 <: T2, 0 →
  Γ ⊢ₜ e : T2.
Proof. rewrite -(iterate_0 tskip e). eauto. Qed.
Hint Resolve Subs_typed_nocoerce.

Lemma is_stamped_pvar i n : i < n → is_stamped_path n getStampTable (pv (var_vl i)).
Proof. eauto. Qed.
Lemma is_stamped_pvars i n l : i < n → is_stamped_ty n getStampTable (pv (var_vl i) @; l).
Proof. eauto using is_stamped_pvar. Qed.
End examples_lemmas.

Hint Resolve is_stamped_pvar is_stamped_pvars.

Section examples.
(* From D Require Import typeExtraction *)
Context `{hasStampTable: stampTable}.

(********************)
(** MICRO-EXAMPLES **)
(********************)

Example ex0 e Γ T:
  Γ ⊢ₜ e : T →
  is_stamped_ty (length Γ) getStampTable T →
  Γ ⊢ₜ e : TTop.
Proof. intros. apply (Subs_typed_nocoerce T TTop); by_dcrush. Qed.

(* XXX Redeclaring notation so that it picks new scopes. Once it picks new
   scopes, the pretty-printer can use overloaded notation in its arguments.
   Instead, declare scopes before typing notation. *)
Local Notation "Γ ⊢ds ds : T"  := (dms_typed Γ ds T) (at level 74, ds, T at next level).

Example ex1 Γ n T:
  Γ ⊢ₜ tv (ν {@ val "a" = vnat n}) : μ {@ val "a" : TNat }.
Proof.
  (* Help proof search: Avoid trying TMuI_typed, that's slow. *)
  apply VObj_typed; by_dcrush.
Qed.

Example ex2 Γ T
  (Hs: (p0 @; "B") ~[ 1 + length Γ ] (getStampTable, (s1, σ1))):
  Γ ⊢ₜ tv (ν {@ type "A" = (σ1 ; s1) } ) :
    TMu (TAnd (TTMem "A" TBot TTop) TTop).
Proof.
  have Hst: is_stamped_ty (1 + length Γ) getStampTable (p0 @; "B").
  by auto 2.
  apply VObj_typed; last by_dcrush. (* Avoid trying TMuI_typed, that's slow. *)
  eapply dcons_typed; trivial.
  eapply (dty_typed (p0 @; "B")); eauto 3.
Qed.

(* Try out fixpoints. *)
Definition F3 T :=
  TMu (TAnd (TTMem "A" T T) TTop).

Example ex3 Γ T
  (Hs: F3 (p0 @; "A") ~[ 1 + length Γ ] (getStampTable, (s1, σ1))):
  Γ ⊢ₜ tv (ν {@ type "A" = (σ1 ; s1) } ) :
    F3 (F3 (TSel p0 "A")).
Proof.
  have Hst: is_stamped_ty (1 + length Γ) getStampTable (F3 (p0 @; "A")).
  by constructor; cbn; eauto.
  apply VObj_typed; last eauto. (* Avoid trying TMuI_typed, that's slow. *)
  eapply dcons_typed; trivial.
  eapply (dty_typed (F3 (p0 @; "A"))); eauto 3.
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
  (Hs1: TNat ~[ 1 + length Γ ] (getStampTable, (s1, σ1))) :
  Γ ⊢ₜ tv hashKeys : KeysT.
Proof.
  cut (Γ ⊢ₜ tv hashKeys : KeysT').
  { intros H.
    apply (Subs_typed_nocoerce KeysT'); first done.
    constructor; stcrush.
    apply TAnd_stp; last eapply TAnd2_stp; stcrush.
    eapply Trans_stp.
    - eapply TAnd1_stp; stcrush.
    - by_dcrush.
  }
  apply VObj_typed; cbn.
  eapply dcons_typed; dcrush; cbn.
  - apply (dty_typed TNat); by_dcrush.
  - apply (App_typed _ _ _ TUnit); first last.
    + by eapply (Subs_typed_nocoerce TNat); eauto 2.
    + dcrush; cbn.
      pose (T0 := μ {@ val "hashCode" : TAll {@} TNat }).
      have Htp: ∀ Γ', T0 :: Γ' ⊢ₜ tv x0 : val "hashCode" : TAll {@} TNat. {
        intros. eapply Subs_typed_nocoerce.
        eapply TMuE_typed'; by [exact: Var_typed'|].
        by eapply TAnd1_stp; stcrush.
      }
      apply (Subs_typed_nocoerce (val "hashCode" : TAll {@} TNat)). exact: Htp.
      dcrush.
      apply Trans_stp with (T2 := iterate TLater 1 TNat) (i2 := 0); first eauto.
      eapply LSel_stp with (p := pv (ids 2)) (U := ⊤%ty).
      dcrush.
      eapply Subs_typed_nocoerce; first by eapply Var_typed'.
      eapply TAnd1_stp; stcrush.
  - stcrush.
Qed.

(* new {
  val subSys1 : { z => type A <: Int } = new { type A = Int }
  val subSys2 : { z => type B } = new { type B = String }
} *)
Definition systemVal := tv (ν
  {@
    val "subSys1" = ν {@ type "A" = (σ1; s1) } ;
    val "subSys2" = ν {@ type "B" = (σ2; s2) } }).

Example motivEx Γ (String : ty)
  (HsString: is_stamped_ty (2 + length Γ) getStampTable String)
  (Hs1: TNat ~[ 2 + length Γ ] (getStampTable, (s1, σ1)))
  (Hs2: String ~[ 2 + length Γ ] (getStampTable, (s2, σ2))):
  Γ ⊢ₜ systemVal :
    μ {@
      val "subSys1" : μ {@ type "A" >: ⊥ <: TNat};
      val "subSys2" : μ {@ type "B" >: ⊥ <: ⊤}}.
Proof.
  apply VObj_typed; last by_dcrush.
  eapply dcons_typed; dcrush.
  all: [> apply (dty_typed TNat) |
    apply (dty_typed String) ]; by_dcrush.
Qed.

End examples.
