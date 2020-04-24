(**
  A stamped typing judgment for DSub, allowing arbitrary values in paths.
*)
From D Require Import tactics.
From D.DSub Require Export syn.
From D.DSub Require Import core_stamping_defs ast_stamping.
From D.DSubSyn Require Import obj_ident_typing.

Set Implicit Arguments.

Implicit Types (L T U V : ty) (v : vl) (e : tm) (Γ : ctx) (g : stys).

Reserved Notation "Γ s⊢ₜ[ g  ] e : T" (at level 74, e, T at next level).
Reserved Notation "Γ s⊢ₜ[ g  ] T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

Inductive typed Γ g : tm → ty → Prop :=
| iT_All_Ex e1 v2 T1 T2:
    Γ s⊢ₜ[ g ] e1: TAll T1 T2 →                        Γ s⊢ₜ[ g ] tv v2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ s⊢ₜ[ g ] tapp e1 (tv v2) : T2.|[v2/]
(** Non-dependent application; allowed for any argument. *)
| iT_All_E e1 e2 T1 T2:
    Γ s⊢ₜ[ g ] e1: TAll T1 (shift T2) →      Γ s⊢ₜ[ g ] e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ s⊢ₜ[ g ] tapp e1 e2 : T2
| iT_All_I e T1 T2:
    (* T1 :: Γ s⊢ₜ[ g ] e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    shift T1 :: Γ s⊢ₜ[ g ] e : T2 →
    (*─────────────────────────*)
    Γ s⊢ₜ[ g ] tv (vabs e) : TAll T1 T2
| iT_Nat_I n:
    Γ s⊢ₜ[ g ] tv (vint n): TInt

(** "General" rules *)
| iT_Var x T :
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ s⊢ₜ[ g ] tv (var_vl x) : shiftN x T
| iT_Sub e T1 T2 i :
    Γ s⊢ₜ[ g ] T1, 0 <: T2, i → Γ s⊢ₜ[ g ] e : T1 →
    (*───────────────────────────────*)
    Γ s⊢ₜ[ g ] iterate tskip i e : T2
| iT_Typ_Abs T L U σ s :
    T ~[ length Γ ] (g, (s, σ)) →
    Γ s⊢ₜ[ g ] T, 1 <: U, 1 →
    Γ s⊢ₜ[ g ] L, 1 <: T, 1 →
    Γ s⊢ₜ[ g ] tv (vstamp σ s) : TTMem L U
(* A bit surprising this is needed, but appears in the DOT papers, and this is
   only admissible if t has a type U that is a proper subtype of TAnd T1 T2. *)
where "Γ s⊢ₜ[ g ] e : T " := (typed Γ g e T)
with
subtype Γ g : ty → nat → ty → nat → Prop :=
| iSub_Refl i T :
    Γ s⊢ₜ[ g ] T, i <: T, i

| iSub_Trans i1 i2 i3 T1 T2 T3:
    Γ s⊢ₜ[ g ] T1, i1 <: T2, i2 → Γ s⊢ₜ[ g ] T2, i2 <: T3, i3 → Γ s⊢ₜ[ g ] T1, i1 <: T3, i3

(* "Structural" rules about indexes *)
| iSub_Succ T i:
    Γ s⊢ₜ[ g ] T, i <: T, S i
| iSub_Mono T1 T2 i:
    Γ s⊢ₜ[ g ] T1, i <: T2, i →
    Γ s⊢ₜ[ g ] T1, S i <: T2, S i

(* "Logical" connectives *)
| iSub_Top i T :
    Γ s⊢ₜ[ g ] T, i <: TTop, i
| iBot_Sub i T :
    Γ s⊢ₜ[ g ] TBot, i <: T, i

(* Type selections *)
| iSel_Sub L U v:
    Γ s⊢ₜ[ g ] tv v : TTMem L U →
    Γ s⊢ₜ[ g ] TSel v, 0 <: U, 1

| iSub_Sel L U v:
    Γ s⊢ₜ[ g ] tv v : TTMem L U →
    Γ s⊢ₜ[ g ] L, 1 <: TSel v, 0

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types.
 "Cov" stands for covariance, "Con" for contravariance. *)
(* Needed? Maybe drop later instead? *)
(* | iLater_Sub_Later T1 T2 i:
    Γ s⊢ₜ[ g ] T1, S i <: T2, S i →
    Γ s⊢ₜ[ g ] TLater T1, i <: TLater T2, i *)
| iAll_Sub_All T1 T2 U1 U2 i:
    (* "Tight" premises. *)
    Γ s⊢ₜ[ g ] T2, S i <: T1, S i →
    iterate TLater (S i) (shift T2) :: Γ s⊢ₜ[ g ] U1, S i <: U2, S i →
    Γ s⊢ₜ[ g ] TAll T1 U1, i <: TAll T2 U2, i
| iTyp_Sub_Typ L1 L2 U1 U2 i:
    Γ s⊢ₜ[ g ] L2, S i <: L1, S i →
    Γ s⊢ₜ[ g ] U1, S i <: U2, S i →
    Γ s⊢ₜ[ g ] TTMem L1 U1, i <: TTMem L2 U2, i
where "Γ s⊢ₜ[ g ] T1 , i1 <: T2 , i2" := (subtype Γ g T1 i1 T2 i2).

(* Just to show this doesn't work as easily. *)
(* Lemma stamp_typing_v1 Γ:
  (∀ e T, Γ u⊢ₜ e : T → Γ s⊢ₜ[ g ] e : T) ∧
  (∀ T1 i1 T2 i2, Γ u⊢ₜ T1, i1 <: T2, i2 → Γ s⊢ₜ[ g ] T1, i1 <: T2, i2).
Proof.
  eapply typing_mut_ind with
      (P := λ Γ e T _, Γ s⊢ₜ[ g ] e : T)
      (P0 := λ Γ T1 i1 T2 i2 _, Γ s⊢ₜ[ g ] T1, i1 <: T2, i2); clear Γ;
    try solve [econstructor; eauto].
Abort. *)

Lemma Vty_typed Γ g T L U σ s :
    T ~[ length Γ ] (g, (s, σ)) →
    Γ s⊢ₜ[ g ] tv (vstamp σ s) : TTMem T T.
Proof. intros H. apply (iT_Typ_Abs (T := T)); auto using iSub_Refl. Qed.

Scheme stamped_typed_mut_ind := Induction for typed Sort Prop
with   stamped_subtype_mut_ind := Induction for subtype Sort Prop.
Combined Scheme stamped_typing_mut_ind from stamped_typed_mut_ind, stamped_subtype_mut_ind.

Hint Constructors subtype typed : core.
Remove Hints iSub_Trans : core.
Hint Extern 10 => try_once iSub_Trans : core.

Lemma stamped_typing_mono_mut Γ g:
  (∀ e T, Γ s⊢ₜ[ g ] e : T → ∀ g' (Hle: g ⊆ g'), Γ s⊢ₜ[ g' ] e : T) ∧
  (∀ T1 i1 T2 i2, Γ s⊢ₜ[ g ] T1, i1 <: T2, i2 → ∀ g' (Hle: g ⊆ g'), Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2).
Proof.
  eapply stamped_typing_mut_ind with
      (P := λ Γ g e T _, ∀ g' (Hle: g ⊆ g'), Γ s⊢ₜ[ g' ] e : T)
      (P0 := λ Γ g T1 i1 T2 i2 _, ∀ g' (Hle: g ⊆ g'), Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2);
  clear Γ; intros; ev; try by eauto.
Qed.
Lemma stamped_typed_mono Γ (g g' : stys) (Hle: g ⊆ g') e T:
  Γ s⊢ₜ[ g ] e : T → Γ s⊢ₜ[ g' ] e : T.
Proof. unmut_lemma (stamped_typing_mono_mut Γ g). Qed.
Lemma stamped_subtype_mono Γ (g g' : stys) (Hle: g ⊆ g') T1 i1 T2 i2:
  Γ s⊢ₜ[ g ] T1, i1 <: T2, i2 → Γ s⊢ₜ[ g' ] T1, i1 <: T2, i2.
Proof. unmut_lemma (stamped_typing_mono_mut Γ g). Qed.
