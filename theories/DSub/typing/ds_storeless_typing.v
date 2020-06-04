(**
  An (unstamped) typing judgment for DSub, allowing arbitrary values in paths.
*)
From D.DSub Require Export ds_syn.

Reserved Notation "Γ ⊢ₜ e : T" (at level 74, e, T at next level).
Reserved Notation "Γ ⊢ₜ T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

Implicit Types (L T U V : ty) (v : vl) (e : tm) (Γ : ctx).

Inductive typed Γ : tm → ty → Prop :=
| iT_All_Ex e1 v2 T1 T2:
    Γ ⊢ₜ e1: TAll T1 T2 →                        Γ ⊢ₜ tv v2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ ⊢ₜ tapp e1 (tv v2) : T2.|[v2/]
(** Non-dependent application; allowed for any argument. *)
| iT_All_E e1 e2 T1 T2:
    Γ ⊢ₜ e1: TAll T1 (shift T2) →      Γ ⊢ₜ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ ⊢ₜ tapp e1 e2 : T2
| iT_All_I e T1 T2:
    (* T1 :: Γ ⊢ₜ e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    shift T1 :: Γ ⊢ₜ e : T2 →
    (*─────────────────────────*)
    Γ ⊢ₜ tv (vabs e) : TAll T1 T2
| iT_Nat_I n:
    Γ ⊢ₜ tv (vint n): TInt

(** "General" rules *)
| iT_Var x T :
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ ⊢ₜ tv (var_vl x) : shiftN x T
| iT_ISub e T1 T2 i :
    Γ ⊢ₜ T1, 0 <: T2, i → Γ ⊢ₜ e : T1 →
    (*───────────────────────────────*)
    Γ ⊢ₜ iterate tskip i e : T2
| iT_Typ_Abs T L U :
    Γ ⊢ₜ T, 1 <: U, 0 →
    Γ ⊢ₜ L, 0 <: T, 1 →
    Γ ⊢ₜ tv (vty T) : TTMem L U
(* A bit surprising this is needed, but appears in the DOT papers, and this is
   only admissible if t has a type U that is a proper subtype of TAnd T1 T2. *)
where "Γ ⊢ₜ e : T " := (typed Γ e T)
with
subtype Γ : ty → nat → ty → nat → Prop :=
| iSub_Refl i T :
    Γ ⊢ₜ T, i <: T, i

| iSub_Trans i1 i2 i3 T1 T2 T3:
    Γ ⊢ₜ T1, i1 <: T2, i2 → Γ ⊢ₜ T2, i2 <: T3, i3 → Γ ⊢ₜ T1, i1 <: T3, i3

(* "Structural" rules about indexes *)
| iSub_Succ T i:
    Γ ⊢ₜ T, i <: T, S i
| iSub_Mono T1 T2 i:
    Γ ⊢ₜ T1, i <: T2, i →
    Γ ⊢ₜ T1, S i <: T2, S i
| iLater_Sub i T:
    Γ ⊢ₜ TLater T, i <: T, S i
| iSub_Later i T:
    Γ ⊢ₜ T, S i <: TLater T, i

(* "Logical" connectives *)
| iSub_Top i T :
    Γ ⊢ₜ T, i <: TTop, i
| iBot_Sub i T :
    Γ ⊢ₜ TBot, i <: T, i

(* Type selections. These rules don't use later, but here (for DSub) the
semantics of TTMem is defined so that most often L can and U must include
later themselves. *)
| iSel_Sub L U v:
    Γ ⊢ₜ tv v : TTMem L U →
    Γ ⊢ₜ TSel v, 0 <: U, 0

| iSub_Sel L U v:
    Γ ⊢ₜ tv v : TTMem L U →
    Γ ⊢ₜ L, 0 <: TSel v, 0

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types. *)
(* Needed? Maybe drop later instead? *)
(* | iLater_Sub_Later T1 T2 i:
    Γ ⊢ₜ T1, S i <: T2, S i →
    Γ ⊢ₜ TLater T1, i <: TLater T2, i *)
| iAll_Sub_All T1 T2 U1 U2 i:
    (* "Tight" premises. *)
    Γ ⊢ₜ T2, S i <: T1, S i →
    iterate TLater (S i) (shift T2) :: Γ ⊢ₜ U1, S i <: U2, S i →
    Γ ⊢ₜ TAll T1 U1, i <: TAll T2 U2, i
| iTyp_Sub_Typ L1 L2 U1 U2 i:
    Γ ⊢ₜ L2, i <: L1, i →
    Γ ⊢ₜ U1, i <: U2, i →
    Γ ⊢ₜ TTMem L1 U1, i <: TTMem L2 U2, i
where "Γ ⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).

Lemma Vty_typed Γ T L U :
    Γ ⊢ₜ tv (vty T) : TTMem (TLater T) (TLater T).
Proof. apply (iT_Typ_Abs Γ T); constructor. Qed.

Scheme typed_mut_ind := Induction for typed Sort Prop
with   subtype_mut_ind := Induction for subtype Sort Prop.

Combined Scheme typing_mut_ind from typed_mut_ind, subtype_mut_ind.
