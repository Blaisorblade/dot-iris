(**
  An (unstamped) typing judgment for DSub, allowing arbitrary values in paths.
*)
From D.DSub Require Export syn.

Reserved Notation "Γ ⊢ₜ e : T" (at level 74, e, T at next level).
Reserved Notation "Γ ⊢ₜ T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

Implicit Types (L T U V : ty) (v : vl) (e : tm) (Γ : ctx).

Inductive typed Γ : tm → ty → Prop :=
| Appv_typed e1 v2 T1 T2:
    Γ ⊢ₜ e1: TAll T1 T2 →                        Γ ⊢ₜ tv v2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ ⊢ₜ tapp e1 (tv v2) : T2.|[v2/]
(** Non-dependent application; allowed for any argument. *)
| App_typed e1 e2 T1 T2:
    Γ ⊢ₜ e1: TAll T1 T2.|[ren (+1)] →      Γ ⊢ₜ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ ⊢ₜ tapp e1 e2 : T2
| Lam_typed e T1 T2:
    (* T1 :: Γ ⊢ₜ e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    T1.|[ren (+1)] :: Γ ⊢ₜ e : T2 →
    (*─────────────────────────*)
    Γ ⊢ₜ tv (vabs e) : TAll T1 T2
| Nat_typed n:
    Γ ⊢ₜ tv (vnat n): TNat

(** "General" rules *)
| Var_typed x T :
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ ⊢ₜ tv (var_vl x) : T.|[ren (+x)]
| Subs_typed e T1 T2 i :
    Γ ⊢ₜ T1, 0 <: T2, i → Γ ⊢ₜ e : T1 →
    (*───────────────────────────────*)
    Γ ⊢ₜ iterate tskip i e : T2
| Vty_abs_typed T L U :
    Γ ⊢ₜ T, 1 <: U, 1 →
    Γ ⊢ₜ L, 1 <: T, 1 →
    Γ ⊢ₜ tv (vty T) : TTMem L U
(* A bit surprising this is needed, but appears in the DOT papers, and this is
   only admissible if t has a type U that is a proper subtype of TAnd T1 T2. *)
where "Γ ⊢ₜ e : T " := (typed Γ e T)
with
subtype Γ : ty → nat → ty → nat → Prop :=
| Refl_stp i T :
    Γ ⊢ₜ T, i <: T, i

| Trans_stp i1 i2 i3 T1 T2 T3:
    Γ ⊢ₜ T1, i1 <: T2, i2 → Γ ⊢ₜ T2, i2 <: T3, i3 → Γ ⊢ₜ T1, i1 <: T3, i3

(* "Structural" rules about indexes *)
| TSucc_stp T i:
    Γ ⊢ₜ T, i <: T, S i
| TMono_stp T1 T2 i:
    Γ ⊢ₜ T1, i <: T2, i →
    Γ ⊢ₜ T1, S i <: T2, S i

(* "Logical" connectives *)
| Top_stp i T :
    Γ ⊢ₜ T, i <: TTop, i
| Bot_stp i T :
    Γ ⊢ₜ TBot, i <: T, i

(* Type selections *)
| SelU_stp L U v:
    Γ ⊢ₜ tv v : TTMem L U →
    Γ ⊢ₜ TSel v, 0 <: U, 1

| LSel_stp L U v:
    Γ ⊢ₜ tv v : TTMem L U →
    Γ ⊢ₜ L, 1 <: TSel v, 0

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types.
 "Cov" stands for covariance, "Con" for contravariance. *)
(* Needed? Maybe drop later instead? *)
(* | TLaterCov_stp T1 T2 i:
    Γ ⊢ₜ T1, S i <: T2, S i →
    Γ ⊢ₜ TLater T1, i <: TLater T2, i *)
| TAllConCov_stp T1 T2 U1 U2 i:
    (* "Tight" premises. *)
    Γ ⊢ₜ T2, S i <: T1, S i →
    iterate TLater (S i) T2.|[ren (+1)] :: Γ ⊢ₜ U1, S i <: U2, S i →
    Γ ⊢ₜ TAll T1 U1, i <: TAll T2 U2, i
| TTMemConCov_stp L1 L2 U1 U2 i:
    Γ ⊢ₜ L2, S i <: L1, S i →
    Γ ⊢ₜ U1, S i <: U2, S i →
    Γ ⊢ₜ TTMem L1 U1, i <: TTMem L2 U2, i
where "Γ ⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).

Lemma Vty_typed Γ T L U :
    Γ ⊢ₜ tv (vty T) : TTMem T T.
Proof. apply (Vty_abs_typed Γ T); apply Refl_stp. Qed.

Scheme typed_mut_ind := Induction for typed Sort Prop
with   subtype_mut_ind := Induction for subtype Sort Prop.

Combined Scheme typing_mut_ind from typed_mut_ind, subtype_mut_ind.
