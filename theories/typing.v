From Dot Require Import tactics dotsyn.

Reserved Notation "Γ ⊢ₜ e : T" (at level 74, e, T at next level).
Reserved Notation "Γ ⊢ₚ p : T , i" (at level 74, p, T, i at next level).
Reserved Notation "Γ ⊢ { l = d } : T" (at level 64, l, d, T at next level).
Reserved Notation "Γ ⊢ds ds : T" (at level 74, ds, T at next level).
Reserved Notation "Γ ⊢ₜ T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

(**
Judgments for typing, subtyping, path and definition typing.
TODO: index the typing judgment as well.
Here we follow Amin's judgment for definition typing: it is Γ ⊢ { l = d } : T,
meaning: this definition, with label l, has type T.
This works, but requires reformulating again a bit semantic definition typing for proofs.
*)
Inductive typed Γ: tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a value . *)
| Appv_typed e1 v2 T1 T2 :
    Γ ⊢ₜ e1: TAll T1 T2 →                        Γ ⊢ₜ tv v2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ ⊢ₜ tapp e1 (tv v2) : T2.|[v2/]
(** Non-dependent application; allowed for any argument. *)
| App_typed e1 e2 T1 T2 :
    Γ ⊢ₜ e1: TAll T1 T2.|[ren (+1)] →      Γ ⊢ₜ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ ⊢ₜ tapp e1 e2 : T2
| Proj_typed e T l:
    Γ ⊢ₜ e : TVMem l T →
    (*─────────────────────────*)
    Γ ⊢ₜ tproj e l : T
| TMuE_typed v T:
    Γ ⊢ₜ tv v: TMu T →
    (*──────────────────────*)
    Γ ⊢ₜ tv v: T.|[v/]
(** Introduction forms *)
| Lam_typed e T1 T2 :
    (* T1 :: Γ ⊢ₜ e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    T1.|[ren (+1)] :: Γ ⊢ₜ e : T2 →
    (*─────────────────────────*)
    Γ ⊢ₜ tv (vabs e) : TAll T1 T2
| VObj_typed ds T:
    TLater T :: Γ ⊢ds ds: T →
    (*──────────────────────*)
    Γ ⊢ₜ tv (vobj ds): TMu T
| TMuI_typed v T:
    Γ ⊢ₜ tv v: T.|[v/] →
    (*──────────────────────*)
    Γ ⊢ₜ tv v: TMu T
| Nat_typed n:
    Γ ⊢ₜ tv (vnat n) : TNat

(** "General" rules *)
| Var_typed x T :
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ ⊢ₜ tv (var_vl x) : T.|[ren (+x)]
| Subs_typed e T1 T2 :
    Γ ⊢ₜ T1, 0 <: T2, 0 → Γ ⊢ₜ e : T1 →
    (*───────────────────────────────*)
    Γ ⊢ₜ e : T2
(* XXX Must be generalized to something like the following, but that needs either
   skip instructions, or an indexed typing judgment. *)
(* | Subs_typed e i1 i2 T1 T2 : *)
(*     Γ ⊢ₜ T1, i1 <: T2, i2 → Γ ⊢ₜ  e : T1 → *)
(*     (*──────────────────────*) *)
(*     Γ ⊢ₜ e : T2 *)
(* A bit surprising this is needed, but appears in the DOT papers, and this is
   only admissible if t has a type U that is a proper subtype of TAnd T1 T2. *)
| TAndI_typed T1 T2 t:
    Γ ⊢ₜ t : T1 →
    Γ ⊢ₜ t : T2 →
    Γ ⊢ₜ t : TAnd T1 T2
with dms_typed Γ: dms → ty → Prop :=
| dnil_typed : Γ ⊢ds [] : TTop
| dcons_typed l d ds T1 T2 :
    Γ ⊢ds ds : T1 →
    l = length ds →
    Γ ⊢ { l = d } : T2 →
    (*──────────────────────*)
    Γ ⊢ds d :: ds : TAnd T1 T2

with dm_typed Γ : label → dm → ty → Prop :=
| dty_typed l L T U:
    Γ ⊢ₜ L, 0 <: U, 0 →
    Γ ⊢ₜ L, 1 <: T, 1 →
    Γ ⊢ₜ T, 1 <: U, 1 →
    Γ ⊢ { l = dtysyn T } : TTMem l L U
| dvl_typed l v T:
    Γ ⊢ₜ tv v : TLater T →
    Γ ⊢ { l = dvl v } : TVMem l T
with path_typed Γ: path → ty → nat → Prop :=
| pv_typed v T :
    Γ ⊢ₜ tv v : T →
    Γ ⊢ₚ pv v : T, 0
(* Mnemonic: Path from SELecting a Field *)
| pself_typed p T i l:
    Γ ⊢ₚ p : T, i →
    Γ ⊢ₚ pself p l : T, i
| p_subs_typed p T1 T2 i j :
    Γ ⊢ₜ T1, i <: T2, j → Γ ⊢ₚ p : T1, i →
    (*───────────────────────────────*)
    Γ ⊢ₚ p : T2, j

(* Γ ⊢ₜ T1, i1 <: T2, i2 means that TLater^i1 T1 <: TLater^i2 T2. *)
with subtype Γ : ty → nat → ty → nat → Prop :=
| Refl_stp i T : Γ ⊢ₜ T, i <: T, i
| Trans_stp i1 i2 i3 T1 T2 T3:
    Γ ⊢ₜ T1, i1 <: T2, i2 → Γ ⊢ₜ T2, i2 <: T3, i3 → Γ ⊢ₜ T1, i1 <: T3, i3

(* "Structural" rules about indexes *)
| TSucc_stp T i:
    Γ ⊢ₜ T, i <: T, S i
| TMono_stp T1 T2 i:
    Γ ⊢ₜ T1, i <: T2, i →
    Γ ⊢ₜ T1, S i <: T2, S i

(* "Logical" connectives *)
| Top_stp i T : Γ ⊢ₜ T, i <: TTop, i
| Bot_stp i T : Γ ⊢ₜ TBot, i <: T, i
| TAnd1_stp T1 T2 i:
    Γ ⊢ₜ TAnd T1 T2, i <: T1, i
| TAnd2_stp T1 T2 i:
    Γ ⊢ₜ TAnd T1 T2, i <: T2, i
| TAnd_stp T1 T2 U i:
    Γ ⊢ₜ U, i <: T1, i →
    Γ ⊢ₜ U, i <: T2, i →
    Γ ⊢ₜ U, i <: TAnd T1 T2, i
| TOr1_stp T1 T2 i:
    Γ ⊢ₜ T1, i <: TOr T1 T2, i
| TOr2_stp T1 T2 i:
    Γ ⊢ₜ T2, i <: TOr T1 T2, i
| TOr_stp T1 T2 U i:
    Γ ⊢ₜ T1, i <: U, i →
    Γ ⊢ₜ T2, i <: U, i →
    Γ ⊢ₜ TOr T1 T2, i <: U, i

(* Type selections *)
| SelU_stp l L U p i j:
    Γ ⊢ₚ p : TTMem l L U, i →
    Γ ⊢ₜ TSel p l, j <: U, S (i + j)
| LSel_stp l L U p i j:
    Γ ⊢ₚ p : TTMem l L U, i →
    Γ ⊢ₜ L, S (i + j) <: TSel p l, j
| SelAU_stp l L U p i j:
    Γ ⊢ₚ p : TTMem l L U, i →
    Γ ⊢ₜ TSelA p l L U, j <: U, i + j
| LSelA_stp l L U p i j:
    Γ ⊢ₚ p : TTMem l L U, i →
    Γ ⊢ₜ L, i + j <: TSelA p l L U, j

(* Subtyping for recursive types. Congruence, and opening in both directions. *)
| mu_x_stp T1 T2 i:
    (T1 :: Γ) ⊢ₜ T1, i <: T2, i →
    Γ ⊢ₜ TMu T1, i <: TMu T2, i
| mu_1_stp T1 T2 i:
    (T1 :: Γ) ⊢ₜ T1, i <: T2.|[ren (+1)], i →
    Γ ⊢ₜ TMu T1, i <: T2, i
| mu_2_stp T1 T2 i:
    (T1 :: Γ) ⊢ₜ T1.|[ren (+1)], i <: T2, i →
    Γ ⊢ₜ T1, i <: TMu T2, i

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types.
 "Cov" stands for covariance, "Con" for contravariance. *)
(* Needed? Maybe drop later instead? *)
| TLaterCov_stp T1 T2 i:
    Γ ⊢ₜ T1, S i <: T2, S i →
    Γ ⊢ₜ TLater T1, i <: TLater T2, i
| TAllConCov_stp T1 T2 U1 U2 i:
    (* "Tight" premises. To avoid TLater, we'd probably need to index the
    context. But let's not; indexing the conclusion of typing and having an
    elimination form for TLater (which increases the index) would be enough. *)
    (* Γ ⊢ₜ T2, S i <: T1, S i → *)
    (* TLater T2 :: Γ ⊢ₜ U1, S i <: U2, S i → *)
    (* Non-tight premises. *)
    Γ ⊢ₜ T2, i <: T1, i →
    T2 :: Γ ⊢ₜ U1, i <: U2, i →
    Γ ⊢ₜ TAll T1 U1, i <: TAll T2 U2, i
| TVMemCov_stp T1 T2 i l:
    Γ ⊢ₜ T1, S i <: T2, S i →
    Γ ⊢ₜ TVMem l T1, i <: TVMem l T2, i
| TTMemConCov_stp L1 L2 U1 U2 i l:
    Γ ⊢ₜ L2, S i <: L1, S i →
    Γ ⊢ₜ U1, S i <: U2, S i →
    Γ ⊢ₜ TTMem l L1 U1, i <: TTMem l L2 U2, i

where "Γ ⊢ₜ e : T" := (typed Γ e T)
and "Γ ⊢ₚ p : T , i" := (path_typed Γ p T i)
and "Γ ⊢ds ds : T" := (dms_typed Γ ds T)
and "Γ ⊢ { l = d } : T" := (dm_typed Γ l d T)
and "Γ ⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).
