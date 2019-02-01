From D Require Import tactics.
From D.Dot Require Import dotsyn.

Reserved Notation "Γ ⊢ₜ e : T , i" (at level 74, e, T at next level).
Reserved Notation "Γ ⊢ₚ p : T , i" (at level 74, p, T, i at next level).
Reserved Notation "Γ |d V ⊢ d : T" (at level 74, d, T, V at next level).
Reserved Notation "Γ |ds V ⊢ ds : T" (at level 74, ds, T, V at next level).
Reserved Notation "Γ ⊢ₜ T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

Implicit Types (L T U V: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

(**
Judgments for typing, subtyping, path and definition typing.
Here we follow Nada Amin's judgment for definition typing: it is Γ ⊢ { l = d } : T,
meaning: this definition, with label l, has type T.
This works, but requires reformulating again a bit semantic definition typing for proofs.
*)
Inductive typed Γ: tm → ty → nat → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a value . *)
| Appv_typed e1 v2 T1 T2 i:
    Γ ⊢ₜ e1: TAll T1 T2, i →                        Γ ⊢ₜ tv v2 : T1, i →
    (*────────────────────────────────────────────────────────────*)
    Γ ⊢ₜ tapp e1 (tv v2) : T2.|[v2/], i
(** Non-dependent application; allowed for any argument. *)
| App_typed e1 e2 T1 T2 i:
    Γ ⊢ₜ e1: TAll T1 T2.|[ren (+1)], i →      Γ ⊢ₜ e2 : T1, i →
    (*────────────────────────────────────────────────────────────*)
    Γ ⊢ₜ tapp e1 e2 : T2, i
| Proj_typed e T l i:
    Γ ⊢ₜ e : TVMem l T, i →
    (*─────────────────────────*)
    Γ ⊢ₜ tproj e l : T, i
| TMuE_typed v T i:
    Γ ⊢ₜ tv v: TMu T, i →
    (*──────────────────────*)
    Γ ⊢ₜ tv v: T.|[v/], i
(** Introduction forms *)
| Lam_typed e T1 T2 :
    (* T1 :: Γ ⊢ₜ e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    T1.|[ren (+1)] :: Γ ⊢ₜ e : T2, 0 →
    (*─────────────────────────*)
    Γ ⊢ₜ tv (vabs e) : TAll T1 T2, 0
| VObj_typed ds T:
    Γ |ds T ⊢ ds: T →
    (*──────────────────────*)
    Γ ⊢ₜ tv (vobj ds): TMu T, 0
| TMuI_typed v T i:
    Γ ⊢ₜ tv v: T.|[v/], i →
    (*──────────────────────*)
    Γ ⊢ₜ tv v: TMu T, i
| Nat_typed n:
    Γ ⊢ₜ tv (vnat n): TNat, 0

(** "General" rules *)
| Var_typed x T :
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ ⊢ₜ tv (var_vl x) : T.|[ren (+x)], 0
| Subs_typed e T1 T2 j :
    Γ ⊢ₜ T1, 0 <: T2, j → Γ ⊢ₜ e : T1, 0 →
    (*───────────────────────────────*)
    Γ ⊢ₜ iterate tskip j e : T2, 0
(* XXX Must be generalized to something like the following, but that needs either
   skip instructions, or an indexed typing judgment. *)
(* | Subs_typed e i1 i2 T1 T2 : *)
(*     Γ ⊢ₜ T1, i1 <: T2, i2 → Γ ⊢ₜ  e : T1 → *)
(*     (*──────────────────────*) *)
(*     Γ ⊢ₜ e : T2 *)
(* A bit surprising this is needed, but appears in the DOT papers, and this is
   only admissible if t has a type U that is a proper subtype of TAnd T1 T2. *)
| TAndI_typed T1 T2 t i:
    Γ ⊢ₜ t : T1, i →
    Γ ⊢ₜ t : T2, i →
    Γ ⊢ₜ t : TAnd T1 T2, i
where "Γ ⊢ₜ e : T , i" := (typed Γ e T i)
with dms_typed Γ: ty → dms → ty → Prop :=
| dnil_typed V : Γ |ds V ⊢ [] : TTop
(* This demands definitions and members to be defined in aligned lists. I think
   we want more freedom, just like in the logical relation? *)
| dcons_typed V l d ds T1 T2:
    Γ |d V ⊢ d : T1 →
    Γ |ds V ⊢ ds : T2 →
    dms_hasnt ds l →
    label_of_ty T1 = Some l →
    (*──────────────────────*)
    Γ |ds V ⊢ (l, d) :: ds : TAnd T1 T2
where "Γ |ds V ⊢ ds : T" := (dms_typed Γ V ds T)
with dm_typed Γ : ty → dm → ty → Prop :=
| dty_typed V l L T U:
    TLater V :: Γ ⊢ₜ L, 0 <: U, 0 →
    TLater V :: Γ ⊢ₜ L, 1 <: T, 1 →
    TLater V :: Γ ⊢ₜ T, 1 <: U, 1 →
    Γ |d V ⊢ dtysyn T : TTMem l L U
| dvl_typed V l v T:
    V :: Γ ⊢ₜ tv v : T, 0 →
    Γ |d V ⊢ dvl v : TVMem l T
where "Γ |d V ⊢ d : T" := (dm_typed Γ V d T)
with path_typed Γ: path → ty → nat → Prop :=
| pv_typed v T i:
    Γ ⊢ₜ tv v : T, i →
    Γ ⊢ₚ pv v : T, i
| pv_dlater p T i:
    Γ ⊢ₚ p : TLater T, i →
    Γ ⊢ₚ p : T, S i
(* Mnemonic: Path from SELecting a Field *)
| pself_typed p T i l:
    Γ ⊢ₚ p : T, i →
    Γ ⊢ₚ pself p l : T, i
| p_subs_typed p T1 T2 i j :
    Γ ⊢ₜ T1, i <: T2, j → Γ ⊢ₚ p : T1, i →
    (*───────────────────────────────*)
    Γ ⊢ₚ p : T2, j
where "Γ ⊢ₚ p : T , i" := (path_typed Γ p T i)
(* Γ ⊢ₜ T1, i1 <: T2, i2 means that TLater^i1 T1 <: TLater^i2 T2. *)
with subtype Γ : ty → nat → ty → nat → Prop :=
| Refl_stp i T : Γ ⊢ₜ T, i <: T, i
| Trans_stp i1 i2 i3 T1 T2 T3:
    Γ ⊢ₜ T1, i1 <: T2, i2 → Γ ⊢ₜ T2, i2 <: T3, i3 → Γ ⊢ₜ T1, i1 <: T3, i3
| TLaterL_stp i T:
   Γ ⊢ₜ TLater T, i <: T, S i
| TLaterR_stp i T:
   Γ ⊢ₜ T, S i <: TLater T, i

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
where "Γ ⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).
