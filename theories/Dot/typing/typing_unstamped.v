(**
  An unstamped typing judgment for Dot, allowing only variables in paths, and not arbitrary values.
  We show that unstamped typing derivations from here can
  be converted to stamped derivations of this typing judgment, in lemma
  [stamp_typing_mut].
*)
From D Require Import tactics.
From D.Dot Require Export syn stampingDefsCore.

Set Implicit Arguments.

(* The typing judgement comes from [s/⊢/u⊢/] over [Dot/typing_objIdent.v], and dropping stamping. *)
Reserved Notation "Γ u⊢ₜ e : T" (at level 74, e, T at next level).
Reserved Notation "Γ u⊢ₚ p : T , i" (at level 74, p, T, i at next level).
Reserved Notation "Γ |d V u⊢{ l := d  } : T" (at level 74, l, d, T, V at next level).
Reserved Notation "Γ |ds V u⊢ ds : T" (at level 74, ds, T, V at next level).
Reserved Notation "Γ u⊢ₜ T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

Implicit Types (L T U V : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty).

(**
Judgments for typing, subtyping, path and definition typing.
*)
Inductive typed Γ : tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a value . *)
| Appv_typed e1 x2 T1 T2:
    Γ u⊢ₜ e1: TAll T1 T2 →                        Γ u⊢ₜ tv (var_vl x2) : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ u⊢ₜ tapp e1 (tv (var_vl x2)) : T2.|[(var_vl x2)/]
(** Non-dependent application; allowed for any argument. *)
| App_typed e1 e2 T1 T2:
    Γ u⊢ₜ e1: TAll T1 T2.|[ren (+1)] →      Γ u⊢ₜ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ u⊢ₜ tapp e1 e2 : T2
| Proj_typed e T l:
    Γ u⊢ₜ e : TVMem l T →
    (*─────────────────────────*)
    Γ u⊢ₜ tproj e l : T
| TMuE_typed x T:
    Γ u⊢ₜ tv (var_vl x): TMu T →
    (*──────────────────────*)
    Γ u⊢ₜ tv (var_vl x): T.|[(var_vl x)/]
(** Introduction forms *)
| Lam_typed e T1 T2:
    (* T1 :: Γ u⊢ₜ e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    is_unstamped_ty (length Γ) T1 →
    T1.|[ren (+1)] :: Γ u⊢ₜ e : T2 →
    (*─────────────────────────*)
    Γ u⊢ₜ tv (vabs e) : TAll T1 T2
| VObj_typed ds T:
    Γ |ds T u⊢ ds: T →
    is_unstamped_ty (S (length Γ)) T →
    (*──────────────────────*)
    Γ u⊢ₜ tv (vobj ds): TMu T
| TMuI_typed x T:
    Γ u⊢ₜ tv (var_vl x): T.|[(var_vl x)/] →
    (*──────────────────────*)
    Γ u⊢ₜ tv (var_vl x): TMu T
| Nat_typed n:
    Γ u⊢ₜ tv (vnat n): TNat

(** "General" rules *)
| Var_typed x T :
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ u⊢ₜ tv (var_vl x) : T.|[ren (+x)]
| Subs_typed e T1 T2 i :
    Γ u⊢ₜ T1, 0 <: T2, i → Γ u⊢ₜ e : T1 →
    (*───────────────────────────────*)
    Γ u⊢ₜ iterate tskip i e : T2
(* A bit surprising this is needed, but appears in the DOT papers, and this is
   only admissible if t has a type U that is a proper subtype of TAnd T1 T2. *)
| TAndI_typed T1 T2 x:
    Γ u⊢ₜ tv (var_vl x) : T1 →
    Γ u⊢ₜ tv (var_vl x) : T2 →
    Γ u⊢ₜ tv (var_vl x) : TAnd T1 T2
where "Γ u⊢ₜ e : T " := (typed Γ e T)
with dms_typed Γ : ty → dms → ty → Prop :=
| dnil_typed V : Γ |ds V u⊢ [] : TTop
(* This demands definitions and members to be defined in aligned lists. *)
| dcons_typed V l d ds T1 T2:
    Γ |d V u⊢{ l := d } : T1 →
    Γ |ds V u⊢ ds : T2 →
    dms_hasnt ds l →
    (*──────────────────────*)
    Γ |ds V u⊢ (l, d) :: ds : TAnd T1 T2
where "Γ |ds V u⊢ ds : T" := (dms_typed Γ V ds T)
with dm_typed Γ : ty → label → dm → ty → Prop :=
| dty_typed T V l L U:
    is_unstamped_ty (S (length Γ)) T →
    TLater V :: Γ u⊢ₜ TLater L, 0 <: TLater T, 0 →
    TLater V :: Γ u⊢ₜ TLater T, 0 <: TLater U, 0 →
    Γ |d V u⊢{ l := dtysyn T } : TTMem l L U
| dvl_typed V l v T:
    TLater V :: Γ u⊢ₜ tv v : T →
    Γ |d V u⊢{ l := dvl v } : TVMem l T
| dvabs_typed V T1 T2 e l:
    T1.|[ren (+1)] :: V :: Γ u⊢ₜ e : T2 →
    Γ |d V u⊢{ l := dvl (vabs e) } : TVMem l (TAll T1 T2)
where "Γ |d V u⊢{ l := d  } : T" := (dm_typed Γ V l d T)
with path_typed Γ : path → ty → nat → Prop :=
| pv_typed x T:
    Γ u⊢ₜ tv (var_vl x) : T →
    Γ u⊢ₚ pv (var_vl x) : T, 0
| pv_dlater p T i:
    Γ u⊢ₚ p : TLater T, i →
    Γ u⊢ₚ p : T, S i
(* Mnemonic: Path from SELecting a Field *)
| pself_typed p T i l:
    Γ u⊢ₚ p : TVMem l T, i →
    Γ u⊢ₚ pself p l : T, i
| p_subs_typed p T1 T2 i j :
    Γ u⊢ₜ T1, i <: T2, i + j →
    Γ u⊢ₚ p : T1, i →
    (*───────────────────────────────*)
    Γ u⊢ₚ p : T2, i + j
where "Γ u⊢ₚ p : T , i" := (path_typed Γ p T i)
(* Γ u⊢ₜ T1, i1 <: T2, i2 means that TLater^i1 T1 <: TLater^i2 T2. *)
with subtype Γ : ty → nat → ty → nat → Prop :=
| Refl_stp i T :
    is_unstamped_ty (length Γ) T →
    Γ u⊢ₜ T, i <: T, i
| Trans_stp i2 T2 {i1 i3 T1 T3}:
    Γ u⊢ₜ T1, i1 <: T2, i2 →
    Γ u⊢ₜ T2, i2 <: T3, i3 →
    Γ u⊢ₜ T1, i1 <: T3, i3
| TLaterL_stp i T:
    is_unstamped_ty (length Γ) T →
    Γ u⊢ₜ TLater T, i <: T, S i
| TLaterR_stp i T:
    is_unstamped_ty (length Γ) T →
    Γ u⊢ₜ T, S i <: TLater T, i

(* "Structural" rules about indexes *)
| TAddLater_stp T i:
    is_unstamped_ty (length Γ) T →
    Γ u⊢ₜ T, i <: TLater T, i
| TMono_stp T1 T2 i j:
    Γ u⊢ₜ T1, i <: T2, j →
    Γ u⊢ₜ T1, S i <: T2, S j

(* "Logical" connectives *)
| Top_stp i T :
    is_unstamped_ty (length Γ) T →
    Γ u⊢ₜ T, i <: TTop, i
| Bot_stp i T :
    is_unstamped_ty (length Γ) T →
    Γ u⊢ₜ TBot, i <: T, i
| TAnd1_stp T1 T2 i:
    is_unstamped_ty (length Γ) T1 →
    is_unstamped_ty (length Γ) T2 →
    Γ u⊢ₜ TAnd T1 T2, i <: T1, i
| TAnd2_stp T1 T2 i:
    is_unstamped_ty (length Γ) T1 →
    is_unstamped_ty (length Γ) T2 →
    Γ u⊢ₜ TAnd T1 T2, i <: T2, i
| TAnd_stp T U1 U2 i j:
    Γ u⊢ₜ T, i <: U1, j →
    Γ u⊢ₜ T, i <: U2, j →
    Γ u⊢ₜ T, i <: TAnd U1 U2, j
| TOr1_stp T1 T2 i:
    is_unstamped_ty (length Γ) T1 →
    is_unstamped_ty (length Γ) T2 →
    Γ u⊢ₜ T1, i <: TOr T1 T2, i
| TOr2_stp T1 T2 i:
    is_unstamped_ty (length Γ) T1 →
    is_unstamped_ty (length Γ) T2 →
    Γ u⊢ₜ T2, i <: TOr T1 T2, i
| TOr_stp T1 T2 U i j:
    Γ u⊢ₜ T1, i <: U, j →
    Γ u⊢ₜ T2, i <: U, j →
    Γ u⊢ₜ TOr T1 T2, i <: U, j

(* Type selections *)
| SelU_stp p L {l U i}:
    Γ u⊢ₚ p : TTMem l L U, i →
    Γ u⊢ₜ TSel p l, i <: TLater U, i
| LSel_stp p U {l L i}:
    Γ u⊢ₚ p : TTMem l L U, i →
    Γ u⊢ₜ TLater L, i <: TSel p l, i

(* TODO: figure out if the drugs I had when I wrote these rules were good or bad. *)
(* | SelU_stp l L U p i j: *)
(*     Γ u⊢ₚ p : TTMem l L U, i → *)
(*     Γ u⊢ₜ TSel p l, j <: U, S (i + j) *)
(* | LSel_stp l L U p i j: *)
(*     Γ u⊢ₚ p : TTMem l L U, i → *)
(*     Γ u⊢ₜ L, S (i + j) <: TSel p l, j *)

(* Subtyping for recursive types. Congruence, and opening in both directions. *)
| Mu_stp_mu T1 T2 i:
    (iterate TLater i T1 :: Γ) u⊢ₜ T1, i <: T2, i →
    is_unstamped_ty (S (length Γ)) T1 →
    Γ u⊢ₜ TMu T1, i <: TMu T2, i
| Mu_stp T i:
    is_unstamped_ty (length Γ) T →
    Γ u⊢ₜ TMu T.|[ren (+1)], i <: T, i
| Stp_mu T i:
    is_unstamped_ty (length Γ) T →
    Γ u⊢ₜ T, i <: TMu T.|[ren (+1)], i

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types.
 "Cov" stands for covariance, "Con" for contravariance. *)
(* Needed? Maybe drop later instead? *)
| TLaterCov_stp T1 T2 i j:
    Γ u⊢ₜ T1, S i <: T2, S j →
    Γ u⊢ₜ TLater T1, i <: TLater T2, j
| TAllConCov_stp T1 T2 U1 U2 i:
    Γ u⊢ₜ TLater T2, i <: TLater T1, i →
    iterate TLater (S i) T2.|[ren (+1)] :: Γ u⊢ₜ TLater U1, i <: TLater U2, i →
    is_unstamped_ty (length Γ) T2 →
    Γ u⊢ₜ TAll T1 U1, i <: TAll T2 U2, i
| TVMemCov_stp T1 T2 i l:
    Γ u⊢ₜ T1, i <: T2, i →
    Γ u⊢ₜ TVMem l T1, i <: TVMem l T2, i
| TTMemConCov_stp L1 L2 U1 U2 i l:
    Γ u⊢ₜ TLater L2, i <: TLater L1, i →
    Γ u⊢ₜ TLater U1, i <: TLater U2, i →
    Γ u⊢ₜ TTMem l L1 U1, i <: TTMem l L2 U2, i
  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
| TAllDistr_stp T U1 U2 i:
    is_unstamped_ty (length Γ) T →
    is_unstamped_ty (S (length Γ)) U1 →
    is_unstamped_ty (S (length Γ)) U2 →
    Γ u⊢ₜ TAnd (TAll T U1) (TAll T U2), i <: TAll T (TAnd U1 U2), i
| TVMemDistr_stp l T1 T2 i:
    is_unstamped_ty (length Γ) T1 →
    is_unstamped_ty (length Γ) T2 →
    Γ u⊢ₜ TAnd (TVMem l T1) (TVMem l T2), i <: TVMem l (TAnd T1 T2), i
| TTMemDistr_strp l L U1 U2 i:
    is_unstamped_ty (length Γ) L →
    is_unstamped_ty (length Γ) U1 →
    is_unstamped_ty (length Γ) U2 →
    Γ u⊢ₜ TAnd (TTMem l L U1) (TTMem l L U2), i <: TTMem l L (TAnd U1 U2), i
where "Γ u⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).

(* Make [T] first argument: Hide Γ for e.g. typing examples. *)
Global Arguments dty_typed {Γ} T _ _ _ _ _ _ _ : assert.

Scheme unstamped_typed_mut_ind := Induction for typed Sort Prop
with   unstamped_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   unstamped_dm_typed_mut_ind := Induction for dm_typed Sort Prop
with   unstamped_path_typed_mut_ind := Induction for path_typed Sort Prop
with   unstamped_subtype_mut_ind := Induction for subtype Sort Prop.

Combined Scheme unstamped_typing_mut_ind from unstamped_typed_mut_ind, unstamped_dms_typed_mut_ind, unstamped_dm_typed_mut_ind,
  unstamped_path_typed_mut_ind, unstamped_subtype_mut_ind.

Hint Constructors typed dms_typed dm_typed path_typed subtype : core.
Remove Hints Trans_stp : core.
Hint Extern 10 => try_once Trans_stp : core.

Lemma unstamped_path_root_is_var Γ p T i:
  Γ u⊢ₚ p : T, i → ∃ x, path_root p = var_vl x.
Proof. by elim; intros; cbn; eauto 2. Qed.

Lemma dtysem_not_utyped Γ V l d T :
  Γ |d V u⊢{ l := d } : T → ∀ σ s, d ≠ dtysem σ s.
Proof. by case. Qed.
