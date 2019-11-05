From D.Dot Require Export syn stampingDefsCore.

Reserved Notation "Γ ⊢ₜ e : T"
  (at level 74, e, T at next level,
  format "'[' '[' Γ ']'  '/' ⊢ₜ  '[' e ']'  :  '[' T ']' ']'").
Reserved Notation "Γ ⊢ₚ p : T , i" (at level 74, p, T, i at next level).
Reserved Notation "Γ |d V ⊢{ l := d } : T "
(* Reserved Notation "Γ |d V ⊢{ l := d  } : T " *)
  (at level 74, l, d, T, V at next level,
   format "'[' '[' Γ  |d  V  ']' '/' '[' ⊢{  l  :=  d  } ']' :  '[' T ']' ']'").
Reserved Notation "Γ |ds V ⊢ ds : T"
  (at level 74, ds, T, V at next level,
  format "'[' '[' Γ  |ds  V  ']' '/' ⊢  '[' ds ']'  :  T ']'" ).
Reserved Notation "Γ ⊢ₜ T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

Implicit Types (L T U V : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty) (g : stys).

Section syntyping.
  Context `{hasStampTable: stampTable}.
(**
Judgments for typing, subtyping, path and definition typing.
*)
Inductive typed Γ : tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a value . *)
| Appv_typed e1 v2 T1 T2:
    Γ ⊢ₜ e1: TAll T1 T2 →                        Γ ⊢ₜ tv v2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ ⊢ₜ tapp e1 (tv v2) : T2.|[v2/]
(** Non-dependent application; allowed for any argument. *)
| App_typed e1 e2 T1 T2:
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
| Lam_typed e T1 T2:
    (* T1 :: Γ ⊢ₜ e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    is_stamped_ty (length Γ) getStampTable T1 →
    T1.|[ren (+1)] :: Γ ⊢ₜ e : T2 →
    (*─────────────────────────*)
    Γ ⊢ₜ tv (vabs e) : TAll T1 T2
| VObj_typed ds T:
    Γ |ds T ⊢ ds: T →
    is_stamped_ty (S (length Γ)) getStampTable T →
    (*──────────────────────*)
    Γ ⊢ₜ tv (vobj ds): TMu T
| TMuI_typed v T:
    Γ ⊢ₜ tv v: T.|[v/] →
    (*──────────────────────*)
    Γ ⊢ₜ tv v: TMu T
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
(* A bit surprising this is needed, but appears in the DOT papers, and this is
   only admissible if t has a type U that is a proper subtype of TAnd T1 T2. *)
| TAndI_typed T1 T2 v:
    Γ ⊢ₜ tv v : T1 →
    Γ ⊢ₜ tv v : T2 →
    Γ ⊢ₜ tv v : TAnd T1 T2
where "Γ ⊢ₜ e : T " := (typed Γ e T)
with dms_typed Γ : ty → dms → ty → Prop :=
| dnil_typed V : Γ |ds V ⊢ [] : TTop
(* This demands definitions and members to be defined in aligned lists. *)
| dcons_typed V l d ds T1 T2:
    Γ |d V ⊢{ l := d } : T1 →
    Γ |ds V ⊢ ds : T2 →
    dms_hasnt ds l →
    (*──────────────────────*)
    Γ |ds V ⊢ (l, d) :: ds : TAnd T1 T2
where "Γ |ds V ⊢ ds : T" := (dms_typed Γ V ds T)
with dm_typed Γ : ty → label → dm → ty → Prop :=
| dty_typed T V l L U s σ:
    T ~[ S (length Γ) ] (getStampTable, (s, σ)) →
    Forall (is_stamped_vl (S (length Γ)) getStampTable) σ →
    TLater V :: Γ ⊢ₜ TLater L, 0 <: TLater T, 0 →
    TLater V :: Γ ⊢ₜ TLater T, 0 <: TLater U, 0 →
    Γ |d V ⊢{ l := dtysem σ s } : TTMem l L U
| dvl_typed V l v T:
    TLater V :: Γ ⊢ₜ tv v : T →
    Γ |d V ⊢{ l := dvl v } : TVMem l T
where "Γ |d V ⊢{ l := d  } : T" := (dm_typed Γ V l d T)
with path_typed Γ : path → ty → nat → Prop :=
| pv_typed v T:
    Γ ⊢ₜ tv v : T →
    Γ ⊢ₚ pv v : T, 0
| pv_dlater p T i:
    Γ ⊢ₚ p : TLater T, i →
    Γ ⊢ₚ p : T, S i
(* Mnemonic: Path from SELecting a Field *)
| pself_typed p T i l:
    Γ ⊢ₚ p : TVMem l T, i →
    Γ ⊢ₚ pself p l : T, i
| p_subs_typed p T1 T2 i j :
    Γ ⊢ₜ T1, i <: T2, i + j →
    Γ ⊢ₚ p : T1, i →
    (*───────────────────────────────*)
    Γ ⊢ₚ p : T2, i + j
where "Γ ⊢ₚ p : T , i" := (path_typed Γ p T i)
(* Γ ⊢ₜ T1, i1 <: T2, i2 means that TLater^i1 T1 <: TLater^i2 T2. *)
with subtype Γ : ty → nat → ty → nat → Prop :=
| Refl_stp i T :
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ T, i <: T, i
| Trans_stp i2 T2 {i1 i3 T1 T3}:
    Γ ⊢ₜ T1, i1 <: T2, i2 →
    Γ ⊢ₜ T2, i2 <: T3, i3 →
    Γ ⊢ₜ T1, i1 <: T3, i3
| TLaterL_stp i T:
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ TLater T, i <: T, S i
| TLaterR_stp i T:
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ T, S i <: TLater T, i

(* "Structural" rules about indexes *)
| TAddLater_stp T i:
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ T, i <: TLater T, i
| TMono_stp T1 T2 i j:
    Γ ⊢ₜ T1, i <: T2, j →
    Γ ⊢ₜ T1, S i <: T2, S j

(* "Logical" connectives *)
| Top_stp i T :
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ T, i <: TTop, i
| Bot_stp i T :
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ TBot, i <: T, i
| TAnd1_stp T1 T2 i:
    is_stamped_ty (length Γ) getStampTable T1 →
    is_stamped_ty (length Γ) getStampTable T2 →
    Γ ⊢ₜ TAnd T1 T2, i <: T1, i
| TAnd2_stp T1 T2 i:
    is_stamped_ty (length Γ) getStampTable T1 →
    is_stamped_ty (length Γ) getStampTable T2 →
    Γ ⊢ₜ TAnd T1 T2, i <: T2, i
| TAnd_stp T U1 U2 i j:
    Γ ⊢ₜ T, i <: U1, j →
    Γ ⊢ₜ T, i <: U2, j →
    Γ ⊢ₜ T, i <: TAnd U1 U2, j
| TOr1_stp T1 T2 i:
    is_stamped_ty (length Γ) getStampTable T1 →
    is_stamped_ty (length Γ) getStampTable T2 →
    Γ ⊢ₜ T1, i <: TOr T1 T2, i
| TOr2_stp T1 T2 i:
    is_stamped_ty (length Γ) getStampTable T1 →
    is_stamped_ty (length Γ) getStampTable T2 →
    Γ ⊢ₜ T2, i <: TOr T1 T2, i
| TOr_stp T1 T2 U i j:
    Γ ⊢ₜ T1, i <: U, j →
    Γ ⊢ₜ T2, i <: U, j →
    Γ ⊢ₜ TOr T1 T2, i <: U, j

(* Type selections *)
| SelU_stp p L {l U i}:
    Γ ⊢ₚ p : TTMem l L U, i →
    Γ ⊢ₜ TSel p l, i <: TLater U, i
| LSel_stp p U {l L i}:
    Γ ⊢ₚ p : TTMem l L U, i →
    Γ ⊢ₜ TLater L, i <: TSel p l, i

(* TODO: figure out if the drugs I had when I wrote these rules were good or bad. *)
(* | SelU_stp l L U p i j: *)
(*     Γ ⊢ₚ p : TTMem l L U, i → *)
(*     Γ ⊢ₜ TSel p l, j <: U, S (i + j) *)
(* | LSel_stp l L U p i j: *)
(*     Γ ⊢ₚ p : TTMem l L U, i → *)
(*     Γ ⊢ₜ L, S (i + j) <: TSel p l, j *)

(* Subtyping for recursive types. Congruence, and opening in both directions. *)
| Mu_stp_mu T1 T2 i:
    (iterate TLater i T1 :: Γ) ⊢ₜ T1, i <: T2, i →
    is_stamped_ty (S (length Γ)) getStampTable T1 →
    Γ ⊢ₜ TMu T1, i <: TMu T2, i
| Mu_stp T i:
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ TMu T.|[ren (+1)], i <: T, i
| Stp_mu T i:
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ T, i <: TMu T.|[ren (+1)], i

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types.
 "Cov" stands for covariance, "Con" for contravariance. *)
(* Needed? Maybe drop later instead? *)
| TLaterCov_stp T1 T2 i j:
    Γ ⊢ₜ T1, S i <: T2, S j →
    Γ ⊢ₜ TLater T1, i <: TLater T2, j
| TAllConCov_stp T1 T2 U1 U2 i:
    Γ ⊢ₜ TLater T2, i <: TLater T1, i →
    iterate TLater (S i) T2.|[ren (+1)] :: Γ ⊢ₜ TLater U1, i <: TLater U2, i →
    is_stamped_ty (length Γ) getStampTable T2 →
    Γ ⊢ₜ TAll T1 U1, i <: TAll T2 U2, i
| TVMemCov_stp T1 T2 i l:
    Γ ⊢ₜ T1, i <: T2, i →
    Γ ⊢ₜ TVMem l T1, i <: TVMem l T2, i
| TTMemConCov_stp L1 L2 U1 U2 i l:
    Γ ⊢ₜ TLater L2, i <: TLater L1, i →
    Γ ⊢ₜ TLater U1, i <: TLater U2, i →
    Γ ⊢ₜ TTMem l L1 U1, i <: TTMem l L2 U2, i
  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
| TAllDistr_stp T U1 U2 i:
    is_stamped_ty (length Γ) getStampTable T →
    is_stamped_ty (S (length Γ)) getStampTable U1 →
    is_stamped_ty (S (length Γ)) getStampTable U2 →
    Γ ⊢ₜ TAnd (TAll T U1) (TAll T U2), i <: TAll T (TAnd U1 U2), i
| TVMemDistr_stp l T1 T2 i:
    is_stamped_ty (length Γ) getStampTable T1 →
    is_stamped_ty (length Γ) getStampTable T2 →
    Γ ⊢ₜ TAnd (TVMem l T1) (TVMem l T2), i <: TVMem l (TAnd T1 T2), i
| TTMemDistr_strp l L U1 U2 i:
    is_stamped_ty (length Γ) getStampTable L →
    is_stamped_ty (length Γ) getStampTable U1 →
    is_stamped_ty (length Γ) getStampTable U2 →
    Γ ⊢ₜ TAnd (TTMem l L U1) (TTMem l L U2), i <: TTMem l L (TAnd U1 U2), i
where "Γ ⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).

  (* Make [T] first argument: Hide Γ for e.g. typing examples. *)
  Global Arguments dty_typed {Γ} T _ _ _ _ _ _ _ _ _ _ : assert.
End syntyping.

Notation "Γ ⊢ₜ e : T " := (typed Γ e T).
Notation "Γ |ds V ⊢ ds : T" := (dms_typed Γ V ds T).
Notation "Γ |d V ⊢{ l := d  } : T" := (dm_typed Γ V l d T).
Notation "Γ ⊢ₚ p : T , i" := (path_typed Γ p T i).
Notation "Γ ⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).

Scheme exp_stamped_typed_mut_ind := Induction for typed Sort Prop
with   exp_stamped_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   exp_stamped_dm_typed_mut_ind := Induction for dm_typed Sort Prop
with   exp_stamped_path_typed_mut_ind := Induction for path_typed Sort Prop.
(* with   subtype_mut_ind := Induction for subtype Sort Prop. *)

Combined Scheme exp_stamped_typing_mut_ind from exp_stamped_typed_mut_ind, exp_stamped_dms_typed_mut_ind,
  exp_stamped_dm_typed_mut_ind, exp_stamped_path_typed_mut_ind.

Scheme stamped_typed_mut_ind := Induction for typed Sort Prop
with   stamped_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   stamped_dm_typed_mut_ind := Induction for dm_typed Sort Prop
with   stamped_path_typed_mut_ind := Induction for path_typed Sort Prop
with   stamped_subtype_mut_ind := Induction for subtype Sort Prop.

Combined Scheme stamped_typing_mut_ind from stamped_typed_mut_ind, stamped_dms_typed_mut_ind,
  stamped_dm_typed_mut_ind, stamped_path_typed_mut_ind, stamped_subtype_mut_ind.
