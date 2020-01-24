From D.Dot.syn Require Export syn path_repl.
From D.Dot.stamping Require Export stampingDefsCore.
From D.Dot.lr Require Import unary_lr.
From D Require Import swap_later_impl.

Implicit Types (L T U V : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty).
Implicit Types (g : stys).

Reserved Notation "Γ v⊢ₜ[ g ] e : T"
  (at level 74, e, T at next level,
  format "'[' '[' Γ ']'  '/' v⊢ₜ[  g  ]  '[' e ']'  :  '[' T ']' ']'").
Reserved Notation "Γ v⊢ₚ[ g  ] p : T , i" (at level 74, p, T, i at next level).
Reserved Notation "Γ |d V v⊢[ g ]{ l := d } : T "
(* Reserved Notation "Γ |d V v⊢[ g  ]{ l := d  } : T " *)
  (at level 74, l, d, T, V at next level,
   format "'[' '[' Γ  |d  V  ']' '/' '[' v⊢[  g  ]{  l  :=  d  } ']' :  '[' T ']' ']'").
Reserved Notation "Γ |ds V v⊢[ g ] ds : T"
  (at level 74, ds, T, V at next level,
  format "'[' '[' Γ  |ds  V  ']' '/' v⊢[  g  ]  '[' ds ']'  :  T ']'" ).
Reserved Notation "Γ v⊢ₜ[ g  ] T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

(**
Judgments for typing, subtyping, path and definition typing.
*)
Inductive typed Γ g : tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a value . *)
| Appv_typed e1 v2 T1 T2:
    Γ v⊢ₜ[ g ] e1: TAll T1 T2 →                        Γ v⊢ₜ[ g ] tv v2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ v⊢ₜ[ g ] tapp e1 (tv v2) : T2.|[v2/]

| App_path_typed p2 e1 T1 T2 T2':
    T2 .Tp[ p2 /]~ T2' →
    is_stamped_ty (length Γ) g T2' →
    Γ v⊢ₜ[ g ] e1: TAll T1 T2 →
    Γ v⊢ₚ[ g ] p2 : T1, 0 →
    (*────────────────────────────────────────────────────────────*)
    Γ v⊢ₜ[ g ] tapp e1 (path2tm p2) : T2'
(** Non-dependent application; allowed for any argument. *)
| App_typed e1 e2 T1 T2:
    Γ v⊢ₜ[ g ] e1: TAll T1 (shift T2) →      Γ v⊢ₜ[ g ] e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ v⊢ₜ[ g ] tapp e1 e2 : T2
| Proj_typed e T l:
    Γ v⊢ₜ[ g ] e : TVMem l T →
    (*─────────────────────────*)
    Γ v⊢ₜ[ g ] tproj e l : T
| TMuE_typed v T:
    Γ v⊢ₜ[ g ] tv v: TMu T →
    (*──────────────────────*)
    Γ v⊢ₜ[ g ] tv v: T.|[v/]
(** Introduction forms *)
| Lam_typed e T1 T2:
    (* T1 :: Γ v⊢ₜ[ g ] e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    is_stamped_ty (length Γ) g T1 →
    shift T1 :: Γ v⊢ₜ[ g ] e : T2 →
    (*─────────────────────────*)
    Γ v⊢ₜ[ g ] tv (vabs e) : TAll T1 T2
| VObj_typed ds T:
    Γ |ds T v⊢[ g ] ds: T →
    is_stamped_ty (S (length Γ)) g T →
    (*──────────────────────*)
    Γ v⊢ₜ[ g ] tv (vobj ds): TMu T
| TMuI_typed v T:
    Γ v⊢ₜ[ g ] tv v: T.|[v/] →
    (*──────────────────────*)
    Γ v⊢ₜ[ g ] tv v: TMu T
| Nat_typed n:
    Γ v⊢ₜ[ g ] tv (vnat n): TNat

(** "General" rules *)
| Var_typed x T :
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ v⊢ₜ[ g ] tv (var_vl x) : shiftN x T
| Subs_typed e T1 T2 i :
    Γ v⊢ₜ[ g ] T1, 0 <: T2, i → Γ v⊢ₜ[ g ] e : T1 →
    (*───────────────────────────────*)
    Γ v⊢ₜ[ g ] iterate tskip i e : T2
| Path_typed p T :
    Γ v⊢ₚ[ g ] p : T, 0 →
    (*───────────────────────────────*)
    Γ v⊢ₜ[ g ] path2tm p : T
| Sem_typed e T :
    is_stamped_ty (length Γ) g T →
    is_stamped_tm (length Γ) g e →
    (∀ `{!dlangG Σ} `{!SwapPropI Σ}, Γ ⊨[ ⟦ g ⟧g ] e : T) →
    Γ v⊢ₜ[ g ] e : T
where "Γ v⊢ₜ[ g ] e : T " := (typed Γ g e T)
with dms_typed Γ g : ty → dms → ty → Prop :=
| dnil_typed V : Γ |ds V v⊢[ g ] [] : TTop
(* This demands definitions and members to be defined in aligned lists. *)
| dcons_typed V l d ds T1 T2:
    Γ |d V v⊢[ g ]{ l := d } : T1 →
    Γ |ds V v⊢[ g ] ds : T2 →
    dms_hasnt ds l →
    (*──────────────────────*)
    Γ |ds V v⊢[ g ] (l, d) :: ds : TAnd T1 T2
where "Γ |ds V v⊢[ g ] ds : T" := (dms_typed Γ g V ds T)
with dm_typed Γ g : ty → label → dm → ty → Prop :=
| dty_typed T V l L U s σ:
    T ~[ S (length Γ) ] (g, (s, σ)) →
    Forall (is_stamped_vl (S (length Γ)) g) σ →
    TLater V :: Γ v⊢ₜ[ g ] TLater L, 0 <: TLater T, 0 →
    TLater V :: Γ v⊢ₜ[ g ] TLater T, 0 <: TLater U, 0 →
    Γ |d V v⊢[ g ]{ l := dtysem σ s } : TTMem l L U
| dvabs_typed V T1 T2 e l:
    is_stamped_ty (S (length Γ)) g T1 →
    shift T1 :: V :: Γ v⊢ₜ[ g ] e : T2 →
    Γ |d V v⊢[ g ]{ l := dpt (pv (vabs e)) } : TVMem l (TAll T1 T2)
| dpt_pv_typed V l v T:
    TLater V :: Γ v⊢ₜ[ g ] tv v : T →
    Γ |d V v⊢[ g ]{ l := dpt (pv v) } : TVMem l T
| dpath_typed V l p T:
    TLater V :: Γ v⊢ₚ[ g ] p : T, 0 →
    Γ |d V v⊢[ g ]{ l := dpt p } : TVMem l T
| dnew_typed V l T ds:
    TLater V :: Γ |ds TAnd T (TSing (pself (pv (ids 1)) l)) v⊢[ g ] ds : T →
    is_stamped_ty (S (S (length Γ))) g T →
    Γ |d V v⊢[ g ]{ l := dpt (pv (vobj ds)) } : TVMem l (TMu T)
| dpt_sub_typed V T1 T2 p l:
    TLater V :: Γ v⊢ₜ[ g ] T1, 0 <: T2, 0 →
    Γ |d V v⊢[ g ]{ l := dpt p } : TVMem l T1 →
    Γ |d V v⊢[ g ]{ l := dpt p } : TVMem l T2
where "Γ |d V v⊢[ g ]{ l := d  } : T" := (dm_typed Γ g V l d T)
with path_typed Γ g : path → ty → nat → Prop :=
| pv_typed v T:
    Γ v⊢ₜ[ g ] tv v : T →
    Γ v⊢ₚ[ g ] pv v : T, 0
| pv_dlater p T i:
    Γ v⊢ₚ[ g ] p : TLater T, i →
    Γ v⊢ₚ[ g ] p : T, S i
(* Mnemonic: Path from SELecting a Field *)
| pself_typed p T i l:
    Γ v⊢ₚ[ g ] p : TVMem l T, i →
    Γ v⊢ₚ[ g ] pself p l : T, i
| p_subs_typed p T1 T2 i j :
    Γ v⊢ₜ[ g ] T1, i <: T2, i + j →
    Γ v⊢ₚ[ g ] p : T1, i →
    (*───────────────────────────────*)
    Γ v⊢ₚ[ g ] p : T2, i + j
| p_mu_i_typed p T {T' i} :
    T .Tp[ p /]~ T' →
    is_stamped_ty (S (length Γ)) g T →
    Γ v⊢ₚ[ g ] p : T', i →
    Γ v⊢ₚ[ g ] p : TMu T, i
| p_mu_e_typed p T {T' i} :
    T .Tp[ p /]~ T' →
    is_stamped_ty (length Γ) g T' →
    Γ v⊢ₚ[ g ] p : TMu T, i →
    Γ v⊢ₚ[ g ] p : T', i
| pself_inv_typed p T i l:
    Γ v⊢ₚ[ g ] pself p l : T, i →
    (*─────────────────────────*)
    Γ v⊢ₚ[ g ] p : TVMem l T, i
| psingleton_refl_typed T p i :
    Γ v⊢ₚ[ g ] p : T, i →
    Γ v⊢ₚ[ g ] p : TSing p, i
| psingleton_inv_typed p q i:
    Γ v⊢ₚ[ g ] p : TSing q, i →
    is_stamped_path (length Γ) g q →
    Γ v⊢ₚ[ g ] q : TTop, i
| psingleton_trans p q T i:
    Γ v⊢ₚ[ g ] p : TSing q, i →
    Γ v⊢ₚ[ g ] q : T, i →
    Γ v⊢ₚ[ g ] p : T, i
| psingleton_elim T p q l i:
    Γ v⊢ₚ[ g ] p : TSing q, i →
    Γ v⊢ₚ[ g ] pself q l : T, i →
    Γ v⊢ₚ[ g ] pself p l : TSing (pself q l), i
| sem_ptyped p T i :
    is_stamped_ty (length Γ) g T →
    is_stamped_path (length Γ) g p →
    (∀ `{!dlangG Σ} `{!SwapPropI Σ}, Γ ⊨p[ ⟦ g ⟧g ] p : T, i) →
    Γ v⊢ₚ[ g ] p : T, i
where "Γ v⊢ₚ[ g ] p : T , i" := (path_typed Γ g p T i)
(* Γ v⊢ₜ[ g ] T1, i1 <: T2, i2 means that TLater^i1 T1 <: TLater^i2 T2. *)
with subtype Γ g : ty → nat → ty → nat → Prop :=
| Refl_stp i T :
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] T, i <: T, i
| Trans_stp i2 T2 {i1 i3 T1 T3}:
    Γ v⊢ₜ[ g ] T1, i1 <: T2, i2 →
    Γ v⊢ₜ[ g ] T2, i2 <: T3, i3 →
    Γ v⊢ₜ[ g ] T1, i1 <: T3, i3
| TLaterL_stp i T:
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] TLater T, i <: T, S i
| TLaterR_stp i T:
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] T, S i <: TLater T, i

(* "Structural" rules about indexes *)
| TAddLater_stp T i:
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] T, i <: TLater T, i
| TMono_stp T1 T2 i j:
    Γ v⊢ₜ[ g ] T1, i <: T2, j →
    Γ v⊢ₜ[ g ] T1, S i <: T2, S j

(* "Logical" connectives *)
| Top_stp i T :
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] T, i <: TTop, i
| Bot_stp i T :
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] TBot, i <: T, i
| TAnd1_stp T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ v⊢ₜ[ g ] TAnd T1 T2, i <: T1, i
| TAnd2_stp T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ v⊢ₜ[ g ] TAnd T1 T2, i <: T2, i
| TAnd_stp T U1 U2 i j:
    Γ v⊢ₜ[ g ] T, i <: U1, j →
    Γ v⊢ₜ[ g ] T, i <: U2, j →
    Γ v⊢ₜ[ g ] T, i <: TAnd U1 U2, j
| TOr1_stp T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ v⊢ₜ[ g ] T1, i <: TOr T1 T2, i
| TOr2_stp T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ v⊢ₜ[ g ] T2, i <: TOr T1 T2, i
| TOr_stp T1 T2 U i j:
    Γ v⊢ₜ[ g ] T1, i <: U, j →
    Γ v⊢ₜ[ g ] T2, i <: U, j →
    Γ v⊢ₜ[ g ] TOr T1 T2, i <: U, j

(* Type selections *)
| SelU_stp p L {l U i}:
    Γ v⊢ₚ[ g ] p : TTMem l L U, i →
    Γ v⊢ₜ[ g ] TSel p l, i <: TLater U, i
| LSel_stp p U {l L i}:
    Γ v⊢ₚ[ g ] p : TTMem l L U, i →
    Γ v⊢ₜ[ g ] TLater L, i <: TSel p l, i
| PSub_singleton_stp p q {i T1 T2}:
    T1 ~Tp[ p := q ]* T2 →
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ v⊢ₚ[ g ] p : TSing q, i →
    Γ v⊢ₜ[ g ] T1, i <: T2, i
| PSym_singleton_stp T {p q i}:
    Γ v⊢ₚ[ g ] p : T, i →
    Γ v⊢ₜ[ g ] TSing p, i <: TSing q, i →
    Γ v⊢ₜ[ g ] TSing q, i <: TSing p, i
| PSelf_singleton_stp {p T i} :
    Γ v⊢ₚ[ g ] p : T, i →
    Γ v⊢ₜ[ g ] TSing p, i <: T, i

(* TODO: figure out if the drugs I had when I wrote these rules were good or bad. *)
(* | SelU_stp l L U p i j: *)
(*     Γ v⊢ₚ[ g ] p : TTMem l L U, i → *)
(*     Γ v⊢ₜ[ g ] TSel p l, j <: U, S (i + j) *)
(* | LSel_stp l L U p i j: *)
(*     Γ v⊢ₚ[ g ] p : TTMem l L U, i → *)
(*     Γ v⊢ₜ[ g ] L, S (i + j) <: TSel p l, j *)

(* Subtyping for recursive types. Congruence, and opening in both directions. *)
| Mu_stp_mu T1 T2 i j:
    (iterate TLater i T1 :: Γ) v⊢ₜ[ g ] T1, i <: T2, j →
    is_stamped_ty (S (length Γ)) g T1 →
    Γ v⊢ₜ[ g ] TMu T1, i <: TMu T2, j
| Mu_stp T i:
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] TMu (shift T), i <: T, i
| Stp_mu T i:
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] T, i <: TMu (shift T), i

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types.
 "Cov" stands for covariance, "Con" for contravariance. *)
(* Needed? Maybe drop later instead? *)
| TLaterCov_stp T1 T2 i j:
    Γ v⊢ₜ[ g ] T1, S i <: T2, S j →
    Γ v⊢ₜ[ g ] TLater T1, i <: TLater T2, j
| TAllConCov_stp T1 T2 U1 U2 i:
    Γ v⊢ₜ[ g ] TLater T2, i <: TLater T1, i →
    iterate TLater (S i) (shift T2) :: Γ v⊢ₜ[ g ] TLater U1, i <: TLater U2, i →
    is_stamped_ty (length Γ) g T2 →
    Γ v⊢ₜ[ g ] TAll T1 U1, i <: TAll T2 U2, i
| TVMemCov_stp T1 T2 i l:
    Γ v⊢ₜ[ g ] T1, i <: T2, i →
    Γ v⊢ₜ[ g ] TVMem l T1, i <: TVMem l T2, i
| TTMemConCov_stp L1 L2 U1 U2 i l:
    Γ v⊢ₜ[ g ] TLater L2, i <: TLater L1, i →
    Γ v⊢ₜ[ g ] TLater U1, i <: TLater U2, i →
    Γ v⊢ₜ[ g ] TTMem l L1 U1, i <: TTMem l L2 U2, i
  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
| TAllDistr_stp T U1 U2 i:
    is_stamped_ty (length Γ) g T →
    is_stamped_ty (S (length Γ)) g U1 →
    is_stamped_ty (S (length Γ)) g U2 →
    Γ v⊢ₜ[ g ] TAnd (TAll T U1) (TAll T U2), i <: TAll T (TAnd U1 U2), i
| TVMemDistr_stp l T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ v⊢ₜ[ g ] TAnd (TVMem l T1) (TVMem l T2), i <: TVMem l (TAnd T1 T2), i
| TTMemDistr_stp l L U1 U2 i:
    is_stamped_ty (length Γ) g L →
    is_stamped_ty (length Γ) g U1 →
    is_stamped_ty (length Γ) g U2 →
    Γ v⊢ₜ[ g ] TAnd (TTMem l L U1) (TTMem l L U2), i <: TTMem l L (TAnd U1 U2), i
| Sem_stp T1 T2 i1 i2 :
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    (∀ `{!dlangG Σ} `{!SwapPropI Σ}, Γ ⊨[ ⟦ g ⟧g ] T1, i1 <: T2, i2) →
    Γ v⊢ₜ[ g ] T1, i1 <: T2, i2
where "Γ v⊢ₜ[ g ] T1 , i1 <: T2 , i2" := (subtype Γ g T1 i1 T2 i2).

(* Make [T] first argument: Hide [Γ] and [g] for e.g. typing examples. *)
Global Arguments dty_typed {Γ g} T _ _ _ _ _ _ _ _ _ _ : assert.

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

Ltac typconstructor_check :=
  lazymatch goal with
  | |- context [ dlang_inst.dlangG ] => fail "Only applicable rule is reflection"
  | _ => idtac
  end.
Ltac typconstructor :=
  match goal with
  | |- typed _ _ _ _ => constructor
  | |- dms_typed _ _ _ _ _ => constructor
  | |- dm_typed _ _ _ _ _ _ => constructor
  | |- path_typed _ _ _ _ _ => constructor
  | |- subtype _ _ _ _ _ _ => constructor
  end; typconstructor_check.
