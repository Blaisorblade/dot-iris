(** * Judgments defining gDOT "storeless" typing.
This is not our official type system and is not documented in the paper; it
is only used as part of safety proofs of "syntactically ill-typed" examples.
The name is historic.
Storeless typing resembles stamped typing, but used to allow arbitrary values
in paths.
*)
From D.Dot Require Export syn path_repl lr_syn_aux.
From D.Dot.typing Require Export typing_aux_defs old_subtyping.
From D.Dot.stamping Require Export core_stamping_defs.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (L T U : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty).
Implicit Types (g : stys).

(* Compatibility *)
Reserved Notation "Γ s⊢ₜ[ g  ] e : T" (at level 74, e, T at next level).
Reserved Notation "Γ s⊢ₚ[ g  ] p : T , i" (at level 74, p, T, i at next level).
Reserved Notation "Γ s⊢[ g  ]{ l := d  } : T " (at level 74, l, d, T at next level).
Reserved Notation "Γ s⊢ds[ g  ] ds : T" (at level 74, ds, T at next level).
Reserved Notation "Γ s⊢ₜ[ g  ] T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

Reserved Notation "Γ v⊢ₜ[ g ] e : T"
  (at level 74, e, T at next level,
  format "'[' '[' Γ ']'  '/' v⊢ₜ[  g  ]  '[' e ']'  :  '[' T ']' ']'").
Reserved Notation "Γ v⊢ₚ[ g  ] p : T , i" (at level 74, p, T, i at next level).
Reserved Notation "Γ v⊢[ g ]{ l := d } : T "
  (at level 74, l, d, T at next level,
   format "'[' '[' Γ  ']' '/' '[' v⊢[  g  ]{  l  :=  d  } ']' :  '[' T ']' ']'").
Reserved Notation "Γ v⊢ds[ g ] ds : T"
  (at level 74, ds, T at next level,
  format "'[' '[' Γ  ']' '/' v⊢ds[  g  ]  '[' ds ']'  :  T ']'" ).
Reserved Notation "Γ v⊢ₜ[ g  ] T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

Notation "Γ v⊢ₚ[ g ] p : T , i" := (path_typed Γ p T i).
Notation "Γ v⊢ₜ[ g ] T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).
Notation "Γ s⊢ₚ[ g ] p : T , i" := (path_typed Γ p T i).
Notation "Γ s⊢ₜ[ g ] T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).

(**
Judgments for typing, subtyping, path and definition typing.
*)
Inductive typed Γ g : tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a variable. *)
| iT_All_Ex e1 x2 T1 T2:
    Γ v⊢ₜ[ g ] e1: TAll T1 T2 →                        Γ v⊢ₜ[g] tv (var_vl x2) : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ v⊢ₜ[g] tapp e1 (tv (var_vl x2)) : T2.|[var_vl x2/]

| iT_All_Ex_p p2 e1 T1 T2 T2':
    T2 .Tp[ p2 /]~ T2' →
    is_stamped_ty (length Γ) g T2' →
    Γ v⊢ₜ[ g ] e1: TAll T1 T2 →
    Γ v⊢ₚ[ g ] p2 : T1, 0 →
    (*────────────────────────────────────────────────────────────*)
    Γ v⊢ₜ[ g ] tapp e1 (path2tm p2) : T2'
(** Non-dependent application; allowed for any argument. *)
| iT_All_E e1 e2 T1 T2:
    Γ v⊢ₜ[ g ] e1: TAll T1 (shift T2) →      Γ v⊢ₜ[ g ] e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ v⊢ₜ[ g ] tapp e1 e2 : T2
| iT_Obj_E e T l:
    Γ v⊢ₜ[ g ] e : TVMem l T →
    (*─────────────────────────*)
    Γ v⊢ₜ[ g ] tproj e l : T
| iT_Mu_E x T:
    Γ v⊢ₜ[ g ] tv (var_vl x): TMu T →
    (*──────────────────────*)
    Γ v⊢ₜ[ g ] tv (var_vl x): T.|[var_vl x/]
(** Introduction forms *)
| iT_All_I_Strong e T1 T2 Γ':
    ⊢G Γ >>▷* Γ' →
    is_stamped_ty (length Γ) g T1 →
    (* T1 :: Γ' v⊢ₜ[ g ] e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    shift T1 :: Γ' v⊢ₜ[ g ] e : T2 →
    (*─────────────────────────*)
    Γ v⊢ₜ[ g ] tv (vabs e) : TAll T1 T2
| iT_Obj_I ds T:
    Γ |L T v⊢ds[ g ] ds: T →
    is_stamped_ty (S (length Γ)) g T →
    (*──────────────────────*)
    Γ v⊢ₜ[ g ] tv (vobj ds): TMu T
| iT_Mu_I x T:
    Γ v⊢ₜ[ g ] tv (var_vl x): T.|[var_vl x/] →
    (*──────────────────────*)
    Γ v⊢ₜ[ g ] tv (var_vl x): TMu T

(** "General" rules *)
| iT_Var x T :
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ v⊢ₜ[ g ] tv (var_vl x) : shiftN x T
| iT_Sub e T1 T2 i :
    Γ v⊢ₜ[ g ] T1, 0 <: T2, i → Γ v⊢ₜ[ g ] e : T1 →
    (*───────────────────────────────*)
    Γ v⊢ₜ[ g ] iterate tskip i e : T2
| iT_Path p T :
    Γ v⊢ₚ[ g ] p : T, 0 →
    (*───────────────────────────────*)
    Γ v⊢ₜ[ g ] path2tm p : T

(** Primitives. *)
| iT_Un u e1 B1 Br (Hu : un_op_syntype u B1 Br) :
    Γ v⊢ₜ[ g ] e1 : TPrim B1 →
    Γ v⊢ₜ[ g ] tun u e1 : TPrim Br
| iT_Bin b e1 e2 B1 B2 Br (Hu : bin_op_syntype b B1 B2 Br) :
    Γ v⊢ₜ[ g ] e1 : TPrim B1 →
    Γ v⊢ₜ[ g ] e2 : TPrim B2 →
    Γ v⊢ₜ[ g ] tbin b e1 e2 : TPrim Br
| iT_If e e1 e2 T :
    Γ v⊢ₜ[ g ] e: TBool →
    Γ v⊢ₜ[ g ] e1 : T →
    Γ v⊢ₜ[ g ] e2 : T →
    Γ v⊢ₜ[ g ] tif e e1 e2 : T
where "Γ v⊢ₜ[ g ] e : T " := (typed Γ g e T)
with dms_typed Γ g : dms → ty → Prop :=
| iD_Nil : Γ v⊢ds[ g ] [] : TTop
(* This demands definitions and members to be defined in aligned lists. *)
| iD_Cons l d ds T1 T2:
    Γ v⊢[ g ]{ l := d } : T1 →
    Γ v⊢ds[ g ] ds : T2 →
    dms_hasnt ds l →
    (*──────────────────────*)
    Γ v⊢ds[ g ] (l, d) :: ds : TAnd T1 T2
where "Γ v⊢ds[ g ] ds : T" := (dms_typed Γ g ds T)
with dm_typed Γ g : label → dm → ty → Prop :=
| iD_Typ_Abs T l L U s σ:
    T ~[ length Γ ] (g, (s, σ)) →
    is_stamped_σ (length Γ) g σ →
    Γ v⊢ₜ[ g ] L, 0 <: TLater T, 0 →
    Γ v⊢ₜ[ g ] TLater T, 0 <: U, 0 →
    Γ v⊢[ g ]{ l := dtysem σ s } : TTMem l L U
| iD_Val l v T:
    Γ v⊢ₜ[ g ] tv v : T →
    Γ v⊢[ g ]{ l := dpt (pv v) } : TVMem l T
| iD_Path l p T:
    Γ v⊢ₚ[ g ] p : T, 0 →
    Γ v⊢[ g ]{ l := dpt p } : TVMem l T
| iD_Val_New l T ds:
    TAnd (TLater T) (TSing (pself (pv (ids 1)) l)) :: Γ v⊢ds[ g ] ds : T →
    is_stamped_ty (S (length Γ)) g T →
    Γ v⊢[ g ]{ l := dpt (pv (vobj ds)) } : TVMem l (TMu T)
| iD_Path_Sub T1 T2 p l:
    Γ v⊢ₜ[ g ] T1, 0 <: T2, 0 →
    Γ v⊢[ g ]{ l := dpt p } : TVMem l T1 →
    Γ v⊢[ g ]{ l := dpt p } : TVMem l T2
where "Γ v⊢[ g ]{ l := d  } : T" := (dm_typed Γ g l d T).

(* Compatibility *)
Notation "Γ s⊢ₜ[ g ] e : T " := (typed Γ g e T).
Notation "Γ s⊢ds[ g ] ds : T" := (dms_typed Γ g ds T).
Notation "Γ s⊢[ g ]{ l := d  } : T" := (dm_typed Γ g l d T).

(* Make [T] first argument: Hide [Γ] and [g] for e.g. typing examples. *)
Global Arguments iD_Typ_Abs {Γ g} T _ _ _ _ _ _ _ _ _ : assert.

Scheme exp_stamped_typed_mut_ind := Induction for typed Sort Prop
with   exp_stamped_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   exp_stamped_dm_typed_mut_ind := Induction for dm_typed Sort Prop.

Combined Scheme exp_storeless_typing_mut_ind from exp_stamped_typed_mut_ind, exp_stamped_dms_typed_mut_ind,
  exp_stamped_dm_typed_mut_ind.

Scheme stamped_typed_mut_ind := Induction for typed Sort Prop
with   stamped_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   stamped_dm_typed_mut_ind := Induction for dm_typed Sort Prop.
Scheme stamped_path_typed_mut_ind := Induction for path_typed Sort Prop
with   stamped_subtype_mut_ind := Induction for subtype Sort Prop.

Combined Scheme storeless_typing_mut_ind from stamped_typed_mut_ind, stamped_dms_typed_mut_ind,
  stamped_dm_typed_mut_ind.
Combined Scheme pure_storeless_typing_mut_ind from stamped_path_typed_mut_ind,
  stamped_subtype_mut_ind.

(** ** A few derived rules, and some automation to use them in examples. *)

Hint Constructors typed subtype dms_typed dm_typed path_typed : core.
Remove Hints iSub_Trans : core.
Hint Extern 10 => try_once iSub_Trans : core.

Lemma iT_Path' Γ v T g
  (Ht : Γ v⊢ₚ[ g ] pv v : T, 0) : Γ v⊢ₜ[ g ] tv v : T.
Proof. exact: (iT_Path _ (p := pv _)). Qed.

Lemma iT_Nat_I Γ g n : Γ v⊢ₜ[ g ] tv (vint n): TInt.
Proof. apply iT_Path'; constructor. Qed.

Lemma iT_Bool_I Γ g b : Γ v⊢ₜ[ g ] tv (vbool b): TBool.
Proof. apply iT_Path'; constructor. Qed.

Lemma iT_All_I Γ e T1 T2 g:
  is_stamped_ty (length Γ) g T1 →
  shift T1 :: Γ v⊢ₜ[ g ] e : T2 →
  (*─────────────────────────*)
  Γ v⊢ₜ[ g ] tv (vabs e) : TAll T1 T2.
Proof. apply iT_All_I_Strong. ietp_weaken_ctx. Qed.

Lemma iT_All_I_strip1 Γ e V T1 T2 g:
  is_stamped_ty (S (length Γ)) g T1 →
  shift T1 :: V :: Γ v⊢ₜ[ g ] e : T2 →
  (*─────────────────────────*)
  Γ |L V v⊢ₜ[ g ] tv (vabs e) : TAll T1 T2.
Proof.
  intros. apply (iT_All_I_Strong (Γ' := (V :: Γ))) => //.
  rewrite /defCtxCons/=; ietp_weaken_ctx.
Qed.

Lemma iD_All Γ V T1 T2 e l g:
  is_stamped_ty (S (length Γ)) g T1 →
  shift T1 :: V :: Γ v⊢ₜ[ g ] e : T2 →
  Γ |L V v⊢[ g ]{ l := dpt (pv (vabs e)) } : TVMem l (TAll T1 T2).
Proof. by intros; apply iD_Val, iT_All_I_strip1. Qed.

Ltac typconstructor :=
  match goal with
  | |- typed      ?Γ _ _ _ => first [
    apply iT_All_I_strip1 | apply iT_All_I |
    apply iT_Nat_I | apply iT_Bool_I |
    constructor]
  | |- dms_typed  ?Γ _ _ _ => constructor
  | |- dm_typed   ?Γ _ _ _ _ => first [apply iD_All | constructor]
  | |- path_typed ?Γ _ _ _ => first [subtypconstructor]
  | |- subtype    ?Γ _ _ _ _ => subtypconstructor
  end.
