(** * Judgments defining gDOT unstamped typing.

We show that unstamped typing derivations from here can
be converted to stamped derivations of this typing judgment, in lemma
[stamp_typing_mut].

This judgment allowing only variables in paths, and not arbitrary values.
*)
From D Require Import tactics.
From D.Dot Require Export syn path_repl lr_syn_aux.
From D.Dot Require Export typing_aux_defs old_subtyping.
From D.Dot Require Export core_stamping_defs.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (L T U : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty).

Reserved Notation "Γ u⊢ₜ e : T" (at level 74, e, T at next level).
Reserved Notation "Γ u⊢{ l := d  } : T" (at level 74, l, d, T at next level).
Reserved Notation "Γ u⊢ds ds : T" (at level 74, ds, T at next level).

(** ** Judgments for typing, subtyping, path and definition typing. *)
Inductive typed Γ : tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a path. *)
| iT_All_E_p p2 e1 T1 T2:
    is_unstamped_ty' (length Γ).+1 T2 →
    (* T2 .Tp[ p2 /]~ T2' → *)
    Γ u⊢ₜ e1: TAll T1 T2 →
    Γ u⊢ₚ p2 : T1, 0 →
    (*────────────────────────────────────────────────────────────*)
    Γ u⊢ₜ tapp e1 (path2tm p2) : T2 .Tp[ p2 /]
(** Non-dependent application; allowed for any argument. *)
| iT_All_E e1 e2 T1 T2:
    Γ u⊢ₜ e1: TAll T1 (shift T2) →      Γ u⊢ₜ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ u⊢ₜ tapp e1 e2 : T2
| iT_Obj_E e T l:
    Γ u⊢ₜ e : TVMem l T →
    (*─────────────────────────*)
    Γ u⊢ₜ tproj e l : T
(** Introduction forms *)
| iT_All_I_Strong e T1 T2 Γ':
    ⊢G Γ >>▷* Γ' →
    (* T1 :: Γ' u⊢ₜ e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    shift T1 :: Γ' u⊢ₜ e : T2 →
    (*─────────────────────────*)
    Γ u⊢ₜ tv (vabs e) : TAll T1 T2
| iT_Obj_I ds T:
    Γ |L T u⊢ds ds: T →
    (*──────────────────────*)
    Γ u⊢ₜ tv (vobj ds): TMu T

(** "General" rules *)
| iT_ISub e T1 T2 i :
    Γ u⊢ₜ T1, 0 <: T2, i → Γ u⊢ₜ e : T1 →
    (*───────────────────────────────*)
    Γ u⊢ₜ iterate tskip i e : T2
| iT_Path p T :
    Γ u⊢ₚ p : T, 0 →
    (*───────────────────────────────*)
    Γ u⊢ₜ path2tm p : T

(** Primitives. *)
| iT_Un u e1 B1 Br (Hu : un_op_syntype u B1 Br) :
    Γ u⊢ₜ e1 : TPrim B1 →
    Γ u⊢ₜ tun u e1 : TPrim Br
| iT_Bin b e1 e2 B1 B2 Br (Hu : bin_op_syntype b B1 B2 Br) :
    Γ u⊢ₜ e1 : TPrim B1 →
    Γ u⊢ₜ e2 : TPrim B2 →
    Γ u⊢ₜ tbin b e1 e2 : TPrim Br
| iT_If e e1 e2 T :
    Γ u⊢ₜ e: TBool →
    Γ u⊢ₜ e1 : T →
    Γ u⊢ₜ e2 : T →
    Γ u⊢ₜ tif e e1 e2 : T
where "Γ u⊢ₜ e : T " := (typed Γ e T)
with dms_typed Γ : dms → ty → Prop :=
| iD_Nil : Γ u⊢ds [] : TTop
(* This demands definitions and members to be defined in aligned lists. *)
| iD_Cons l d ds T1 T2:
    Γ u⊢{ l := d } : T1 →
    Γ u⊢ds ds : T2 →
    dms_hasnt ds l →
    (*──────────────────────*)
    Γ u⊢ds (l, d) :: ds : TAnd T1 T2
where "Γ u⊢ds ds : T" := (dms_typed Γ ds T)
with dm_typed Γ : label → dm → ty → Prop :=
| iD_Typ_Abs T l L U:
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ L, 0 <: TLater T, 0 →
    Γ u⊢ₜ TLater T, 0 <: U, 0 →
    Γ u⊢{ l := dtysyn T } : TTMem l L U
| iD_Val l v T:
    Γ u⊢ₜ tv v : T →
    Γ u⊢{ l := dpt (pv v) } : TVMem l T
| iD_Path l p T:
    Γ u⊢ₚ p : T, 0 →
    Γ u⊢{ l := dpt p } : TVMem l T
| iD_Val_New l T ds:
    TAnd (TLater T) (TSing (pself (pv (ids 1)) l)) :: Γ u⊢ds ds : T →
    Γ u⊢{ l := dpt (pv (vobj ds)) } : TVMem l (TMu T)
| iD_Path_Sub T1 T2 p l:
    Γ u⊢ₜ T1, 0 <: T2, 0 →
    Γ u⊢{ l := dpt p } : TVMem l T1 →
    Γ u⊢{ l := dpt p } : TVMem l T2
where "Γ u⊢{ l := d  } : T" := (dm_typed Γ l d T).

(* Make [T] first argument: Hide Γ for e.g. typing examples. *)
Global Arguments iD_Typ_Abs {Γ} T _ _ _ _ _ _ : assert.

Scheme unstamped_typed_mut_ind := Induction for typed Sort Prop
with   unstamped_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   unstamped_dm_typed_mut_ind := Induction for dm_typed Sort Prop.

Combined Scheme old_unstamped_typing_mut_ind from
  unstamped_typed_mut_ind, unstamped_dms_typed_mut_ind, unstamped_dm_typed_mut_ind.

Lemma dtysem_not_utyped Γ l d T :
  Γ u⊢{ l := d } : T → ∀ σ s, d ≠ dtysem σ s.
Proof. by case. Qed.

(** ** A few derived rules, and some automation to use them in examples. *)

Hint Constructors typed dms_typed dm_typed : core.

Lemma iT_Path' Γ v T
  (Ht : Γ u⊢ₚ pv v : T, 0) : Γ u⊢ₜ tv v : T.
Proof. exact: (iT_Path (p := pv _)). Qed.

Lemma iT_Nat_I Γ n : Γ u⊢ₜ tv (vint n): TInt.
Proof. apply iT_Path'; constructor. Qed.

Lemma iT_Bool_I Γ b : Γ u⊢ₜ tv (vbool b): TBool.
Proof. apply iT_Path'; constructor. Qed.

Lemma iT_All_I Γ e T1 T2:
  shift T1 :: Γ u⊢ₜ e : T2 →
  (*─────────────────────────*)
  Γ u⊢ₜ tv (vabs e) : TAll T1 T2.
Proof. apply iT_All_I_Strong. ietp_weaken_ctx. Qed.

Lemma iT_All_I_strip1 Γ e V T1 T2:
  shift T1 :: V :: Γ u⊢ₜ e : T2 →
  (*─────────────────────────*)
  Γ |L V u⊢ₜ tv (vabs e) : TAll T1 T2.
Proof.
  intros. apply iT_All_I_Strong with (Γ' := (V :: Γ)) => //.
  rewrite /defCtxCons/=; ietp_weaken_ctx.
Qed.

Lemma iD_All Γ V T1 T2 e l:
  shift T1 :: V :: Γ u⊢ₜ e : T2 →
  Γ |L V u⊢{ l := dpt (pv (vabs e)) } : TVMem l (TAll T1 T2).
Proof. by intros; apply iD_Val, iT_All_I_strip1. Qed.

Lemma iT_Var {Γ x T}
  (Hx : Γ !! x = Some T) :
  Γ u⊢ₜ tv (vvar x) : shiftN x T.
Proof. apply iT_Path'. eauto. Qed.

Lemma iP_VarT {Γ x T} :
  Γ u⊢ₜ tv (vvar x) : T →
  Γ u⊢ₚ pv (vvar x) : T, 0.
Proof.
  move E: (tv (vvar x)) => t; induction 1; simplify_eq/=;
    last by destruct p; simplify_eq/=.
  destruct i; last by [simplify_eq]; rewrite iterate_0 in E; simplify_eq/=.
  eapply iP_ISub'; eauto.
Qed.

Ltac typconstructor :=
  match goal with
  | |- typed ?Γ _ _ => first [
    apply iT_All_I_strip1 | apply iT_All_I |
    apply iT_Var |
    apply iT_Nat_I | apply iT_Bool_I |
    constructor]
  | |- dms_typed ?Γ _ _ => constructor
  | |- dm_typed ?Γ _ _ _ => first [apply iD_All | constructor]
  | |- path_typed ?Γ _ _ _ => first [apply iP_VarT | subtypconstructor]
  | |- subtype ?Γ _ _ _ _ => subtypconstructor
  end.
