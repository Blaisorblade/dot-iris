(** * Judgments defining syntactic gDOT definition and term typing. *)
From D Require Import tactics.
From D.Dot Require Export syn path_repl lr_syn_aux.
From D.Dot Require Export typing_aux_defs type_eq subtyping.
From D.Dot Require Export core_stamping_defs.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (L T U : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty).

Reserved Notation "Γ t⊢ₜ e : T" (at level 74, e, T at next level).
Reserved Notation "Γ t⊢{ l := d  } : T" (at level 74, l, d, T at next level).
Reserved Notation "Γ t⊢ds ds : T" (at level 74, ds, T at next level).

(** ** Judgments for typing, subtyping, path and definition typing. *)
Inductive typed Γ : tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a path. *)
| iT_All_E_p p2 e1 T1 T2:
    is_unstamped_ty' (length Γ).+1 T2 →
    Γ t⊢ₜ e1: TAll T1 T2 →
    Γ t⊢ₚ p2 : T1, 0 →
    (*────────────────────────────────────────────────────────────*)
    Γ t⊢ₜ tapp e1 (path2tm p2) : T2 .Tp[ p2 /]
(** Non-dependent application; allowed for any argument. *)
| iT_All_E e1 e2 T1 T2:
    Γ t⊢ₜ e1: TAll T1 (shift T2) →      Γ t⊢ₜ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ t⊢ₜ tapp e1 e2 : T2
| iT_Obj_E e T l:
    Γ t⊢ₜ e : TVMem l T →
    (*─────────────────────────*)
    Γ t⊢ₜ tproj e l : T
(** Introduction forms *)
| iT_All_I_Strong e T1 T2 Γ':
    ⊢G Γ >>▷* Γ' →
    (* T1 :: Γ' t⊢ₜ e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    shift T1 :: Γ' t⊢ₜ e : T2 →
    (*─────────────────────────*)
    Γ t⊢ₜ tv (vabs e) : TAll T1 T2
| iT_Obj_I ds T:
    Γ |L T t⊢ds ds: T →
    (*──────────────────────*)
    Γ t⊢ₜ tv (vobj ds): TMu T

(** "General" rules *)
| iT_ISub e T1 T2 :
    Γ t⊢ₜ T1 <:[ 0 ] T2 → Γ t⊢ₜ e : T1 →
    (*───────────────────────────────*)
    Γ t⊢ₜ e : T2
| iT_Skip e T :
    Γ t⊢ₜ e : TLater T →
    (*───────────────────────────────*)
    Γ t⊢ₜ tskip e : T
| iT_Path p T :
    Γ t⊢ₚ p : T, 0 →
    (*───────────────────────────────*)
    Γ t⊢ₜ path2tm p : T

(** Primitives. *)
| iT_Un u e1 B1 Br (Hu : un_op_syntype u B1 Br) :
    Γ t⊢ₜ e1 : TPrim B1 →
    Γ t⊢ₜ tun u e1 : TPrim Br
| iT_Bin b e1 e2 B1 B2 Br (Hu : bin_op_syntype b B1 B2 Br) :
    Γ t⊢ₜ e1 : TPrim B1 →
    Γ t⊢ₜ e2 : TPrim B2 →
    Γ t⊢ₜ tbin b e1 e2 : TPrim Br
| iT_If e e1 e2 T :
    Γ t⊢ₜ e: TBool →
    Γ t⊢ₜ e1 : T →
    Γ t⊢ₜ e2 : T →
    Γ t⊢ₜ tif e e1 e2 : T
where "Γ t⊢ₜ e : T" := (typed Γ e T)
with dms_typed Γ : dms → ty → Prop :=
| iD_Nil : Γ t⊢ds [] : TTop
(* This demands definitions and members to be defined in aligned lists. *)
| iD_Cons l d ds T1 T2:
    Γ t⊢{ l := d } : T1 →
    Γ t⊢ds ds : T2 →
    dms_hasnt ds l →
    (*──────────────────────*)
    Γ t⊢ds (l, d) :: ds : TAnd T1 T2
where "Γ t⊢ds ds : T" := (dms_typed Γ ds T)
with dm_typed Γ : label → dm → ty → Prop :=
| iD_Typ_Abs T l L U:
    nclosed T (length Γ) →
    Γ t⊢ₜ L <:[0] TLater T →
    Γ t⊢ₜ TLater T <:[0] U →
    Γ t⊢{ l := dtysyn T } : TTMem l L U
| iD_Val l v T:
    Γ t⊢ₜ tv v : T →
    Γ t⊢{ l := dpt (pv v) } : TVMem l T
| iD_Path l p T:
    Γ t⊢ₚ p : T, 0 →
    Γ t⊢{ l := dpt p } : TVMem l T
| iD_Val_New l T ds:
    TAnd (TLater T) (TSing (pself (pv (ids 1)) l)) :: Γ t⊢ds ds : T →
    Γ t⊢{ l := dpt (pv (vobj ds)) } : TVMem l (TMu T)
| iD_Path_Sub T1 T2 p l:
    Γ t⊢ₜ T1 <:[0] T2 →
    Γ t⊢{ l := dpt p } : TVMem l T1 →
    Γ t⊢{ l := dpt p } : TVMem l T2
where "Γ t⊢{ l := d  } : T" := (dm_typed Γ l d T).

(* Make [T] first argument: Hide Γ for e.g. typing examples. *)
#[global] Arguments iD_Typ_Abs {Γ} T _ _ _ _ _ _ : assert.

Scheme typed_mut_ind := Induction for typed Sort Prop
with   dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   dm_typed_mut_ind := Induction for dm_typed Sort Prop.
Combined Scheme typing_mut_ind from typed_mut_ind, dms_typed_mut_ind, dm_typed_mut_ind.

Lemma dtysem_not_utyped Γ l d T :
  Γ t⊢{ l := d } : T → ∀ σ s, d ≠ dtysem σ s.
Proof. by case. Qed.

(** ** A few derived rules, and some automation to use them in examples. *)

Hint Constructors typed dms_typed dm_typed : core.

(** Ensure [eauto]'s proof search does not diverge due to transitivity. *)
#[global] Remove Hints iStp_Trans : core.
Hint Extern 10 => try_once iStp_Trans : core.

Lemma iT_Path' Γ v T
  (Ht : Γ t⊢ₚ pv v : T, 0) : Γ t⊢ₜ tv v : T.
Proof. exact: (iT_Path (p := pv _)). Qed.

Lemma iT_Var Γ x T
  (Hl : Γ !! x = Some T) :
  Γ t⊢ₜ tv (vvar x) : shiftN x T.
Proof. intros. apply iT_Path', iP_Var, Hl. Qed.

Lemma iT_All_I Γ e T1 T2:
  shift T1 :: Γ t⊢ₜ e : T2 →
  (*─────────────────────────*)
  Γ t⊢ₜ tv (vabs e) : TAll T1 T2.
Proof. apply iT_All_I_Strong. ietp_weaken_ctx. Qed.

Lemma iT_All_I_strip1 Γ e V T1 T2:
  shift T1 :: V :: Γ t⊢ₜ e : T2 →
  (*─────────────────────────*)
  Γ |L V t⊢ₜ tv (vabs e) : TAll T1 T2.
Proof.
  intros. apply iT_All_I_Strong with (Γ' := (V :: Γ)) => //.
  rewrite /defCtxCons/=; ietp_weaken_ctx.
Qed.

Lemma iD_All Γ V T1 T2 e l:
  shift T1 :: V :: Γ t⊢ₜ e : T2 →
  Γ |L V t⊢{ l := dpt (pv (vabs e)) } : TVMem l (TAll T1 T2).
Proof. by intros; apply iD_Val, iT_All_I_strip1. Qed.

Lemma iT_ISub' Γ i T1 T2 e :
  Γ t⊢ₜ T1 <:[ 0 ] iterate TLater i T2 →
  Γ t⊢ₜ e : T1 →
  Γ t⊢ₜ iterate tskip i e : T2.
Proof.
  elim: i T1 T2 => [|i +] T1 T2; first eauto.
  rewrite (iterate_S _ _ e) iterate_Sr => IHi IHsub IH1.
  apply /iT_Skip /IHi /IH1 /IHsub.
Qed.

(** Never used, but displayed in the paper. *)
Lemma iT_Sel_Unfold Γ i e p l L U :
  Γ t⊢ₚ p : TTMem l L U, i →
  Γ t⊢ₜ e : TSel p l →
  Γ t⊢ₜ iterate tskip i e : U.
Proof.
  intros Hp He.
  apply: iT_ISub' He.
  ettrans; first apply (iStp_Add_LaterN (j := i)).
  rewrite -iLaterN0_Stp_Eq.
  apply: iSel_Stp Hp.
Qed.

Ltac typconstructor_blacklist Γ :=
  lazymatch goal with
  | |- path_typed ?Γ' _ _ _ =>
  tryif (unify Γ Γ') then idtac else fail 1 "Only applicable rule is iStp_Skolem_P"
  | _ => idtac
  end.

(* XXX test *)
Ltac typconstructor :=
  match goal with
  | |- typed _ _ _ =>
    first [apply iT_Var | apply iT_All_I_strip1 | apply iT_All_I | constructor]
  | |- dms_typed _ _ _ => constructor
  | |- dm_typed _ _ _ _ => first [apply iD_All | constructor]
  | |- path_typed _ _ _ _ => first [apply iP_Later | constructor]
  | |- subtype ?Γ _ _ _ _ =>
    first [apply iLater_Idx_Stp | constructor ]; typconstructor_blacklist Γ
  end.
