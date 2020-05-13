(** * Judgments defining gDOT unstamped typing.

We show that unstamped typing derivations from here can
be converted to stamped derivations of this typing judgment, in lemma
[stamp_typing_mut].

This judgment allowing only variables in paths, and not arbitrary values.
*)
From D Require Import tactics.
From D.Dot Require Export syn path_repl lr_syn_aux.
From D.Dot.typing Require Export typing_aux_defs.
From D.Dot.stamping Require Export core_stamping_defs.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (L T U : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty).

(* The typing judgement comes from [s/⊢/u⊢/] over [Dot/stamped_typing.v], and dropping stamping. *)
Reserved Notation "Γ u⊢ₜ e : T" (at level 74, e, T at next level).
Reserved Notation "Γ u⊢ₚ p : T , i" (at level 74, p, T, i at next level).
Reserved Notation "Γ u⊢{ l := d  } : T" (at level 74, l, d, T at next level).
Reserved Notation "Γ u⊢ds ds : T" (at level 74, ds, T at next level).
Reserved Notation "Γ u⊢ₜ T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

(** ** Judgments for typing, subtyping, path and definition typing. *)
Inductive typed Γ : tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a path. *)
| iT_All_Ex_p p2 e1 T1 T2:
    is_unstamped_ty' (S (length Γ)) T2 →
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
    is_unstamped_ty' (length Γ) T1 →
    (* T1 :: Γ' u⊢ₜ e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    shift T1 :: Γ' u⊢ₜ e : T2 →
    (*─────────────────────────*)
    Γ u⊢ₜ tv (vabs e) : TAll T1 T2
| iT_Obj_I ds T:
    Γ |L T u⊢ds ds: T →
    is_unstamped_ty' (S (length Γ)) T →
    (*──────────────────────*)
    Γ u⊢ₜ tv (vobj ds): TMu T

(** "General" rules *)
| iT_Var x T :
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ u⊢ₜ tv (var_vl x) : shiftN x T
| iT_Sub e T1 T2 i :
    Γ u⊢ₜ T1, 0 <: T2, i → Γ u⊢ₜ e : T1 →
    (*───────────────────────────────*)
    Γ u⊢ₜ iterate tskip i e : T2
| iT_Path p T :
    Γ u⊢ₚ p : T, 0 →
    (*───────────────────────────────*)
    Γ u⊢ₜ path2tm p : T

(** Primitives. *)
| iT_Nat_I n:
    Γ u⊢ₜ tv (vint n): TInt
| iT_Bool_I b:
    Γ u⊢ₜ tv (vbool b): TBool
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
    Γ u⊢ₜ TLater L, 0 <: TLater T, 0 →
    Γ u⊢ₜ TLater T, 0 <: TLater U, 0 →
    Γ u⊢{ l := dtysyn T } : TTMem l L U
| iD_Val l v T:
    Γ u⊢ₜ tv v : T →
    Γ u⊢{ l := dpt (pv v) } : TVMem l T
| iD_Path l p T:
    Γ u⊢ₚ p : T, 0 →
    Γ u⊢{ l := dpt p } : TVMem l T
| iD_Val_New l T ds:
    TAnd (TLater T) (TSing (pself (pv (ids 1)) l)) :: Γ u⊢ds ds : T →
    is_unstamped_ty' (S (length Γ)) T →
    Γ u⊢{ l := dpt (pv (vobj ds)) } : TVMem l (TMu T)
| iD_Path_Sub T1 T2 p l:
    Γ u⊢ₜ T1, 0 <: T2, 0 →
    Γ u⊢{ l := dpt p } : TVMem l T1 →
    Γ u⊢{ l := dpt p } : TVMem l T2
where "Γ u⊢{ l := d  } : T" := (dm_typed Γ l d T)
with path_typed Γ : path → ty → nat → Prop :=
| iP_Val x T:
    Γ u⊢ₜ tv (var_vl x) : T →
    Γ u⊢ₚ pv (var_vl x) : T, 0
(* Mnemonic: Path from SELecting a Field *)
| iP_Fld_E p T i l:
    Γ u⊢ₚ p : TVMem l T, i →
    Γ u⊢ₚ pself p l : T, i
| iP_Sub p T1 T2 i j :
    Γ u⊢ₜ T1, i <: T2, i + j →
    Γ u⊢ₚ p : T1, i →
    (*───────────────────────────────*)
    Γ u⊢ₚ p : T2, i + j
| iP_Mu_I p T {i} :
    is_unstamped_ty' (S (length Γ)) T →
    Γ u⊢ₚ p : T .Tp[ p /], i →
    Γ u⊢ₚ p : TMu T, i
| iP_Mu_E p T {i} :
    is_unstamped_ty' (S (length Γ)) T →
    Γ u⊢ₚ p : TMu T, i →
    Γ u⊢ₚ p : T .Tp[ p /], i
| iP_Fld_I p T i l:
    Γ u⊢ₚ pself p l : T, i →
    (*─────────────────────────*)
    Γ u⊢ₚ p : TVMem l T, i
| iP_Sngl_Refl T p i :
    Γ u⊢ₚ p : T, i →
    Γ u⊢ₚ p : TSing p, i
| iP_Sngl_Inv p q i:
    Γ u⊢ₚ p : TSing q, i →
    is_unstamped_path' (length Γ) q →
    Γ u⊢ₚ q : TTop, i
| iP_Sngl_Trans p q T i:
    Γ u⊢ₚ p : TSing q, i →
    Γ u⊢ₚ q : T, i →
    Γ u⊢ₚ p : T, i
| iP_Sngl_E T p q l i:
    Γ u⊢ₚ p : TSing q, i →
    Γ u⊢ₚ pself q l : T, i →
    Γ u⊢ₚ pself p l : TSing (pself q l), i
where "Γ u⊢ₚ p : T , i" := (path_typed Γ p T i)
(* Γ u⊢ₜ T1, i1 <: T2, i2 means that TLater^i1 T1 <: TLater^i2 T2. *)
with subtype Γ : ty → nat → ty → nat → Prop :=
| iSub_Refl i T :
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ T, i <: T, i
| iSub_Trans i2 T2 {i1 i3 T1 T3}:
    Γ u⊢ₜ T1, i1 <: T2, i2 →
    Γ u⊢ₜ T2, i2 <: T3, i3 →
    Γ u⊢ₜ T1, i1 <: T3, i3
| iLater_Sub i T:
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ TLater T, i <: T, S i
| iSub_Later i T:
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ T, S i <: TLater T, i

(* "Structural" rule about indexes *)
| iSub_Add_Later T i:
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ T, i <: TLater T, i

(* "Logical" connectives *)
| iSub_Top i T :
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ T, i <: TTop, i
| iBot_Sub i T :
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ TBot, i <: T, i
| iAnd1_Sub T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ u⊢ₜ TAnd T1 T2, i <: T1, i
| iAnd2_Sub T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ u⊢ₜ TAnd T1 T2, i <: T2, i
| iSub_And T U1 U2 i j:
    Γ u⊢ₜ T, i <: U1, j →
    Γ u⊢ₜ T, i <: U2, j →
    Γ u⊢ₜ T, i <: TAnd U1 U2, j
| iSub_Or1 T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ u⊢ₜ T1, i <: TOr T1 T2, i
| iSub_Or2 T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ u⊢ₜ T2, i <: TOr T1 T2, i
| iOr_Sub T1 T2 U i j:
    Γ u⊢ₜ T1, i <: U, j →
    Γ u⊢ₜ T2, i <: U, j →
    Γ u⊢ₜ TOr T1 T2, i <: U, j

(* Type selections *)
| iSel_Sub p L {l U i}:
    Γ u⊢ₚ p : TTMem l L U, i →
    Γ u⊢ₜ TSel p l, i <: TLater U, i
| iSub_Sel p U {l L i}:
    Γ u⊢ₚ p : TTMem l L U, i →
    Γ u⊢ₜ TLater L, i <: TSel p l, i
| iSngl_pq_Sub p q {i T1 T2}:
    T1 ~Tp[ p := q ]* T2 →
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ u⊢ₚ p : TSing q, i →
    Γ u⊢ₜ T1, i <: T2, i
| iSngl_Sub_Sym T {p q i}:
    Γ u⊢ₚ p : T, i →
    Γ u⊢ₜ TSing p, i <: TSing q, i →
    Γ u⊢ₜ TSing q, i <: TSing p, i
| iSngl_Sub_Self {p T i} :
    Γ u⊢ₚ p : T, i →
    Γ u⊢ₜ TSing p, i <: T, i

(* Subtyping for recursive types. Congruence, and opening in both directions. *)
| iMu_Sub_Mu T1 T2 i j:
    (iterate TLater i T1 :: Γ) u⊢ₜ T1, i <: T2, j →
    is_unstamped_ty' (S (length Γ)) T1 →
    Γ u⊢ₜ TMu T1, i <: TMu T2, j
| iMu_Sub T i:
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ TMu (shift T), i <: T, i
| iSub_Mu T i:
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ T, i <: TMu (shift T), i

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types. *)
| iAll_Sub_All T1 T2 U1 U2 i:
    Γ u⊢ₜ TLater T2, i <: TLater T1, i →
    iterate TLater (S i) (shift T2) :: Γ u⊢ₜ TLater U1, i <: TLater U2, i →
    is_unstamped_ty' (length Γ) T2 →
    Γ u⊢ₜ TAll T1 U1, i <: TAll T2 U2, i
| iFld_Sub_Fld T1 T2 i l:
    Γ u⊢ₜ T1, i <: T2, i →
    Γ u⊢ₜ TVMem l T1, i <: TVMem l T2, i
| iTyp_Sub_Typ L1 L2 U1 U2 i l:
    Γ u⊢ₜ TLater L2, i <: TLater L1, i →
    Γ u⊢ₜ TLater U1, i <: TLater U2, i →
    Γ u⊢ₜ TTMem l L1 U1, i <: TTMem l L2 U2, i
  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
| iAnd_All_Sub_Distr T U1 U2 i:
    is_unstamped_ty' (length Γ) T →
    is_unstamped_ty' (S (length Γ)) U1 →
    is_unstamped_ty' (S (length Γ)) U2 →
    Γ u⊢ₜ TAnd (TAll T U1) (TAll T U2), i <: TAll T (TAnd U1 U2), i
| iAnd_Fld_Sub_Distr l T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ u⊢ₜ TAnd (TVMem l T1) (TVMem l T2), i <: TVMem l (TAnd T1 T2), i
| iAnd_Typ_Sub_Distr l L U1 U2 i:
    is_unstamped_ty' (length Γ) L →
    is_unstamped_ty' (length Γ) U1 →
    is_unstamped_ty' (length Γ) U2 →
    Γ u⊢ₜ TAnd (TTMem l L U1) (TTMem l L U2), i <: TTMem l L (TAnd U1 U2), i

where "Γ u⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).

(* Make [T] first argument: Hide Γ for e.g. typing examples. *)
Global Arguments iD_Typ_Abs {Γ} T _ _ _ _ _ _ : assert.

Scheme unstamped_typed_mut_ind := Induction for typed Sort Prop
with   unstamped_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   unstamped_dm_typed_mut_ind := Induction for dm_typed Sort Prop
with   unstamped_path_typed_mut_ind := Induction for path_typed Sort Prop
with   unstamped_subtype_mut_ind := Induction for subtype Sort Prop.

Combined Scheme unstamped_typing_mut_ind from unstamped_typed_mut_ind, unstamped_dms_typed_mut_ind, unstamped_dm_typed_mut_ind,
  unstamped_path_typed_mut_ind, unstamped_subtype_mut_ind.

Scheme exp_unstamped_typed_mut_ind := Induction for typed Sort Prop
with   exp_unstamped_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   exp_unstamped_dm_typed_mut_ind := Induction for dm_typed Sort Prop
with   exp_unstamped_path_typed_mut_ind := Induction for path_typed Sort Prop.

Combined Scheme exp_unstamped_typing_mut_ind from exp_unstamped_typed_mut_ind, exp_unstamped_dms_typed_mut_ind,
  exp_unstamped_dm_typed_mut_ind, exp_unstamped_path_typed_mut_ind.

Lemma unstamped_path_root_is_var Γ p T i:
  Γ u⊢ₚ p : T, i → ∃ x, path_root p = var_vl x.
Proof. by elim; intros; cbn; eauto 2 using is_unstamped_path_root. Qed.

Lemma dtysem_not_utyped Γ l d T :
  Γ u⊢{ l := d } : T → ∀ σ s, d ≠ dtysem σ s.
Proof. by case. Qed.

(** ** A few derived rules, and some automation to use them in examples. *)

Hint Constructors typed dms_typed dm_typed path_typed subtype : core.

(** Ensure [eauto]'s proof search does not diverge due to transitivity. *)
Remove Hints iSub_Trans : core.
Hint Extern 10 => try_once iSub_Trans : core.

Lemma iT_All_I Γ e T1 T2:
  is_unstamped_ty' (length Γ) T1 →
  shift T1 :: Γ u⊢ₜ e : T2 →
  (*─────────────────────────*)
  Γ u⊢ₜ tv (vabs e) : TAll T1 T2.
Proof. apply iT_All_I_Strong. ietp_weaken_ctx. Qed.

Lemma iT_All_I_strip1 Γ e V T1 T2:
  is_unstamped_ty' (S (length Γ)) T1 →
  shift T1 :: V :: Γ u⊢ₜ e : T2 →
  (*─────────────────────────*)
  Γ |L V u⊢ₜ tv (vabs e) : TAll T1 T2.
Proof.
  intros. apply iT_All_I_Strong with (Γ' := (V :: Γ)) => //.
  rewrite /defCtxCons/=; ietp_weaken_ctx.
Qed.

Lemma iD_All Γ V T1 T2 e l:
  is_unstamped_ty' (S (length Γ)) T1 →
  shift T1 :: V :: Γ u⊢ₜ e : T2 →
  Γ |L V u⊢{ l := dpt (pv (vabs e)) } : TVMem l (TAll T1 T2).
Proof. by intros; apply iD_Val, iT_All_I_strip1. Qed.

Lemma iP_Later {Γ p T i} :
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₚ p : TLater T, i →
  Γ u⊢ₚ p : T, S i.
Proof.
  intros Hu Hp; apply iP_Sub with (j := 1) (T1 := TLater T) (T2 := T) in Hp;
    move: Hp; rewrite (plusnS i 0) (plusnO i); intros; by [|constructor].
Qed.

Ltac ettrans := eapply iSub_Trans.

Lemma Sub_later_shift {Γ T1 T2 i j}
  (Hs1: is_unstamped_ty' (length Γ) T1)
  (Hs2: is_unstamped_ty' (length Γ) T2)
  (Hsub: Γ u⊢ₜ T1, S i <: T2, S j):
  Γ u⊢ₜ TLater T1, i <: TLater T2, j.
Proof.
  ettrans; first exact: iLater_Sub.
  by eapply iSub_Trans, iSub_Later.
Qed.

Lemma Sub_later_shift_inv {Γ T1 T2 i j}
  (Hs1: is_unstamped_ty' (length Γ) T1)
  (Hs2: is_unstamped_ty' (length Γ) T2)
  (Hsub: Γ u⊢ₜ TLater T1, i <: TLater T2, j):
  Γ u⊢ₜ T1, S i <: T2, S j.
Proof.
  ettrans; first exact: iSub_Later.
  by eapply iSub_Trans, iLater_Sub.
Qed.

Ltac typconstructor :=
  match goal with
  | |- typed _ _ _ => first [apply iT_All_I_strip1 | apply iT_All_I | constructor]
  | |- dms_typed _ _ _ => constructor
  | |- dm_typed _ _ _ _ => first [apply iD_All | constructor]
  | |- path_typed _ _ _ _ => first [apply iP_Later | constructor]
  | |- subtype _ _ _ _ _ =>
    first [apply Sub_later_shift | constructor ]
  end.
