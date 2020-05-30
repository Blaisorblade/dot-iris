(** * Judgments defining gDOT unstamped typing.

We show that unstamped typing derivations from here can
be converted to stamped derivations of this typing judgment, in lemma
[stamp_typing_mut].

This judgment allowing only variables in paths, and not arbitrary values.
*)
From D Require Import tactics.
From D.Dot Require Export syn path_repl lr_syn_aux.
From D.Dot.typing Require Export typing_aux_defs type_eq.
From D.Dot.stamping Require Export core_stamping_defs.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (L T U : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty).

Reserved Notation "Γ t⊢ₜ e : T" (at level 74, e, T at next level).
Reserved Notation "Γ t⊢ₚ p : T , i" (at level 74, p, T, i at next level).
Reserved Notation "Γ t⊢{ l := d  } : T" (at level 74, l, d, T at next level).
Reserved Notation "Γ t⊢ds ds : T" (at level 74, ds, T at next level).
Reserved Notation "Γ t⊢ₜ T1 <:[ i  ] T2" (at level 74, T1, T2 at next level).

(** ** Judgments for typing, subtyping, path and definition typing. *)
Inductive typed Γ : tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a path. *)
| iT_All_Ex_p p2 e1 T1 T2:
    is_unstamped_ty' (S (length Γ)) T2 →
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
    is_unstamped_ty' (length Γ) T1 →
    (* T1 :: Γ' t⊢ₜ e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    shift T1 :: Γ' t⊢ₜ e : T2 →
    (*─────────────────────────*)
    Γ t⊢ₜ tv (vabs e) : TAll T1 T2
| iT_Obj_I ds T:
    Γ |L T t⊢ds ds: T →
    is_unstamped_ty' (S (length Γ)) T →
    (*──────────────────────*)
    Γ t⊢ₜ tv (vobj ds): TMu T

(** "General" rules *)
| iT_Sub e T1 T2 :
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
| iT_Nat_I n:
    Γ t⊢ₜ tv (vint n): TInt
| iT_Bool_I b:
    Γ t⊢ₜ tv (vbool b): TBool
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
where "Γ t⊢ₜ e : T " := (typed Γ e T)
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
    (* To drop *)
    is_unstamped_ty' (length Γ) T →
    (* To keep *)
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
    is_unstamped_ty' (S (length Γ)) T →
    Γ t⊢{ l := dpt (pv (vobj ds)) } : TVMem l (TMu T)
| iD_Path_Sub T1 T2 p l:
    Γ t⊢ₜ T1 <:[0] T2 →
    Γ t⊢{ l := dpt p } : TVMem l T1 →
    Γ t⊢{ l := dpt p } : TVMem l T2
where "Γ t⊢{ l := d  } : T" := (dm_typed Γ l d T)
with path_typed Γ : path → ty → nat → Prop :=
| iP_Var x T:
    Γ !! x = Some T →
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ t⊢ₚ pv (var_vl x) : shiftN x T, 0
(* Mnemonic: Path from SELecting a Field *)
| iP_Fld_E p T i l:
    Γ t⊢ₚ p : TVMem l T, i →
    Γ t⊢ₚ pself p l : T, i
| iP_Sub p T1 T2 i :
    Γ t⊢ₜ T1 <:[i] T2 →
    Γ t⊢ₚ p : T1, i →
    (*───────────────────────────────*)
    Γ t⊢ₚ p : T2, i
| iP_Later p T i :
    Γ t⊢ₚ p : TLater T, i →
    (*───────────────────────────────*)
    Γ t⊢ₚ p : T, S i
| iP_Mu_I p T {i} :
    is_unstamped_ty' (S (length Γ)) T →
    Γ t⊢ₚ p : T .Tp[ p /], i →
    Γ t⊢ₚ p : TMu T, i
| iP_Mu_E p T {i} :
    is_unstamped_ty' (S (length Γ)) T →
    Γ t⊢ₚ p : TMu T, i →
    Γ t⊢ₚ p : T .Tp[ p /], i
| iP_Fld_I p T i l:
    Γ t⊢ₚ pself p l : T, i →
    (*─────────────────────────*)
    Γ t⊢ₚ p : TVMem l T, i
| iP_Sngl_Refl T p i :
    Γ t⊢ₚ p : T, i →
    Γ t⊢ₚ p : TSing p, i
| iP_Sngl_Inv p q i:
    Γ t⊢ₚ p : TSing q, i →
    is_unstamped_path' (length Γ) q →
    Γ t⊢ₚ q : TTop, i
| iP_Sngl_Trans p q T i:
    Γ t⊢ₚ p : TSing q, i →
    Γ t⊢ₚ q : T, i →
    Γ t⊢ₚ p : T, i
| iP_Sngl_E T p q l i:
    Γ t⊢ₚ p : TSing q, i →
    Γ t⊢ₚ pself q l : T, i →
    Γ t⊢ₚ pself p l : TSing (pself q l), i
where "Γ t⊢ₚ p : T , i" := (path_typed Γ p T i)
with subtype Γ : nat → ty → ty → Prop :=
| iStp_Refl i T :
    is_unstamped_ty' (length Γ) T →
    Γ t⊢ₜ T <:[i] T
| iStp_Trans T2 {i T1 T3}:
    Γ t⊢ₜ T1 <:[i] T2 →
    Γ t⊢ₜ T2 <:[i] T3 →
    Γ t⊢ₜ T1 <:[i] T3
| iLater_Idx_Stp i T1 T2: (* XXX name *)
    Γ t⊢ₜ T1 <:[S i] T2 →
    Γ t⊢ₜ TLater T1 <:[i] TLater T2
| iIdx_Later_Stp i T1 T2: (* XXX name*)
    Γ t⊢ₜ TLater T1 <:[i] TLater T2 →
    Γ t⊢ₜ T1 <:[S i] T2

(* "Structural" rule about indexes *)
| iStp_Add_Later T i:
    is_unstamped_ty' (length Γ) T →
    Γ t⊢ₜ T <:[i] TLater T

(* "Logical" connectives *)
| iStp_Top i T :
    is_unstamped_ty' (length Γ) T →
    Γ t⊢ₜ T <:[i] TTop
| iBot_Stp i T :
    is_unstamped_ty' (length Γ) T →
    Γ t⊢ₜ TBot <:[i] T
| iAnd1_Stp T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ t⊢ₜ TAnd T1 T2 <:[i] T1
| iAnd2_Stp T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ t⊢ₜ TAnd T1 T2 <:[i] T2
| iStp_And T U1 U2 i:
    Γ t⊢ₜ T <:[i] U1 →
    Γ t⊢ₜ T <:[i] U2 →
    Γ t⊢ₜ T <:[i] TAnd U1 U2
| iStp_Or1 T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ t⊢ₜ T1 <:[i] TOr T1 T2
| iStp_Or2 T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ t⊢ₜ T2 <:[i] TOr T1 T2
| iOr_Stp T1 T2 U i:
    Γ t⊢ₜ T1 <:[i] U →
    Γ t⊢ₜ T2 <:[i] U →
    Γ t⊢ₜ TOr T1 T2 <:[i] U

(* Type selections *)
| iSel_Stp p L {l U i}:
    Γ t⊢ₚ p : TTMem l L U, i →
    Γ t⊢ₜ TSel p l <:[i] U
| iStp_Sel p U {l L i}:
    Γ t⊢ₚ p : TTMem l L U, i →
    Γ t⊢ₜ L <:[i] TSel p l

| iSngl_pq_Stp p q {i T1 T2}:
    T1 ~Tp[ p := q ]* T2 →
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ t⊢ₚ p : TSing q, i →
    Γ t⊢ₜ T1 <:[i] T2
| iSngl_Stp_Sym T {p q i}:
    Γ t⊢ₚ p : T, i →
    Γ t⊢ₜ TSing p <:[i] TSing q →
    Γ t⊢ₜ TSing q <:[i] TSing p
| iSngl_Stp_Self {p T i} :
    Γ t⊢ₚ p : T, i →
    Γ t⊢ₜ TSing p <:[i] T

(* Subtyping for recursive types. Congruence, and opening in both directions. *)
| iMu_Stp_Mu T1 T2 i:
    (iterate TLater i T1 :: Γ) t⊢ₜ T1 <:[i] T2 →
    is_unstamped_ty' (S (length Γ)) T1 →
    Γ t⊢ₜ TMu T1 <:[i] TMu T2
| iMu_Stp T i:
    is_unstamped_ty' (length Γ) T →
    Γ t⊢ₜ TMu (shift T) <:[i] T
| iStp_Mu T i:
    is_unstamped_ty' (length Γ) T →
    Γ t⊢ₜ T <:[i] TMu (shift T)

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types. *)
| iAll_Stp_All T1 T2 U1 U2 i:
    Γ t⊢ₜ TLater T2 <:[i] TLater T1 →
    iterate TLater (S i) (shift T2) :: Γ t⊢ₜ TLater U1 <:[i] TLater U2 →
    is_unstamped_ty' (length Γ) T2 →
    Γ t⊢ₜ TAll T1 U1 <:[i] TAll T2 U2
| iFld_Stp_Fld T1 T2 i l:
    Γ t⊢ₜ T1 <:[i] T2 →
    Γ t⊢ₜ TVMem l T1 <:[i] TVMem l T2
| iTyp_Stp_Typ L1 L2 U1 U2 i l:
    Γ t⊢ₜ L2 <:[i] L1 →
    Γ t⊢ₜ U1 <:[i] U2 →
    Γ t⊢ₜ TTMem l L1 U1 <:[i] TTMem l L2 U2
  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <:[i] F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <:[i] F[A ∧ B] in the model.
    *)
| iAnd_All_Stp_Distr T U1 U2 i:
    is_unstamped_ty' (length Γ) T →
    is_unstamped_ty' (S (length Γ)) U1 →
    is_unstamped_ty' (S (length Γ)) U2 →
    Γ t⊢ₜ TAnd (TAll T U1) (TAll T U2) <:[i] TAll T (TAnd U1 U2)
| iAnd_Fld_Stp_Distr l T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ t⊢ₜ TAnd (TVMem l T1) (TVMem l T2) <:[i] TVMem l (TAnd T1 T2)
| iAnd_Typ_Stp_Distr l L U1 U2 i:
    is_unstamped_ty' (length Γ) L →
    is_unstamped_ty' (length Γ) U1 →
    is_unstamped_ty' (length Γ) U2 →
    Γ t⊢ₜ TAnd (TTMem l L U1) (TTMem l L U2) <:[i] TTMem l L (TAnd U1 U2)
| iDistr_And_Or_Stp {S T U i}:
    is_unstamped_ty' (length Γ) S →
    is_unstamped_ty' (length Γ) T →
    is_unstamped_ty' (length Γ) U →
    Γ t⊢ₜ TAnd (TOr S T) U  <:[i] TOr (TAnd S U) (TAnd T U)
| iStp_Eq i T1 T2 :
    |- T1 == T2 →
    Γ t⊢ₜ T1 <:[i] T2

where "Γ t⊢ₜ T1 <:[ i  ] T2"  := (subtype Γ i T1 T2).

(* Make [T] first argument: Hide Γ for e.g. typing examples. *)
Global Arguments iD_Typ_Abs {Γ} T _ _ _ _ _ _ _ : assert.

Scheme typed_mut_ind := Induction for typed Sort Prop
with   dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   dm_typed_mut_ind := Induction for dm_typed Sort Prop
with   path_typed_mut_ind := Induction for path_typed Sort Prop
with   subtype_mut_ind := Induction for subtype Sort Prop.

Combined Scheme typing_mut_ind from typed_mut_ind, dms_typed_mut_ind, dm_typed_mut_ind,
  path_typed_mut_ind, subtype_mut_ind.

Scheme exp_typed_mut_ind := Induction for typed Sort Prop
with   exp_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   exp_dm_typed_mut_ind := Induction for dm_typed Sort Prop
with   exp_path_typed_mut_ind := Induction for path_typed Sort Prop.

Combined Scheme exp_typing_mut_ind from exp_typed_mut_ind, exp_dms_typed_mut_ind,
  exp_dm_typed_mut_ind, exp_path_typed_mut_ind.

Lemma unstamped_path_root_is_var Γ p T i:
  Γ t⊢ₚ p : T, i → ∃ x, path_root p = var_vl x.
Proof. by elim; intros; cbn; eauto 2 using is_unstamped_path_root. Qed.

Lemma dtysem_not_utyped Γ l d T :
  Γ t⊢{ l := d } : T → ∀ σ s, d ≠ dtysem σ s.
Proof. by case. Qed.

(** ** A few derived rules, and some automation to use them in examples. *)

Hint Constructors typed dms_typed dm_typed path_typed subtype : core.

(** Ensure [eauto]'s proof search does not diverge due to transitivity. *)
Remove Hints iStp_Trans : core.
Hint Extern 10 => try_once iStp_Trans : core.

Lemma iT_Var Γ x T
  (Hl : Γ !! x = Some T) :
  Γ t⊢ₜ tv (var_vl x) : shiftN x T.
Proof. intros. apply (iT_Path (p := pv _)), iP_Var, Hl. Qed.

Lemma iT_All_I Γ e T1 T2:
  is_unstamped_ty' (length Γ) T1 →
  shift T1 :: Γ t⊢ₜ e : T2 →
  (*─────────────────────────*)
  Γ t⊢ₜ tv (vabs e) : TAll T1 T2.
Proof. apply iT_All_I_Strong. ietp_weaken_ctx. Qed.

Lemma iT_All_I_strip1 Γ e V T1 T2:
  is_unstamped_ty' (S (length Γ)) T1 →
  shift T1 :: V :: Γ t⊢ₜ e : T2 →
  (*─────────────────────────*)
  Γ |L V t⊢ₜ tv (vabs e) : TAll T1 T2.
Proof.
  intros. apply iT_All_I_Strong with (Γ' := (V :: Γ)) => //.
  rewrite /defCtxCons/=; ietp_weaken_ctx.
Qed.

Lemma iD_All Γ V T1 T2 e l:
  is_unstamped_ty' (S (length Γ)) T1 →
  shift T1 :: V :: Γ t⊢ₜ e : T2 →
  Γ |L V t⊢{ l := dpt (pv (vabs e)) } : TVMem l (TAll T1 T2).
Proof. by intros; apply iD_Val, iT_All_I_strip1. Qed.

Ltac ettrans := eapply iStp_Trans.

(* Old names: *)
Definition Sub_later_shift := iLater_Idx_Stp.
Definition Sub_later_shift_inv := iIdx_Later_Stp.

Ltac typconstructor :=
  match goal with
  | |- typed _ _ _ =>
    first [apply iT_Var | apply iT_All_I_strip1 | apply iT_All_I | constructor]
  | |- dms_typed _ _ _ => constructor
  | |- dm_typed _ _ _ _ => first [apply iD_All | constructor]
  | |- path_typed _ _ _ _ => first [apply iP_Later | constructor]
  | |- subtype _ _ _ _ _ =>
    first [apply Sub_later_shift | constructor ]
  end.
