(** * Judgments defining gDOT "storeless" typing.
This is not our official type system and is not documented in the paper; it
is only used as part of safety proofs of "syntactically ill-typed" examples.
The name is historic.
Storeless typing resembles stamped typing, but used to allow arbitrary values
in paths.
*)
From D.Dot Require Export syn path_repl lr_syn_aux.
From D.Dot Require Export typing_aux_defs old_subtyping.
From D.Dot Require Export core_stamping_defs.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (L T U : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty).

(* Hack *)
Notation "Γ v⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2)
  (at level 74, T1, T2, i1, i2 at next level, only parsing).


Reserved Notation "Γ v⊢ₜ e : T"
  (at level 74, e, T at next level,
  format "'[' '[' Γ ']'  '/' v⊢ₜ  '[' e ']'  :  '[' T ']' ']'").
Reserved Notation "Γ v⊢{ l := d } : T"
  (at level 74, l, d, T at next level,
   format "'[' '[' Γ  ']' '/' '[' v⊢{  l  :=  d  } ']' :  '[' T ']' ']'").
Reserved Notation "Γ v⊢ds ds : T"
  (at level 74, ds, T at next level,
  format "'[' '[' Γ  ']' '/' v⊢ds  '[' ds ']'  :  T ']'" ).

(**
Judgments for typing, subtyping, path and definition typing.
*)
Inductive typed Γ : tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a variable. *)
| iT_All_Ex e1 x2 T1 T2:
    Γ v⊢ₜ e1: TAll T1 T2 →                        Γ v⊢ₜ tv (vvar x2) : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ v⊢ₜ tapp e1 (tv (vvar x2)) : T2.|[vvar x2/]

| iT_All_E_p p2 e1 T1 T2 T2':
    T2 .Tp[ p2 /]~ T2' →
    is_unstamped_ty' (length Γ) T2' →
    Γ v⊢ₜ e1: TAll T1 T2 →
    Γ u⊢ₚ p2 : T1, 0 →
    (*────────────────────────────────────────────────────────────*)
    Γ v⊢ₜ tapp e1 (path2tm p2) : T2'
(** Non-dependent application; allowed for any argument. *)
| iT_All_E e1 e2 T1 T2:
    Γ v⊢ₜ e1: TAll T1 (shift T2) →      Γ v⊢ₜ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ v⊢ₜ tapp e1 e2 : T2
| iT_Obj_E e T l:
    Γ v⊢ₜ e : TVMem l T →
    (*─────────────────────────*)
    Γ v⊢ₜ tproj e l : T
(** Introduction forms *)
| iT_All_I_Strong e T1 T2 Γ':
    ⊢G Γ >>▷* Γ' →
    (* T1 :: Γ' v⊢ₜ e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    shift T1 :: Γ' v⊢ₜ e : T2 →
    (*─────────────────────────*)
    Γ v⊢ₜ tv (vabs e) : TAll T1 T2
| iT_Obj_I ds T:
    Γ |L T v⊢ds ds: T →
    (*──────────────────────*)
    Γ v⊢ₜ tv (vobj ds): TMu T
(** "General" rules *)
| iT_ISub e T1 T2 i :
    Γ v⊢ₜ T1, 0 <: T2, i → Γ v⊢ₜ e : T1 →
    (*───────────────────────────────*)
    Γ v⊢ₜ iterate tskip i e : T2
| iT_Path p T :
    Γ u⊢ₚ p : T, 0 →
    (*───────────────────────────────*)
    Γ v⊢ₜ path2tm p : T

(** Primitives. *)
| iT_Un u e1 B1 Br (Hu : un_op_syntype u B1 Br) :
    Γ v⊢ₜ e1 : TPrim B1 →
    Γ v⊢ₜ tun u e1 : TPrim Br
| iT_Bin b e1 e2 B1 B2 Br (Hu : bin_op_syntype b B1 B2 Br) :
    Γ v⊢ₜ e1 : TPrim B1 →
    Γ v⊢ₜ e2 : TPrim B2 →
    Γ v⊢ₜ tbin b e1 e2 : TPrim Br
| iT_If e e1 e2 T :
    Γ v⊢ₜ e: TBool →
    Γ v⊢ₜ e1 : T →
    Γ v⊢ₜ e2 : T →
    Γ v⊢ₜ tif e e1 e2 : T
where "Γ v⊢ₜ e : T" := (typed Γ e T)
with dms_typed Γ : dms → ty → Prop :=
| iD_Nil : Γ v⊢ds [] : TTop
(* This demands definitions and members to be defined in aligned lists. *)
| iD_Cons l d ds T1 T2:
    Γ v⊢{ l := d } : T1 →
    Γ v⊢ds ds : T2 →
    dms_hasnt ds l →
    (*──────────────────────*)
    Γ v⊢ds (l, d) :: ds : TAnd T1 T2
where "Γ v⊢ds ds : T" := (dms_typed Γ ds T)
with dm_typed Γ : label → dm → ty → Prop :=
| iD_Typ_Abs_new T l L U :
    nclosed T (length Γ) →
    Γ v⊢ₜ L, 0 <: TLater T, 0 →
    Γ v⊢ₜ TLater T, 0 <: U, 0 →
    Γ v⊢{ l := dtysyn T } : TTMem l L U

| iD_Typ_Abs_old T l L U s σ:
    nclosed T (length Γ) →
    Γ v⊢ₜ L, 0 <: TLater T, 0 →
    Γ v⊢ₜ TLater T, 0 <: U, 0 →
    (* Yeah, the actual σ and s don't matter here. *)
    Γ v⊢{ l := dtysem σ s } : TTMem l L U
| iD_Val l v T:
    Γ v⊢ₜ tv v : T →
    Γ v⊢{ l := dpt (pv v) } : TVMem l T
| iD_Path l p T:
    Γ u⊢ₚ p : T, 0 →
    Γ v⊢{ l := dpt p } : TVMem l T
| iD_Val_New l T ds:
    TAnd (TLater T) (TSing (pself (pv (ids 1)) l)) :: Γ v⊢ds ds : T →
    Γ v⊢{ l := dpt (pv (vobj ds)) } : TVMem l (TMu T)
| iD_Path_Sub T1 T2 p l:
    Γ v⊢ₜ T1, 0 <: T2, 0 →
    Γ v⊢{ l := dpt p } : TVMem l T1 →
    Γ v⊢{ l := dpt p } : TVMem l T2
where "Γ v⊢{ l := d  } : T" := (dm_typed Γ l d T).

(* Make [T] first argument: Hide [Γ] and [g] for e.g. typing examples. *)
#[global] Arguments iD_Typ_Abs_old {Γ} T _ _ _ _ _ _ _ _ : assert.

Scheme storeless_typed_mut_ind := Induction for typed Sort Prop
with   storeless_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   storeless_dm_typed_mut_ind := Induction for dm_typed Sort Prop.

Combined Scheme storeless_typing_mut_ind from storeless_typed_mut_ind,
  storeless_dms_typed_mut_ind, storeless_dm_typed_mut_ind.

(** ** A few derived rules, and some automation to use them in examples. *)

Hint Constructors typed subtype dms_typed dm_typed path_typed : core.
Remove Hints iSub_Trans : core.
Hint Extern 10 => try_once iSub_Trans : core.

Lemma iT_Path' Γ v T
  (Ht : Γ u⊢ₚ pv v : T, 0) : Γ v⊢ₜ tv v : T.
Proof. exact: (iT_Path _ (p := pv _)). Qed.

Lemma iT_Nat_I Γ n : Γ v⊢ₜ tv (vint n): TInt.
Proof. apply iT_Path'; constructor. Qed.

Lemma iT_Bool_I Γ b : Γ v⊢ₜ tv (vbool b): TBool.
Proof. apply iT_Path'; constructor. Qed.

Lemma iT_All_I Γ e T1 T2 :
  shift T1 :: Γ v⊢ₜ e : T2 →
  (*─────────────────────────*)
  Γ v⊢ₜ tv (vabs e) : TAll T1 T2.
Proof. apply iT_All_I_Strong. ietp_weaken_ctx. Qed.

Lemma iT_All_I_strip1 Γ e V T1 T2:
  shift T1 :: V :: Γ v⊢ₜ e : T2 →
  (*─────────────────────────*)
  Γ |L V v⊢ₜ tv (vabs e) : TAll T1 T2.
Proof.
  intros. apply (iT_All_I_Strong (Γ' := (V :: Γ))) => //.
  rewrite /defCtxCons/=; ietp_weaken_ctx.
Qed.

Lemma iD_All Γ V T1 T2 e l:
  shift T1 :: V :: Γ v⊢ₜ e : T2 →
  Γ |L V v⊢{ l := dpt (pv (vabs e)) } : TVMem l (TAll T1 T2).
Proof. by intros; apply iD_Val, iT_All_I_strip1. Qed.

Lemma iT_Var {Γ x T}
  (Hx : Γ !! x = Some T) :
  Γ v⊢ₜ tv (vvar x) : shiftN x T.
Proof. apply iT_Path'. eauto. Qed.

Lemma iP_VarT {Γ x T}  :
  Γ v⊢ₜ tv (vvar x) : T →
  Γ u⊢ₚ pv (vvar x) : T, 0.
Proof.
  move E: (tv (vvar x)) => t; induction 1; simplify_eq/=;
    last by destruct p; simplify_eq/=.
  destruct i; last by [simplify_eq]; rewrite iterate_0 in E; simplify_eq/=.
  eapply iP_ISub'; eauto.
Qed.

Lemma iT_Mu_E {Γ x T}:
  Γ v⊢ₜ tv (vvar x): TMu T →
  is_unstamped_ty' (length Γ).+1 T →
  Γ v⊢ₜ tv (vvar x): T.|[vvar x/].
Proof. move => Hx Hu. by eapply iT_Path', iP_Mu_E', iP_VarT, Hx. Qed.

Lemma iT_Mu_I {Γ x T}:
  Γ v⊢ₜ tv (vvar x): T.|[vvar x/] →
  is_unstamped_ty' (length Γ).+1 T →
  Γ v⊢ₜ tv (vvar x): TMu T.
Proof. move => Hx Hu. by eapply iT_Path', iP_Mu_I', iP_VarT, Hx. Qed.

Ltac typconstructor :=
  match goal with
  | |- typed      ?Γ _ _ => first [
    apply iT_All_I_strip1 | apply iT_All_I |
    apply iT_Var |
    apply iT_Nat_I | apply iT_Bool_I |
    apply iT_Mu_E | apply iT_Mu_I |
    constructor]
  | |- dms_typed  ?Γ _ _ => constructor
  | |- dm_typed   ?Γ _ _ _ => first [apply iD_All | constructor]
  | |- path_typed ?Γ _ _ _ => first [subtypconstructor]
  | |- subtype    ?Γ _ _ _ _ => subtypconstructor
  end.
