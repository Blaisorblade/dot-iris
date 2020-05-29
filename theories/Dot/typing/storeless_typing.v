(** * Judgments defining gDOT storeless typing.
Storeless typing resembles stamped typing, but also allows arbitrary values in
paths.
*)
From D.Dot Require Export syn path_repl lr_syn_aux.
From D.Dot.typing Require Export typing_aux_defs.
From D.Dot.stamping Require Export core_stamping_defs.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (L T U : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty).
Implicit Types (g : stys).

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

(**
Judgments for typing, subtyping, path and definition typing.
*)
Inductive typed Γ g : tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a value . *)
| iT_All_Ex e1 v2 T1 T2:
    Γ v⊢ₜ[ g ] e1: TAll T1 T2 →                        Γ v⊢ₜ[ g ] tv v2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ v⊢ₜ[ g ] tapp e1 (tv v2) : T2.|[v2/]

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
| iT_Mu_E v T:
    Γ v⊢ₜ[ g ] tv v: TMu T →
    (*──────────────────────*)
    Γ v⊢ₜ[ g ] tv v: T.|[v/]
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
| iT_Mu_I v T:
    Γ v⊢ₜ[ g ] tv v: T.|[v/] →
    (*──────────────────────*)
    Γ v⊢ₜ[ g ] tv v: TMu T

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
| iT_Nat_I n:
    Γ v⊢ₜ[ g ] tv (vint n): TInt
| iT_Bool_I b:
    Γ v⊢ₜ[ g ] tv (vbool b): TBool
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
where "Γ v⊢[ g ]{ l := d  } : T" := (dm_typed Γ g l d T)
with path_typed Γ g : path → ty → nat → Prop :=
| iP_Var v T:
    Γ v⊢ₜ[ g ] tv v : T →
    Γ v⊢ₚ[ g ] pv v : T, 0
(* Mnemonic: Path from SELecting a Field *)
| iP_Fld_E p T i l:
    Γ v⊢ₚ[ g ] p : TVMem l T, i →
    Γ v⊢ₚ[ g ] pself p l : T, i
| iP_Sub p T1 T2 i j :
    Γ v⊢ₜ[ g ] T1, i <: T2, i + j →
    Γ v⊢ₚ[ g ] p : T1, i →
    (*───────────────────────────────*)
    Γ v⊢ₚ[ g ] p : T2, i + j
| iP_Mu_I p T {T' i} :
    T .Tp[ p /]~ T' →
    is_stamped_ty (S (length Γ)) g T →
    Γ v⊢ₚ[ g ] p : T', i →
    Γ v⊢ₚ[ g ] p : TMu T, i
| iP_Mu_E p T {T' i} :
    T .Tp[ p /]~ T' →
    is_stamped_ty (length Γ) g T' →
    Γ v⊢ₚ[ g ] p : TMu T, i →
    Γ v⊢ₚ[ g ] p : T', i
| iP_Fld_I p T i l:
    Γ v⊢ₚ[ g ] pself p l : T, i →
    (*─────────────────────────*)
    Γ v⊢ₚ[ g ] p : TVMem l T, i
| iP_Sngl_Refl T p i :
    Γ v⊢ₚ[ g ] p : T, i →
    Γ v⊢ₚ[ g ] p : TSing p, i
| iP_Sngl_Inv p q i:
    Γ v⊢ₚ[ g ] p : TSing q, i →
    is_stamped_path (length Γ) g q →
    Γ v⊢ₚ[ g ] q : TTop, i
| iP_Sngl_Trans p q T i:
    Γ v⊢ₚ[ g ] p : TSing q, i →
    Γ v⊢ₚ[ g ] q : T, i →
    Γ v⊢ₚ[ g ] p : T, i
| iP_Sngl_E T p q l i:
    Γ v⊢ₚ[ g ] p : TSing q, i →
    Γ v⊢ₚ[ g ] pself q l : T, i →
    Γ v⊢ₚ[ g ] pself p l : TSing (pself q l), i
where "Γ v⊢ₚ[ g ] p : T , i" := (path_typed Γ g p T i)
(* Γ v⊢ₜ[ g ] T1, i1 <: T2, i2 means that TLater^i1 T1 <: TLater^i2 T2. *)
with subtype Γ g : ty → nat → ty → nat → Prop :=
| iSub_Refl i T :
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] T, i <: T, i
| iSub_Trans i2 T2 {i1 i3 T1 T3}:
    Γ v⊢ₜ[ g ] T1, i1 <: T2, i2 →
    Γ v⊢ₜ[ g ] T2, i2 <: T3, i3 →
    Γ v⊢ₜ[ g ] T1, i1 <: T3, i3
| iLater_Sub i T:
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] TLater T, i <: T, S i
| iSub_Later i T:
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] T, S i <: TLater T, i

(* "Structural" rule about indexes *)
| iSub_Add_Later T i:
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] T, i <: TLater T, i

(* "Logical" connectives *)
| iSub_Top i T :
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] T, i <: TTop, i
| iBot_Sub i T :
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] TBot, i <: T, i
| iAnd1_Sub T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ v⊢ₜ[ g ] TAnd T1 T2, i <: T1, i
| iAnd2_Sub T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ v⊢ₜ[ g ] TAnd T1 T2, i <: T2, i
| iSub_And T U1 U2 i j:
    Γ v⊢ₜ[ g ] T, i <: U1, j →
    Γ v⊢ₜ[ g ] T, i <: U2, j →
    Γ v⊢ₜ[ g ] T, i <: TAnd U1 U2, j
| iSub_Or1 T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ v⊢ₜ[ g ] T1, i <: TOr T1 T2, i
| iSub_Or2 T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ v⊢ₜ[ g ] T2, i <: TOr T1 T2, i
| iOr_Sub T1 T2 U i j:
    Γ v⊢ₜ[ g ] T1, i <: U, j →
    Γ v⊢ₜ[ g ] T2, i <: U, j →
    Γ v⊢ₜ[ g ] TOr T1 T2, i <: U, j

(* Type selections *)
| iSel_Sub p L {l U i}:
    Γ v⊢ₚ[ g ] p : TTMem l L U, i →
    Γ v⊢ₜ[ g ] TSel p l, i <: U, i
| iSub_Sel p U {l L i}:
    Γ v⊢ₚ[ g ] p : TTMem l L U, i →
    Γ v⊢ₜ[ g ] L, i <: TSel p l, i

| iSngl_pq_Sub p q {i T1 T2}:
    T1 ~Tp[ p := q ]* T2 →
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ v⊢ₚ[ g ] p : TSing q, i →
    Γ v⊢ₜ[ g ] T1, i <: T2, i
| iSngl_Sub_Sym T {p q i}:
    Γ v⊢ₚ[ g ] p : T, i →
    Γ v⊢ₜ[ g ] TSing p, i <: TSing q, i →
    Γ v⊢ₜ[ g ] TSing q, i <: TSing p, i
| iSngl_Sub_Self {p T i} :
    Γ v⊢ₚ[ g ] p : T, i →
    Γ v⊢ₜ[ g ] TSing p, i <: T, i

(* Subtyping for recursive types. Congruence, and opening in both directions. *)
| iMu_Sub_Mu T1 T2 i j:
    (iterate TLater i T1 :: Γ) v⊢ₜ[ g ] T1, i <: T2, j →
    is_stamped_ty (S (length Γ)) g T1 →
    Γ v⊢ₜ[ g ] TMu T1, i <: TMu T2, j
| iMu_Sub T i:
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] TMu (shift T), i <: T, i
| iSub_Mu T i:
    is_stamped_ty (length Γ) g T →
    Γ v⊢ₜ[ g ] T, i <: TMu (shift T), i

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types. *)
| iAll_Sub_All T1 T2 U1 U2 i:
    Γ v⊢ₜ[ g ] TLater T2, i <: TLater T1, i →
    iterate TLater (S i) (shift T2) :: Γ v⊢ₜ[ g ] TLater U1, i <: TLater U2, i →
    is_stamped_ty (length Γ) g T2 →
    Γ v⊢ₜ[ g ] TAll T1 U1, i <: TAll T2 U2, i
| iFld_Sub_Fld T1 T2 i l:
    Γ v⊢ₜ[ g ] T1, i <: T2, i →
    Γ v⊢ₜ[ g ] TVMem l T1, i <: TVMem l T2, i
| iTyp_Sub_Typ L1 L2 U1 U2 i l:
    Γ v⊢ₜ[ g ] L2, i <: L1, i →
    Γ v⊢ₜ[ g ] U1, i <: U2, i →
    Γ v⊢ₜ[ g ] TTMem l L1 U1, i <: TTMem l L2 U2, i
  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
| iAnd_All_Sub_Distr T U1 U2 i:
    is_stamped_ty (length Γ) g T →
    is_stamped_ty (S (length Γ)) g U1 →
    is_stamped_ty (S (length Γ)) g U2 →
    Γ v⊢ₜ[ g ] TAnd (TAll T U1) (TAll T U2), i <: TAll T (TAnd U1 U2), i
| iAnd_Fld_Sub_Distr l T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ v⊢ₜ[ g ] TAnd (TVMem l T1) (TVMem l T2), i <: TVMem l (TAnd T1 T2), i
| iAnd_Typ_Sub_Distr l L U1 U2 i:
    is_stamped_ty (length Γ) g L →
    is_stamped_ty (length Γ) g U1 →
    is_stamped_ty (length Γ) g U2 →
    Γ v⊢ₜ[ g ] TAnd (TTMem l L U1) (TTMem l L U2), i <: TTMem l L (TAnd U1 U2), i
| iDistr_And_Or_Sub {S T U i}:
    is_stamped_ty (length Γ) g S →
    is_stamped_ty (length Γ) g T →
    is_stamped_ty (length Γ) g U →
    Γ v⊢ₜ[ g ] TAnd (TOr S T) U , i <: TOr (TAnd S U) (TAnd T U), i

(* "Structural" rule about indexes. Only try last. *)

| iSub_Skolem_P {T1 T2 i j}:
    is_stamped_ty (length Γ) g T1 →
    iterate TLater i (shift T1) :: Γ v⊢ₚ[ g ] pv (ids 0) : shift T2, j →
    (*───────────────────────────────*)
    Γ v⊢ₜ[ g ] T1, i <: T2, j
where "Γ v⊢ₜ[ g ] T1 , i1 <: T2 , i2" := (subtype Γ g T1 i1 T2 i2).

(* Make [T] first argument: Hide [Γ] and [g] for e.g. typing examples. *)
Global Arguments iD_Typ_Abs {Γ g} T _ _ _ _ _ _ _ _ _ : assert.

Scheme exp_stamped_typed_mut_ind := Induction for typed Sort Prop
with   exp_stamped_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   exp_stamped_dm_typed_mut_ind := Induction for dm_typed Sort Prop
with   exp_stamped_path_typed_mut_ind := Induction for path_typed Sort Prop.

Combined Scheme exp_storeless_typing_mut_ind from exp_stamped_typed_mut_ind, exp_stamped_dms_typed_mut_ind,
  exp_stamped_dm_typed_mut_ind, exp_stamped_path_typed_mut_ind.

Scheme stamped_typed_mut_ind := Induction for typed Sort Prop
with   stamped_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   stamped_dm_typed_mut_ind := Induction for dm_typed Sort Prop
with   stamped_path_typed_mut_ind := Induction for path_typed Sort Prop
with   stamped_subtype_mut_ind := Induction for subtype Sort Prop.

Combined Scheme storeless_typing_mut_ind from stamped_typed_mut_ind, stamped_dms_typed_mut_ind,
  stamped_dm_typed_mut_ind, stamped_path_typed_mut_ind, stamped_subtype_mut_ind.

(** ** A few derived rules, and some automation to use them in examples. *)

Hint Constructors typed subtype dms_typed dm_typed path_typed : core.
Remove Hints iSub_Trans : core.
Hint Extern 10 => try_once iSub_Trans : core.

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

Lemma iP_Later {Γ p T i g} :
  is_stamped_ty (length Γ) g T →
  Γ v⊢ₚ[ g ] p : TLater T, i →
  Γ v⊢ₚ[ g ] p : T, S i.
Proof.
  intros Hu Hp; apply iP_Sub with (j := 1) (T1 := TLater T) (T2 := T) in Hp;
    move: Hp; rewrite (plusnS i 0) (plusnO i); intros; by [|constructor].
Qed.

Ltac ettrans := eapply iSub_Trans.

Lemma Sub_later_shift {Γ T1 T2 i j g}
  (Hs1: is_stamped_ty (length Γ) g T1)
  (Hs2: is_stamped_ty (length Γ) g T2)
  (Hsub: Γ v⊢ₜ[ g ] T1, S i <: T2, S j):
  Γ v⊢ₜ[ g ] TLater T1, i <: TLater T2, j.
Proof.
  ettrans; first exact: iLater_Sub.
  by eapply iSub_Trans, iSub_Later.
Qed.

Lemma Sub_later_shift_inv {Γ T1 T2 i j g}
  (Hs1: is_stamped_ty (length Γ) g T1)
  (Hs2: is_stamped_ty (length Γ) g T2)
  (Hsub: Γ v⊢ₜ[ g ] TLater T1, i <: TLater T2, j):
  Γ v⊢ₜ[ g ] T1, S i <: T2, S j.
Proof.
  ettrans; first exact: iSub_Later.
  by eapply iSub_Trans, iLater_Sub.
Qed.

Ltac typconstructor_blacklist Γ :=
  lazymatch goal with
  | |- path_typed ?Γ' _ _ _ _ =>
  tryif (unify Γ Γ') then idtac else fail 1 "Only applicable rule is iSub_Skolem_P"
  | _ => idtac
  end.

Ltac typconstructor :=
  match goal with
  | |- typed      ?Γ _ _ _ => first [apply iT_All_I_strip1 | apply iT_All_I | constructor]
  | |- dms_typed  ?Γ _ _ _ => constructor
  | |- dm_typed   ?Γ _ _ _ _ => first [apply iD_All | constructor]
  | |- path_typed ?Γ _ _ _ _ => first [apply iP_Later | constructor]
  | |- subtype    ?Γ _ _ _ _ _ =>
    first [apply Sub_later_shift | constructor ]; typconstructor_blacklist Γ
  end.
