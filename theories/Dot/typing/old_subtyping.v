(** * Judgments defining the previous version of gDOT subtyping. *)
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
Inductive path_typed Γ : path → ty → nat → Prop :=
| iP_Var x T:
    Γ !! x = Some T →
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ u⊢ₚ pv (var_vl x) : shiftN x T, 0
| iP_Nat_I n:
    Γ u⊢ₚ pv (vint n): TInt, 0
| iP_Bool_I b:
    Γ u⊢ₚ pv (vbool b): TBool, 0
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
    Γ u⊢ₜ TSel p l, i <: U, i
| iSub_Sel p U {l L i}:
    Γ u⊢ₚ p : TTMem l L U, i →
    Γ u⊢ₜ L, i <: TSel p l, i

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
    Γ u⊢ₜ L2, i <: L1, i →
    Γ u⊢ₜ U1, i <: U2, i →
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
| iDistr_And_Or_Sub {S T U i}:
    is_unstamped_ty' (length Γ) S →
    is_unstamped_ty' (length Γ) T →
    is_unstamped_ty' (length Γ) U →
    Γ u⊢ₜ TAnd (TOr S T) U , i <: TOr (TAnd S U) (TAnd T U), i
| iSub_Skolem_P {T1 T2 i j}:
    is_unstamped_ty' (length Γ) T1 →
    iterate TLater i (shift T1) :: Γ u⊢ₚ pv (ids 0) : shift T2, j →
    (*───────────────────────────────*)
    Γ u⊢ₜ T1, i <: T2, j

where "Γ u⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).

Scheme unstamped_path_typed_mut_ind := Induction for path_typed Sort Prop
with   unstamped_subtype_mut_ind := Induction for subtype Sort Prop.
Combined Scheme old_pure_typing_mut_ind from unstamped_path_typed_mut_ind, unstamped_subtype_mut_ind.

Hint Constructors path_typed subtype : core.
(** Ensure [eauto]'s proof search does not diverge due to transitivity. *)
Remove Hints iSub_Trans : core.
Hint Extern 10 => try_once iSub_Trans : core.

Lemma unstamped_path_root_is_var Γ p T i:
  Γ u⊢ₚ p : T, i →
  (∃ x, path_root p = var_vl x) ∨
  (∃ l, path_root p = vlit l).
Proof. by elim; intros; cbn; eauto 3 using is_unstamped_path_root. Qed.


Ltac ettrans := eapply iSub_Trans.

Lemma iP_Later {Γ p T i} :
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₚ p : TLater T, i →
  Γ u⊢ₚ p : T, S i.
Proof.
  intros Hu Hp; apply iP_Sub with (j := 1) (T1 := TLater T) (T2 := T) in Hp;
    move: Hp; rewrite (plusnS i 0) (plusnO i); intros; by [|constructor].
Qed.

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

Lemma iP_Sub' {Γ p T1 T2 i} :
  Γ u⊢ₜ T1, i <: T2, i →
  Γ u⊢ₚ p : T1, i →
  (*───────────────────────────────*)
  Γ u⊢ₚ p : T2, i.
Proof.
  intros Hsub Hp; rewrite -(plusnO i).
  by eapply iP_Sub, Hp; rewrite plusnO.
Qed.

Ltac typconstructor_blacklist Γ :=
  lazymatch goal with
  | |- path_typed ?Γ' _ _ _ =>
  tryif (unify Γ Γ') then idtac else fail 1 "Only applicable rule is iSub_Skolem_P"
  | _ => idtac
  end.

Ltac subtypconstructor :=
  match goal with
  | |- path_typed ?Γ _ _ _ => first [apply iP_Later | constructor]
  | |- subtype ?Γ _ _ _ _ =>
    first [apply Sub_later_shift | constructor ]; typconstructor_blacklist Γ
  end.
