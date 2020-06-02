(** * Judgments defining gDOT path- and sub- typing.
This judgment allowing only variables in paths, and not arbitrary values.
*)
From D Require Import tactics.
From D.Dot Require Export syn path_repl lr_syn_aux.
From D.Dot.typing Require Export typing_aux_defs type_eq.
From D.Dot.stamping Require Export core_stamping_defs.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (L T U : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty).

Reserved Notation "Γ t⊢ₚ p : T , i" (at level 74, p, T, i at next level).
Reserved Notation "Γ t⊢ₜ T1 <:[ i  ] T2" (at level 74, T1, T2 at next level).

Inductive path_typed Γ : path → ty → nat → Prop :=
| iP_Var x T:
    Γ !! x = Some T →
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ t⊢ₚ pv (var_vl x) : shiftN x T, 0
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
    atomic_path_root q →
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
    Γ t⊢ₜ T <:[i] TLater T

(* "Logical" connectives *)
| iStp_Top i T :
    Γ t⊢ₜ T <:[i] TTop
| iBot_Stp i T :
    Γ t⊢ₜ TBot <:[i] T
| iAnd1_Stp T1 T2 i:
    Γ t⊢ₜ TAnd T1 T2 <:[i] T1
| iAnd2_Stp T1 T2 i:
    Γ t⊢ₜ TAnd T1 T2 <:[i] T2
| iStp_And T U1 U2 i:
    Γ t⊢ₜ T <:[i] U1 →
    Γ t⊢ₜ T <:[i] U2 →
    Γ t⊢ₜ T <:[i] TAnd U1 U2
| iStp_Or1 T1 T2 i:
    Γ t⊢ₜ T1 <:[i] TOr T1 T2
| iStp_Or2 T1 T2 i:
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
    Γ t⊢ₜ TMu T1 <:[i] TMu T2
| iMu_Stp T i:
    Γ t⊢ₜ TMu (shift T) <:[i] T
| iStp_Mu T i:
    Γ t⊢ₜ T <:[i] TMu (shift T)

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types. *)
| iAll_Stp_All T1 T2 U1 U2 i:
    Γ t⊢ₜ TLater T2 <:[i] TLater T1 →
    iterate TLater (S i) (shift T2) :: Γ t⊢ₜ TLater U1 <:[i] TLater U2 →
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
    Γ t⊢ₜ TAnd (TAll T U1) (TAll T U2) <:[i] TAll T (TAnd U1 U2)
| iAnd_Fld_Stp_Distr l T1 T2 i:
    Γ t⊢ₜ TAnd (TVMem l T1) (TVMem l T2) <:[i] TVMem l (TAnd T1 T2)
| iAnd_Typ_Stp_Distr l L U1 U2 i:
    Γ t⊢ₜ TAnd (TTMem l L U1) (TTMem l L U2) <:[i] TTMem l L (TAnd U1 U2)
| iDistr_And_Or_Stp {S T U i}:
    Γ t⊢ₜ TAnd (TOr S T) U  <:[i] TOr (TAnd S U) (TAnd T U)
| iStp_Eq i T1 T2 :
    |- T1 == T2 →
    Γ t⊢ₜ T1 <:[i] T2

where "Γ t⊢ₜ T1 <:[ i  ] T2"  := (subtype Γ i T1 T2).

Scheme path_typed_mut_ind := Induction for path_typed Sort Prop
with   subtype_mut_ind := Induction for subtype Sort Prop.
Combined Scheme pure_typing_mut_ind from path_typed_mut_ind, subtype_mut_ind.

Hint Constructors path_typed subtype : core.

(** Ensure [eauto]'s proof search does not diverge due to transitivity. *)
Remove Hints iStp_Trans : core.
Hint Extern 10 => try_once iStp_Trans : core.

Lemma unstamped_path_root_is_var Γ p T i:
  Γ t⊢ₚ p : T, i →
  atomic_path_root p.
Proof. by elim; eauto 3. Qed.

Ltac ettrans := eapply iStp_Trans.
