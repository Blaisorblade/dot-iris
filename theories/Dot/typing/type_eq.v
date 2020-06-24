From D.Dot Require Import syn.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

Reserved Notation "|- T1 == T2" (at level 70, T1 at level 69, only parsing).
Inductive type_equiv : Equiv ty :=
| type_equiv_later_and T1 T2 :
  |- TLater (TAnd T1 T2) == TAnd (TLater T1) (TLater T2)
| type_equiv_later_or T1 T2 :
  |- TLater (TOr T1 T2) == TOr (TLater T1) (TLater T2)
| type_equiv_later_mu T :
  |- TLater (TMu T) == TMu (TLater T)
(* Congruence closure *)
| type_equiv_top : |- TTop == TTop
| type_equiv_bot : |- TBot == TBot

| type_equiv_and T1 T2 U1 U2 : |- T1 == U1 → |- T2 == U2 → |- TAnd T1 T2 == TAnd U1 U2
| type_equiv_or T1 T2 U1 U2 : |- T1 == U1 → |- T2 == U2 → |- TOr T1 T2 == TOr U1 U2
| type_equiv_later T1 U1 : |- T1 == U1 → |- TLater T1 == TLater U1
| type_equiv_all T1 T2 U1 U2 : |- T1 == U1 → |- T2 == U2 → |- TAll T1 T2 == TAll U1 U2
| type_equiv_mu T1 U1 : |- T1 == U1 → |- TMu T1 == TMu U1

| type_equiv_vmem l T1 U1 : |- T1 == U1 → |- TVMem l T1 == TVMem l U1
| type_equiv_tmem l T1 T2 U1 U2 : |- T1 == U1 → |- T2 == U2 → |- TTMem l T1 T2 == TTMem l U1 U2

| type_equiv_sel p l : |- TSel p l == TSel p l
| type_equiv_prim b : |- TPrim b == TPrim b
| type_equiv_sing p : |- TSing p == TSing p
| type_equiv_sym : Symmetric type_equiv
| type_equiv_trans : Transitive type_equiv
where "|- T1 == T2" := (type_equiv T1 T2).

Existing Instance type_equiv.
Local Hint Constructors type_equiv : core.
Remove Hints type_equiv_sym type_equiv_trans : core.

Instance type_equiv_refl: Reflexive type_equiv.
Proof. intros T; induction T; auto. Qed.

Existing Instances type_equiv_sym type_equiv_trans.

Lemma type_equiv_laterN_and j U1 U2 :
  |- iterate TLater j (TAnd U1 U2)
  == TAnd (iterate TLater j U1) (iterate TLater j U2).
Proof. elim: j U1 U2 => [//|j IHj] U1 U2; rewrite !iterate_S; eauto 3 using type_equiv_trans. Qed.
  (* etrans; last apply type_equiv_later_and. by constructor. *)

Lemma type_equiv_laterN_or j U1 U2 :
  |- iterate TLater j (TOr U1 U2)
  == TOr (iterate TLater j U1) (iterate TLater j U2).
Proof. elim: j U1 U2 => [//|j IHj] U1 U2; rewrite !iterate_S; eauto 3 using type_equiv_trans. Qed.

Lemma type_equiv_laterN_mu j U1 :
  |- iterate TLater j (TMu U1)
  == TMu (iterate TLater j U1).
Proof. elim: j U1 => [//|j IHj] U1; rewrite !iterate_S; eauto 3 using type_equiv_trans. Qed.
