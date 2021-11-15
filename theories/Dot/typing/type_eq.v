From D.Dot Require Import syn.

Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (L T U : ty) (v : vl) (e : tm) (d : dm) (ds : dms) (Γ : ctx).

Reserved Notation "|- T1 == T2" (at level 70, T1 at level 69).
Reserved Notation "|-K K1 == K2" (at level 70, K1 at level 69).
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

| type_equiv_and T1 U1 T2 U2 : |- T1 == T2 → |- U1 == U2 → |- TAnd T1 U1 == TAnd T2 U2
| type_equiv_or T1 U1 T2 U2 : |- T1 == T2 → |- U1 == U2 → |- TOr T1 U1 == TOr T2 U2
| type_equiv_later T1 T2 : |- T1 == T2 → |- TLater T1 == TLater T2
| type_equiv_all S1 T1 S2 T2 : |- S1 == S2 → |- T1 == T2 → |- TAll S1 T1 == TAll S2 T2
| type_equiv_mu T1 T2 : |- T1 == T2 → |- TMu T1 == TMu T2

| type_equiv_vmem l T1 T2 : |- T1 == T2 → |- TVMem l T1 == TVMem l T2
| type_equiv_ktmem l K1 K2 : |-K K1 == K2 → |- kTTMem l K1 == kTTMem l K2

| type_equiv_ksel n p l : |- kTSel n p l == kTSel n p l
| type_equiv_prim b : |- TPrim b == TPrim b
| type_equiv_sing p : |- TSing p == TSing p
| type_equiv_lam T1 T2 : |- T1 == T2 → |- TLam T1 == TLam T2
| type_equiv_app T1 T2 p : |- T1 == T2 → |- TApp T1 p == TApp T2 p
| type_equiv_sym : Symmetric type_equiv
| type_equiv_trans : Transitive type_equiv
where "|- T1 == T2" := (type_equiv T1 T2)
with kind_equiv : Equiv kind :=
| kind_equiv_kintv L1 L2 U1 U2 : |- L1 == L2 → |- U1 == U2 → |-K kintv L1 U1 == kintv L2 U2
| kind_equiv_kpi S1 S2 K1 K2 : |- S1 == S2 → |-K K1 == K2 → |-K kpi S1 K1 == kpi S2 K2
| kind_equiv_sym : Symmetric kind_equiv
| kind_equiv_trans : Transitive kind_equiv
where "|-K K1 == K2" := (kind_equiv K1 K2).
(* XXX add extra HK-gDOT rules? *)

Scheme type_equiv_mut_ind := Induction for type_equiv Sort Prop
with   kind_equiv_mut_ind := Induction for kind_equiv Sort Prop.
Combined Scheme type_kind_eq_mut_ind from type_equiv_mut_ind, kind_equiv_mut_ind.

Existing Instances type_equiv kind_equiv.
#[local] Hint Constructors type_equiv kind_equiv : core.
#[local] Remove Hints type_equiv_sym type_equiv_trans
  kind_equiv_sym kind_equiv_trans : core.

Lemma type_equiv_refl' T : |- T == T
with kind_equiv_refl' K : |-K K == K.
Proof. all: [> destruct T | destruct K]; constructor; auto. Qed.

#[global] Instance type_equiv_refl : Reflexive type_equiv := type_equiv_refl'.
#[global] Instance kind_equiv_refl : Reflexive kind_equiv := kind_equiv_refl'.

Existing Instances type_equiv_sym type_equiv_trans kind_equiv_sym kind_equiv_trans.

#[global] Instance : Equivalence type_equiv := {}.
#[global] Instance : RewriteRelation type_equiv := {}.

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
