(** * Prove syntactic translation from old unstamped typing to typing. *)
From D Require Import tactics succ_notation.
(* Beware the order of imports! We want [subtyping] and [typing] to be preferred. *)
From D.Dot Require Import old_subtyping old_unstamped_typing unstampedness_binding.
From D.Dot Require Import subtyping typing.

Implicit Types (L T U : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty).

Set Implicit Arguments.
Unset Strict Implicit.
Set Suggest Proof Using.
Set Default Proof Using "Type".

Local Lemma iP_ISub_Der Γ i j T1 T2 p :
  Γ t⊢ₜ iterate TLater i T1 <:[ 0 ] iterate TLater (i + j) T2 →
  Γ t⊢ₚ p : T1, i →
  Γ t⊢ₚ p : T2, i + j.
Proof. rewrite -iterate_comp -iLaterN0_Stp_Eq; eapply iP_ISub_Alt. Qed.

Local Definition renew_path_typed_def Γ p T i (HT : Γ u⊢ₚ p : T, i) := Γ t⊢ₚ p : T, i.
Local Definition renew_subtype_def Γ T1 i1 T2 i2 (HT: Γ u⊢ₜ T1, i1 <: T2, i2) :=
  Γ t⊢ₜ iterate TLater i1 T1 <:[ 0 ] iterate TLater i2 T2.
Arguments renew_subtype_def /.
Arguments renew_path_typed_def /.

Theorem renew_subtyping_mut Γ :
  (∀ p T i (HT : Γ u⊢ₚ p : T, i), renew_path_typed_def HT) ∧
  (∀ T1 i1 T2 i2 (HT: Γ u⊢ₜ T1, i1 <: T2, i2), renew_subtype_def HT).
Proof.
  apply old_pure_typing_mut_ind; clear Γ; cbn; intros *; try by [intros;
    eauto 2 using iP_ISub_Der, iP_Sngl_Trans, iP_Mu_E, iP_Mu_I];
    rewrite -?iLaterN0_Stp_Eq; eauto 2; try by rewrite iterate_Sr.
  - move=> _ IH1 _ IH2.
    ettrans; last eapply iStp_Eq, symmetry, type_equiv_laterN_and; auto 2.
  - move=> _ IH1 _ IH2.
    ettrans; first eapply iStp_Eq, type_equiv_laterN_or; auto 2.
  - move=> _ IH1.
    ettrans; first eapply iStp_Eq, type_equiv_laterN_mu.
    ettrans; last eapply iStp_Eq, symmetry, type_equiv_laterN_mu.
    auto 2.
  - move=> _ IH1. apply iStp_Skolem_P. by rewrite iterate_0 TLater_subst.
Qed.

Lemma renew_path_typed Γ p T i (HT : Γ u⊢ₚ p : T, i) : Γ t⊢ₚ p : T, i.
Proof. by apply renew_subtyping_mut. Qed.
Lemma renew_subtype Γ T1 i1 T2 i2 (HT: Γ u⊢ₜ T1, i1 <: T2, i2) :
  Γ t⊢ₜ iterate TLater i1 T1 <:[ 0 ] iterate TLater i2 T2.
Proof. by apply renew_subtyping_mut. Qed.

Local Definition renew_typed_def Γ e T (HT: Γ u⊢ₜ e : T) := Γ t⊢ₜ e : T.
Local Definition renew_dms_typed_def Γ ds T (HT: Γ u⊢ds ds : T) := Γ t⊢ds ds : T.
Local Definition renew_dm_typed_def Γ l d T (HT : Γ u⊢{ l := d } : T) := Γ t⊢{ l := d } : T.
Arguments renew_typed_def /.
Arguments renew_dms_typed_def /.
Arguments renew_dm_typed_def /.

Theorem renew_typing_mut Γ :
  (∀ e T (HT: Γ u⊢ₜ e : T), renew_typed_def HT) ∧
  (∀ ds T (HT: Γ u⊢ds ds : T), renew_dms_typed_def HT) ∧
  (∀ l d T (HT : Γ u⊢{ l := d } : T), renew_dm_typed_def HT).
Proof.
  apply old_unstamped_typing_mut_ind; clear Γ; cbn; intros *; try by [intros;
    hnf in *; eauto 3 using renew_path_typed].
  - move=> /renew_subtype + _; rewrite iterate_0. apply iT_ISub'.
  - move=> + /renew_subtype + /renew_subtype.
    rewrite !(iterate_0, iterate_S) => Hu.
    eapply iD_Typ_Abs, is_unstamped_nclosed_ty, Hu.
  - move=> /renew_subtype; rewrite !(iterate_0, iterate_S) => Hsub _ IHt.
    apply /iD_Path_Sub /IHt /Hsub.
Qed.

Theorem renew_typed Γ e T (HT: Γ u⊢ₜ e : T) : Γ t⊢ₜ e : T.
Proof. by apply renew_typing_mut. Qed.
Lemma renew_dms_typed Γ ds T (HT: Γ u⊢ds ds : T) : Γ t⊢ds ds : T.
Proof. by apply renew_typing_mut. Qed.
Lemma renew_dm_typed Γ l d T (HT : Γ u⊢{ l := d } : T) : Γ t⊢{ l := d } : T.
Proof. by apply renew_typing_mut. Qed.
