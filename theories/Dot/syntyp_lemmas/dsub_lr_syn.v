(** * Semantic lemmas for single-delay subtyping. *)
From iris.proofmode Require Import proofmode.

From D Require Import iris_prelude swap_later_impl.
From D.Dot Require Import unary_lr dsub_lr.

Implicit Types (Σ : gFunctors).
Implicit Types (v : vl) (e : tm) (d : dm) (ds : dms) (ρ : env) (l : label).

Set Implicit Arguments.
Unset Strict Implicit.

Section DStpLemmas.
  Context `{HdotG : !dlangG Σ}.

  Lemma Stp_Refl {Γ} T i : ⊢ Γ ⊨ T <:[i] T.
  Proof. apply sStp_Refl. Qed.

  Lemma Stp_Trans {Γ T1 T2 T3 i} :
    Γ ⊨ T1 <:[i] T2 -∗ Γ ⊨ T2 <:[i] T3 -∗ Γ ⊨ T1 <:[i] T3.
  Proof. apply sStp_Trans. Qed.

  Lemma Stp_Top Γ T i :
    ⊢ Γ ⊨ T <:[i] TTop.
  Proof. rw. apply sStp_Top. Qed.

  Lemma Bot_Stp Γ T i :
    ⊢ Γ ⊨ TBot <:[i] T.
  Proof. rw. apply sBot_Stp. Qed.

  Lemma And1_Stp Γ T1 T2 i :
    ⊢ Γ ⊨ TAnd T1 T2 <:[i] T1.
  Proof. rw. apply sAnd1_Stp. Qed.
  Lemma And2_Stp Γ T1 T2 i :
    ⊢ Γ ⊨ TAnd T1 T2 <:[i] T2.
  Proof. rw. apply sAnd2_Stp. Qed.

  Lemma Stp_And Γ T U1 U2 i:
    Γ ⊨ T <:[i] U1 -∗
    Γ ⊨ T <:[i] U2 -∗
    Γ ⊨ T <:[i] TAnd U1 U2.
  Proof. rw. apply sStp_And. Qed.

  Lemma Stp_Or1 Γ T1 T2 i: ⊢ Γ ⊨ T1 <:[i] TOr T1 T2.
  Proof. rw. apply sStp_Or1. Qed.
  Lemma Stp_Or2 Γ T1 T2 i: ⊢ Γ ⊨ T2 <:[i] TOr T1 T2.
  Proof. rw. apply sStp_Or2. Qed.

  Lemma Or_Stp Γ T1 T2 U i:
    Γ ⊨ T1 <:[i] U -∗
    Γ ⊨ T2 <:[i] U -∗
    Γ ⊨ TOr T1 T2 <:[i] U.
  Proof. rw. apply sOr_Stp. Qed.

  Lemma Distr_And_Or_Stp Γ {S T U i} :
    ⊢ Γ ⊨ TAnd (TOr S T) U <:[i] TOr (TAnd S U) (TAnd T U).
  Proof. rw. apply sDistr_And_Or_Stp. Qed.

  Lemma Later_Stp_Eq {Γ T U i} `{SwapPropI Σ}:
    Γ ⊨ T <:[i.+1] U ⊣⊢
    Γ ⊨ TLater T <:[i] TLater U.
  Proof. rw. apply sLater_Stp_Eq. Qed.
  Lemma Stp_Add_Later {Γ T i}:
    ⊢ Γ ⊨ T <:[i] TLater T.
  Proof. rw. apply sStp_Add_Later. Qed.

  Lemma Stp_Sel {Γ L U p l i} :
    Γ ⊨p p : TTMem l L U, i -∗
    Γ ⊨ L <:[i] TSel p l.
  Proof. rw. apply sStp_Sel. Qed.

  Lemma Sel_Stp {Γ L U p l i}:
    Γ ⊨p p : TTMem l L U, i -∗
    Γ ⊨ TSel p l <:[i] U.
  Proof. rw. apply sSel_Stp. Qed.

  Lemma Mu_Stp_Mu {Γ} T1 T2 i `{!SwapPropI Σ} :
    iterate TLater i T1 :: Γ ⊨ T1 <:[i] T2 -∗
    Γ ⊨ TMu T1 <:[i] TMu T2.
  Proof. rw. apply sMu_Stp_Mu. Qed.

  Lemma Mu_Stp {Γ} T i : ⊢ Γ ⊨ TMu (shift T) <:[i] T.
  Proof.
    rw. rewrite (interp_commute_weaken_one T).
    apply sMu_Stp.
  Qed.

  Lemma Stp_Mu {Γ} T i : ⊢ Γ ⊨ T <:[i] TMu (shift T).
  Proof.
    rw. rewrite (interp_commute_weaken_one T).
    apply sStp_Mu.
  Qed.

  Lemma Fld_Stp_Fld {Γ T1 T2 i l} :
    Γ ⊨ T1 <:[i] T2 -∗
    Γ ⊨ TVMem l T1 <:[i] TVMem l T2.
  Proof. rw. apply sFld_Stp_Fld. Qed.

  Lemma Typ_Stp_Typ Γ L1 L2 U1 U2 i l :
    Γ ⊨ L2 <:[i] L1 -∗
    Γ ⊨ U1 <:[i] U2 -∗
    Γ ⊨ TTMem l L1 U1 <:[i] TTMem l L2 U2.
  Proof. rw. apply sTyp_Stp_Typ. Qed.

  Lemma All_Stp_All {Γ} T1 T2 U1 U2 i `{!SwapPropI Σ} :
    Γ ⊨ TLater T2 <:[i] TLater T1 -∗
    iterate TLater i.+1 (shift T2) :: Γ ⊨ TLater U1 <:[i] TLater U2 -∗
    Γ ⊨ TAll T1 U1 <:[i] TAll T2 U2.
  Proof. rw. rewrite (interp_commute_weaken_one T2). apply: sAll_Stp_All. Qed.

  Lemma Stp_Skolem_P {Γ T1 T2 i j} `{!SwapPropI Σ} :
    iterate TLater i (shift T1) :: Γ ⊨p pv (ids 0) : shift T2, i + j -∗
    (*───────────────────────────────*)
    Γ ⊨ T1 <:[i] iterate TLater j T2.
  Proof. rw. rewrite !interp_commute_weaken_one. apply: sStp_Skolem_P. Qed.

  Lemma And_All_1_Stp_Distr Γ S T1 T2 i:
    ⊢ Γ ⊨ TAnd (TAll S T1) (TAll S T2) <:[i] TAll S (TAnd T1 T2).
  Proof. rw. apply sAnd_All_1_Stp_Distr. Qed.

  Lemma And_All_2_Stp_Distr Γ S1 S2 T i:
    ⊢ Γ ⊨ TAnd (TAll S1 T) (TAll S2 T) <:[i] TAll (TOr S1 S2) T.
  Proof. rw. apply sAnd_All_2_Stp_Distr. Qed.

  Lemma And_Fld_Stp_Distr Γ l T1 T2 i:
    ⊢ Γ ⊨ TAnd (TVMem l T1) (TVMem l T2) <:[i] TVMem l (TAnd T1 T2).
  Proof. rw. apply sAnd_Fld_Stp_Distr. Qed.

  Lemma And_Typ_Stp_Distr Γ l L1 L2 U1 U2 i :
    ⊢ Γ ⊨ TAnd (TTMem l L1 U1) (TTMem l L2 U2) <:[i] TTMem l (TOr L1 L2) (TAnd U1 U2).
  Proof. rw. apply sAnd_Typ_Stp_Distr. Qed.

  Lemma Or_Fld_Stp_Distr Γ l T1 T2 i:
    ⊢ Γ ⊨ TVMem l (TOr T1 T2) <:[i] TOr (TVMem l T1) (TVMem l T2).
  Proof. rw. apply sOr_Fld_Stp_Distr. Qed.

  Lemma P_Later {Γ} p T i :
    Γ ⊨p p : TLater T, i -∗
    Γ ⊨p p : T, i.+1.
  Proof. rw. apply sP_Later. Qed.
End DStpLemmas.
