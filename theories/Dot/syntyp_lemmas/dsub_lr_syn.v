(** * Semantic lemmas for single-delay subtyping. *)
From iris.proofmode Require Import tactics.

From D Require Import iris_prelude swap_later_impl.
From D.Dot Require Import unary_lr dsub_lr.

Implicit Types (Σ : gFunctors).
Implicit Types (v : vl) (e : tm) (d : dm) (ds : dms) (ρ : env) (l : label).

Set Suggest Proof Using.
Set Default Proof Using "Type*".
Set Implicit Arguments.
Unset Strict Implicit.

Section DStpLemmas.
  Context `{HdotG : !dlangG Σ}.

  Lemma Mu_Stp_Mu {Γ} T1 T2 i `{!SwapPropI Σ}:
    iterate TLater i T1 :: Γ ⊨ T1 <:[i] T2 -∗
    Γ ⊨ TMu T1 <:[i] TMu T2.
  Proof.
    rewrite /istpd -sMu_Stp_Mu.
    by rewrite fmap_cons (iterate_TLater_oLater i T1).
  Qed.

  Lemma Mu_Stp {Γ} T i : ⊢ Γ ⊨ TMu (shift T) <:[i] T.
  Proof.
    rewrite /istpd; cbn -[sstpd].
    rewrite (interp_commute_weaken_one T).
    apply sMu_Stp.
  Qed.

  Lemma Stp_Mu {Γ} T i : ⊢ Γ ⊨ T <:[i] TMu (shift T).
  Proof.
    rewrite /istpd; cbn -[sstpd].
    rewrite (interp_commute_weaken_one T).
    apply sStp_Mu.
  Qed.

  Lemma All_Stp_All {Γ} T1 T2 U1 U2 i `{!SwapPropI Σ}:
    Γ ⊨ TLater T2 <:[i] TLater T1 -∗
    iterate TLater i.+1 (shift T2) :: Γ ⊨ TLater U1 <:[i] TLater U2 -∗
    Γ ⊨ TAll T1 U1 <:[i] TAll T2 U2.
  Proof.
    rewrite /istpd fmap_cons iterate_TLater_oLater.
    rewrite (interp_commute_weaken_one T2).
    apply: sAll_Stp_All.
  Qed.

  Lemma Stp_Skolem_P {Γ T1 T2 i j} `{!SwapPropI Σ} :
    iterate TLater i (shift T1) :: Γ ⊨p pv (ids 0) : shift T2, i + j -∗
    (*───────────────────────────────*)
    Γ ⊨ T1 <:[i] iterate TLater j T2.
  Proof.
    rewrite /iptp /istpd fmap_cons !iterate_TLater_oLater !interp_commute_weaken_one.
    exact: sStp_Skolem_P.
  Qed.
End DStpLemmas.
