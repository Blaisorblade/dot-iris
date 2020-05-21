(** * Semantic lemmas for definition typing of type definitions. *)
From stdpp Require Import gmap.
From D.Dot Require Import unary_lr.

Set Implicit Arguments.

Implicit Types (v: vl) (e: tm) (n: nat) (s: stamp).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Section typing_type_member_defs.
  Context `{!dlangG Σ}.

  Lemma sD_Typ_Abs {Γ} T L U s σ l:
    Γ s⊨ oLater T, 0 <: oLater U, 0 -∗
    Γ s⊨ oLater L, 0 <: oLater T, 0 -∗
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l L U.
  Proof.
    rewrite !sdtp_eq; iIntros "#HTU #HLT #Hs !>" (ρ Hpid) "#Hg".
    rewrite cTMem_eq; iDestruct "Hs" as (φ Hγφ) "Hγ".
    iExists (hoEnvD_inst (σ.|[ρ]) φ); iSplit.
    by iApply (dm_to_type_intro with "Hγ").
    iModIntro; repeat iSplit; iIntros (v) "#HL";
      rewrite /= later_intuitionistically.
    - iIntros "!>". iApply Hγφ. by iApply "HLT".
    - iApply ("HTU" with "Hg"). by iApply Hγφ.
  Qed.

  Lemma D_Typ_Abs {Γ} T L U s σ l:
    Γ ⊨ TLater T, 0 <: TLater U, 0 -∗
    Γ ⊨ TLater L, 0 <: TLater T, 0 -∗
    s ↝[ σ ] V⟦ T ⟧ -∗
    Γ ⊨ { l := dtysem σ s } : TTMem l L U.
  Proof. apply sD_Typ_Abs. Qed.

  Lemma sD_Typ {Γ} (T : oltyO Σ 0) s σ l:
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l T T.
  Proof. by iIntros "#Hs"; iApply sD_Typ_Abs; [> iApply sSub_Refl ..|]. Qed.

  Lemma D_Typ {Γ} T s σ l:
    s ↝[ σ ] V⟦ T ⟧ -∗
    Γ ⊨ { l := dtysem σ s } : TTMem l T T.
  Proof. apply sD_Typ. Qed.
End typing_type_member_defs.
