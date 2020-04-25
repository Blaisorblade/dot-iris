From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.

Set Implicit Arguments.

Implicit Types (v: vl) (e: tm) (n: nat) (s: stamp).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Section typing_type_member_defs.
  Context `{!dlangG Σ}.

  (* Beware: here we must use [∞ σ.|[ρ]], not [∞ σ >> ρ],
     since the former is what we need to prove [sD_Typ_Abs] below.
     Not sure that's still true if we change dm_to_type,
    but quite possibly yes.. *)
  (*
    Even if semantic types use infinite substitutions, we can still reuse the
    current stamping theory, based on finite substitutions.
  *)
  Import stamp_transfer.

  (* Alternative presentation *)
  Lemma sD_Typ_Sub {Γ} L1 L2 U1 U2 s σ l:
    Γ s⊨ oLater U1, 0 <: oLater U2, 0 -∗
    Γ s⊨ oLater L2, 0 <: oLater L1, 0 -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l L1 U1 -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l L2 U2.
  Proof.
    rewrite !sdtp_eq; iIntros "#HU #HL #Hd !>" (ρ Hpid) "#Hg".
    iSpecialize ("Hd" $! ρ Hpid with "Hg"); rewrite !cTMem_eq.
    iDestruct "Hd" as (ψ) "(Hφ & HLψ & HψU)".
    iExists ψ. iFrame "Hφ".
    iModIntro; repeat iSplit; iIntros (v) "#H".
    - iApply "HLψ". by iApply "HL".
    - iApply ("HU" with "Hg"). by iApply "HψU".
  Qed.

  Lemma sD_Typ0 {Γ} (T : oltyO Σ 0) s σ l:
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l T T.
  Proof.
    rewrite !sdtp_eq; iIntros "#Hs !>" (ρ Hpid) "#Hg".
    rewrite cTMem_eq; iDestruct "Hs" as (φ Hγφ) "Hγ".
    iExists (hoEnvD_inst (σ.|[ρ]) φ); iSplit.
    by iApply (dm_to_type_intro with "Hγ").
    (* Dropping [iNext], as follows, requires the instance in
    https://gitlab.mpi-sws.org/iris/iris/issues/287. *)
    iModIntro; repeat iSplit; iIntros (v) "#H "; iNext; rewrite /= (Hγφ _ _ _) //.
    (* iModIntro; repeat iSplit; iIntros (v) "#H "; rewrite /= (Hγφ _ _ _) //. *)
  Qed.

  Lemma sD_Typ_Abs {Γ} T L U s σ l:
    Γ s⊨ oLater T, 0 <: oLater U, 0 -∗
    Γ s⊨ oLater L, 0 <: oLater T, 0 -∗
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : cTMem l L U.
  Proof.
    (* iIntros "HTU HLT Hs".
    iApply (sD_Typ_Sub with "HTU HLT").
    by iApply sD_Typ0.
  Qed. *)
    rewrite !sdtp_eq; iIntros "#HTU #HLT #Hs !>" (ρ Hpid) "#Hg".
    rewrite cTMem_eq; iDestruct "Hs" as (φ Hγφ) "Hγ".
    iExists (hoEnvD_inst (σ.|[ρ]) φ); iSplit.
    by iApply (dm_to_type_intro with "Hγ").
    iModIntro; repeat iSplit; iIntros (v) "#HL"; rewrite later_intuitionistically.
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
  Proof. iIntros "#Hs"; iApply sD_Typ_Abs; by [| iIntros "!> **"]. Qed.

  Lemma D_Typ {Γ} T s σ l:
    s ↝[ σ ] V⟦ T ⟧ -∗
    Γ ⊨ { l := dtysem σ s } : TTMem l T T.
  Proof. apply sD_Typ. Qed.
End typing_type_member_defs.
