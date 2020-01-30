From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr typeExtractionSyn.

Set Implicit Arguments.

Implicit Types (v: vl) (e: tm) (n: nat) (s: stamp) (g : stys).

Section typing_type_member_defs.
  Context `{!dlangG Σ}.

  (* Beware: here we must use [∞ σ.|[ρ]], not [∞ σ >> ρ],
     since the former is what we need to prove [D_Typ_Abs] below.
     Not sure that's still true if we change dm_to_type,
    but quite possibly yes.. *)
  (*
    Even if semantic types use infinite substitutions, we can still reuse the
    current stamping theory, based on finite substitutions.
  *)
  Definition leadsto_envD_equiv {i} s σ (φ : hoEnvD Σ i) : iProp Σ :=
    (∃ (φ' : hoEnvD Σ i),
      ⌜φ ≡ (λ args ρ, φ' args (∞ σ.|[ρ]))⌝ ∧ s ↝n[ i ] φ')%I.
  Arguments leadsto_envD_equiv /.
  Notation "s ↝[  σ  ] φ" := (leadsto_envD_equiv s σ φ) (at level 20).

  Import stamp_transfer.

  Lemma extraction_to_leadsto_envD_equiv T g s σ n: T ~[ n ] (g, (s, σ)) →
    wellMappedφ ⟦ g ⟧g -∗ s ↝[ σ ] pty_interpO T.
  Proof.
    move => [T'] [Hl] [<- [_ /is_stamped_nclosed_ty HclT]].
    iIntros "Hm". iExists (pty_interpO T'). iSplitR.
    - iIntros "!%" (args ρ v). exact: interp_subst_commute.
    - iApply (wellMappedφ_apply with "Hm"). by rewrite lookup_fmap Hl.
  Qed.

  Lemma sD_Typ_Abs {Γ} T L U s σ l:
    Γ s⊨ oLater T, 0 <: oLater U, 0 -∗
    Γ s⊨ oLater L, 0 <: oLater T, 0 -∗
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : oLDTMem l L U.
  Proof.
    iIntros "#HTU #HLT #Hs /= !>" (ρ Hpid) "#Hg"; iSplit => //=.
    iDestruct "Hs" as (φ Hγφ) "Hγ".
    iExists (hoEnvD_inst (σ.|[ρ]) φ); iSplit.
    by iApply (dm_to_type_intro with "Hγ").
    iModIntro; repeat iSplit; iIntros (v) "#HL"; rewrite later_intuitionistically.
    - iIntros "!>". iApply Hγφ. by iApply "HLT".
    - iApply "HTU" => //. by iApply Hγφ.
  Qed.

  Lemma sD_Typ {Γ} (T : oltyO Σ 0) s σ l:
    s ↝[ σ ] T -∗
    Γ s⊨ { l := dtysem σ s } : oLDTMem l T T.
  Proof. iIntros "#Hs"; iApply sD_Typ_Abs; by [| iIntros "!> **"]. Qed.


  Lemma D_Typ_Abs {Γ} T L U s σ l:
    Γ ⊨ TLater T, 0 <: TLater U, 0 -∗
    Γ ⊨ TLater L, 0 <: TLater T, 0 -∗
    s ↝[ σ ] p⟦ T ⟧ -∗
    Γ ⊨ { l := dtysem σ s } : TTMem l L U.
  Proof. apply sD_Typ_Abs. Qed.

  Lemma D_Typ {Γ} T s σ l:
    s ↝[ σ ] p⟦ T ⟧ -∗
    Γ ⊨ { l := dtysem σ s } : TTMem l T T.
  Proof. apply sD_Typ. Qed.
End typing_type_member_defs.
