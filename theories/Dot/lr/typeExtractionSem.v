From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr typeExtractionSyn.

Set Implicit Arguments.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx) (n: nat) (s: stamp) (g : stys).

Section typing_type_member_defs.
  Context `{!dlangG Σ}.

  (* Beware: here we must use [to_subst σ.|[ρ]], not [to_subst σ >> ρ],
     since the former is what we need to prove [D_Typ_Abs] below.
     Not sure that's still true if we change dm_to_type,
    but quite possibly yes.. *)
    (* use interp_extractedTy? *)
  Definition leadsto_envD_equiv s σ (φ : envD Σ) : iProp Σ :=
    (∃ (φ' : envD Σ),
      ⌜φ ≡ (λ ρ, φ' (to_subst σ.|[ρ]))⌝ ∧ s ↝ φ')%I.
  Arguments leadsto_envD_equiv /.
  Notation "s ↝[  σ  ] φ" := (leadsto_envD_equiv s σ φ) (at level 20).

  Import stamp_transfer.

  Lemma extraction_to_leadsto_envD_equiv T g s σ n: T ~[ n ] (g, (s, σ)) →
    wellMappedφ ⟦ g ⟧g -∗ s ↝[ σ ] ty_interp T.
  Proof.
    move => [T'] [Hl] [<- [_ /is_stamped_nclosed_ty HclT]].
    iIntros "Hm". iExists (ty_interp T'). iSplitR.
    - iIntros "!%" (ρ v). exact: interp_subst_commute.
    - iApply (wellMappedφ_apply with "Hm"). by rewrite lookup_fmap Hl.
  Qed.

  (** XXX In fact, this lemma should be provable for any φ,
      not just ⟦ T ⟧, but we haven't actually defined the
      necessary notation to state it:
  Lemma D_Typ_Sem Γ L U s σ l φ:
    Γ ⊨ φ, 1 <: U, 1 -∗
    Γ ⊨ L, 1 <: φ, 1 -∗
    (s, σ) ↝[ length Γ ] φ -∗
    Γ ⊨d dtysem σ s : TTMem l L U.
    *)
  Lemma D_Typ_Abs Γ T L U s σ l:
    Γ ⊨ TLater T, 0 <: TLater U, 0 -∗
    Γ ⊨ TLater L, 0 <: TLater T, 0 -∗
    s ↝[ σ ] ⟦ T ⟧ -∗
    Γ ⊨ { l := dtysem σ s } : TTMem l L U.
  Proof.
    iIntros "#HTU #HLT #Hs /= !>" (ρ) "#Hg".
    iDestruct "Hs" as (φ Hγφ) "Hγ"; iSplit => //=.
    iExists (φ _); iSplit. by iApply (dm_to_type_intro with "Hγ").
    iModIntro; repeat iSplitL; iIntros (v) "#HL";
      rewrite later_intuitionistically.
    - iIntros "!>". iApply Hγφ. by iApply "HLT".
    - iApply "HTU" => //. by iApply Hγφ.
  Qed.

  Lemma D_Typ Γ T s σ l:
    s ↝[ σ ] ⟦ T ⟧ -∗
    Γ ⊨ { l := dtysem σ s } : TTMem l T T.
  Proof. iIntros "#Hs"; iApply D_Typ_Abs => //; iApply Sub_Refl. Qed.
End typing_type_member_defs.
