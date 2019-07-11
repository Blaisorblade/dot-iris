From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr synLemmas typeExtractionSyn.

Set Implicit Arguments.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx) (n: nat) (s: stamp).
Notation sγmap := (gmap stamp gname).
Implicit Types (g : stys) (sγ : sγmap).

Section interp_equiv.
  Context `{!dlangG Σ}.

  Implicit Types (φ: envD Σ).

  (** This interpretation is too naive: it substitutes σ into T' *before* applying our semantics,
      but we will not be able to do this when we use saved propositions to pre-interpret T'. *)
  Definition interp_extractedTy_naive: extractionResult -> envD Σ :=
    λ gsσ ρ v,
    let '(g, (s, σ)) := gsσ in
    (∃ T' : ty, ⌜g !! s = Some T'⌝ ∧ ⟦ T'.|[to_subst σ] ⟧ ρ v)%I.

  (** We can relate the  ⟦ T ⟧ with the naive stamp semantics at all environments. *)
  Lemma extraction_envD_equiv_naive g s σ T n ρ v:
    T ~[ n ] (g, (s, σ)) →
    ⟦ T ⟧ ρ v ≡ interp_extractedTy_naive (g, (s, σ)) ρ v.
  Proof.
    cbn; intros (T' & -> & <- & HclT & HclT').
    iSplit; iIntros "H"; [| iDestruct "H" as (T'' Heq) "?" ]; naive_solver.
  Qed.

  (** However, a stamp semantics that carries over to saved predicates must use
      σ in ρ. And the result is only equivalent for closed ρ with the expected length. *)
  Definition interp_extractedTy: (ty * vls) → envD Σ :=
    λ '(T, σ) ρ v,
    (⟦ T ⟧ (to_subst σ.|[ρ]) v)%I.
  Notation "⟦ T ⟧ [ σ ]" := (interp_extractedTy (T, σ)).

  Definition envD_equiv n φ1 φ2: iProp Σ :=
    (∀ ρ v, ⌜ length ρ = n ⌝ → ⌜ cl_ρ ρ ⌝ → φ1 (to_subst ρ) v ≡ φ2 (to_subst ρ) v)%I.
  Notation "φ1 ≈[  n  ] φ2" := (envD_equiv n φ1 φ2) (at level 70).

  Lemma extraction_envD_equiv g s σ T n:
    T ~[ n ] (g, (s, σ)) →
    (∃ T', ⌜ g !! s = Some T'⌝ ∧
        ⟦ T ⟧ ≈[ n ] ⟦ T' ⟧ [ σ ])%I.
  Proof.
    iIntros ((T' & -> & <- & HclT & HclT')). iExists _; iSplit => //.
    iIntros (ρ v <- Hclρ). by rewrite interp_subst_commute.
  Qed.

  (** envD_equiv commutes with substitution. *)
  Lemma envD_equiv_subst g T m n ξ s1 σ1 s2 σ2:
    T ~[ m ] (g, (s1, σ1)) →
    T.|[to_subst ξ] ~[ n ] (g, (s2, σ2)) →
    length ξ = m →
    nclosed_σ ξ n →
    (∃ T1 T2, ⌜ g !! s1 = Some T1⌝ ∧ ⌜ g !! s2 = Some T2 ⌝ ∧
    ⟦ T1 ⟧ [ σ1.|[to_subst ξ] ] ≈[ n ] ⟦ T2 ⟧ [ σ2 ])%I.
  Proof.
    rewrite /interp_extractedTy; iIntros ((T1 & -> & Heq1 & Hclσ1 & HclT1) (T2 & -> & Heq2 & Hclσ2 & HclT2) Hlenξ Hclξ).
    iExists _, _; repeat iSplit => //; iIntros (ρ v Hlenρ Hclρ) "/= !%"; subst.
    have Hclσ1ξ: nclosed_σ σ1.|[to_subst ξ] (length ρ). exact: nclosed_σ_to_subst.
    have Hrew: T2.|[to_subst σ2.|[to_subst ρ]] = T1.|[to_subst σ1.|[to_subst ξ].|[to_subst ρ]].
    by erewrite !subst_compose; rewrite ?map_length ?Heq1 ?Heq2.
    rewrite (interp_subst_ids T1 _ _) (interp_subst_ids T2 _ _) ?Hrew //; exact: nclosed_σ_to_subst.
  Qed.

  (* To give a definitive version of wellMapped, we need stampHeap to be stored in a resource. Here it is: *)
  Definition wellMapped g : iProp Σ :=
    (□∀ s T, ⌜ g !! s = Some T⌝ → s ↝ ⟦ T ⟧)%I.
  Instance wellMapped_persistent g: Persistent (wellMapped g) := _.
  Global Arguments wellMapped: simpl never.

  (** We can transfer one mapping from [g] into Iris resources. *)
  Lemma transferOne sγ g s T :
    sγ !! s = None → allGs sγ ∧ wellMapped g ==∗
    ∃ sγ', ⌜gdom sγ' ≡ {[s]} ∪ gdom sγ⌝ ∧ allGs sγ' ∧ wellMapped (<[s := T]> g).
  Proof.
    iIntros (HsFresh) "[Hallsγ #Hwmg]".
    iMod (saved_ho_sem_type_alloc 0 (vopen (ty_interp T))) as (γ) "Hγ".
    iMod (gen_iheap_alloc _ _ γ HsFresh with "Hallsγ") as "[Hallsγ Hs]".
    iExists (<[s:=γ]> sγ); iModIntro; iFrame; iSplit. by rewrite dom_insert.
    iAssert (s ↝ ⟦ T ⟧)%I as "#Hmaps {Hγ Hs}". iExists γ. by iFrame.
    iIntros (s' T' Hlook) "!>". destruct (decide (s' = s)) as [->|Hne].
    - suff ->: T' = T by []. move: Hlook. by rewrite lookup_insert => -[->].
    - rewrite lookup_insert_ne // in Hlook. by iApply "Hwmg".
  Qed.

  Notation freshMappings g sγ := (∀ s, s ∈ gdom g → sγ !! s = None).

  Lemma freshMappings_split s T g sγ :
    freshMappings (<[s:=T]> g) sγ → sγ !! s = None ∧ freshMappings g sγ.
  Proof.
    intros Hdom; split => [|s' Hs']; apply Hdom;
    rewrite dom_insert; set_solver.
  Qed.

  Lemma transfer' g sγ : freshMappings g sγ → allGs sγ ==∗
    ∃ sγ', ⌜gdom sγ' ≡ gdom g ∪ gdom sγ⌝ ∧ allGs sγ' ∧ wellMapped g.
  Proof.
    elim g using map_ind.
    - iIntros "/=" (H) "Hallsγ !>". iExists sγ; iFrame; iSplit.
      + by rewrite dom_empty left_id.
      + by iIntros (???).
    - move => /= {g} s T g Hsg IH /freshMappings_split [Hssγ Hdom]. iIntros "Hallsγ".
      iMod (IH Hdom with "Hallsγ") as (sγ' Hsγ') "Hown".
      iMod (transferOne sγ' g s T with "Hown") as (sγ'' Hsγ'') "Hown".
      + eapply (not_elem_of_dom (D := gset stamp)).
        rewrite Hsγ' not_elem_of_union !not_elem_of_dom; by split.
      + iExists sγ''; iFrame; iIntros "!%".
        by rewrite Hsγ'' Hsγ' dom_insert union_assoc.
  Qed.

  Lemma transfer g sγ : freshMappings g sγ → allGs sγ ==∗ wellMapped g.
  Proof.
    iIntros (Hs) "H". by iMod (transfer' sγ Hs with "H") as (sγ' ?) "[_ $]".
  Qed.

  Lemma transfer_empty g : allGs ∅ ==∗ wellMapped g.
  Proof. exact: transfer. Qed.
End interp_equiv.

Section typing_type_member_defs.
  Context `{!dlangG Σ}.

  Definition leadsto_envD_equiv (sσ: extractedTy) n (φ : envD Σ) : iProp Σ :=
    let '(s, σ) := sσ in
    (⌜nclosed_σ σ n⌝ ∧ ∃ (φ' : envD Σ), s ↝ φ' ∗ envD_equiv n φ (λ ρ, φ' (to_subst σ.|[ρ])))%I.
  Arguments leadsto_envD_equiv /.
  Notation "sσ ↝[  n  ] φ" := (leadsto_envD_equiv sσ n φ) (at level 20).

  Lemma extraction_to_leadsto_envD_equiv T g sσ n: T ~[ n ] (g, sσ) →
    wellMapped g -∗ sσ ↝[ n ] ty_interp T.
  Proof.
    move: sσ => [s σ] [T'] [Hl] [<-] [Hclσ HclT] /=. iIntros "Hm".
    iSplit => //; iExists (ty_interp T'); iSplitL; [iApply "Hm" | ];
    iIntros "!% //" (ρ v <- Hclρ).
    exact: interp_subst_commute.
  Qed.

  (** XXX In fact, this lemma should be provable for any φ,
      not just ⟦ T ⟧, but we haven't actually defined the
      necessary notation to state it:
  Lemma D_Typ_Sem Γ L U s σ l φ:
    Γ ⊨ [φ, 1] <: [U, 1] -∗
    Γ ⊨ [L, 1] <: [φ, 1] -∗
    (s, σ) ↝[ length Γ ] φ -∗
    Γ ⊨d dtysem σ s : TTMem l L U.
    *)
  Lemma D_Typ Γ T L U s σ l:
    Γ ⊨ [T, 1] <: [U, 1] -∗
    Γ ⊨ [L, 1] <: [T, 1] -∗
    (s, σ) ↝[ length Γ ] ⟦ T ⟧ -∗
    Γ ⊨d{ l := dtysem σ s } : TTMem l L U.
  Proof.
    iIntros "#HTU #HLT #[% Hs] /=". iSplit; first auto using fv_dtysem.
    iIntros "!>" (ρ) "#Hg".
    iDestruct (interp_env_props with "Hg") as %[Hclp Hlen]; rewrite <- Hlen in *.
    iDestruct "Hs" as (φ) "[Hγ Hγφ]".
    iSplit => //. iExists (φ _); iSplit.
    by iApply (dm_to_type_intro with "Hγ").
    iModIntro; repeat iSplitL; iIntros (v Hclv) "#HL";
      rewrite later_intuitionistically.
    - iIntros "!>"; iApply (internal_eq_iff with "(Hγφ [#//] [#//])").
      by iApply "HLT".
    - iApply "HTU" => //.
      by iApply (internal_eq_iff with "(Hγφ [#//] [#//])").
  Qed.

  Lemma D_Typ_Concr Γ T s σ l:
    (s, σ) ↝[ length Γ ] ⟦ T ⟧ -∗
    Γ ⊨d{ l := dtysem σ s } : TTMem l T T.
  Proof. iIntros "#Hs"; iApply D_Typ; by [| iIntros "!> **"]. Qed.
End typing_type_member_defs.
