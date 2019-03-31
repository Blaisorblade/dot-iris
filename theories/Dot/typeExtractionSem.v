From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.

From D Require Import tactics.
From D.Dot Require Import syn operational synLemmas unary_lr unary_lr_binding typeExtractionSyn.
Import uPred.

Set Primitive Projections.
Set Implicit Arguments.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx) (g: stys) (n: nat) (s: stamp).

Section interp_equiv.
  Context `{!dotG Σ}.

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
    (⟦ T ⟧ ρ v ↔ interp_extractedTy_naive (g, (s, σ)) ρ v)%I.
  Proof.
    cbn; intros (T' & -> & <- & HclT & HclT').
    iSplit; iIntros "H"; [| iDestruct "H" as (T'' Heq) "?" ]; naive_solver.
  Qed.

  (** However, a stamp semantics that carries over to saved predicates must use
      σ in ρ. And the result is only equivalent for closed ρ with the expected length. *)
  Definition interp_extractedTy: (ty * vls) → envD Σ :=
    λ '(T, σ) ρ v,
    (⟦ T ⟧ (subst_sigma σ ρ) v)%I.
  Notation "⟦ T ⟧ [ σ ]" := (interp_extractedTy (T, σ)).

  Definition envD_equiv n φ1 φ2: iProp Σ :=
    (∀ ρ v, ⌜ length ρ = n ⌝ → ⌜ cl_ρ ρ ⌝ → φ1 ρ v ≡ φ2 ρ v)%I.
  Notation "φ1 ≈[  n  ] φ2" := (envD_equiv n φ1 φ2) (at level 70).

  Lemma extraction_envD_equiv g s σ T n:
    T ~[ n ] (g, (s, σ)) →
    (∃ T', ⌜ g !! s = Some T'⌝ ∧
        ⟦ T ⟧ ≈[ n ] ⟦ T' ⟧ [ σ ])%I.
  Proof.
    iIntros ((T' & -> & <- & HclT & HclT')). iExists _; iSplit => //.
    iIntros (ρ v <- Hclρ). by rewrite interp_subst_commute /subst_sigma.
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
    have Hclσ1ξ: nclosed_σ σ1.|[to_subst ξ] (length ρ). by apply nclosed_σ_to_subst.
    have Hrew: T2.|[to_subst σ2.|[to_subst ρ]] =
                  T1.|[to_subst σ1.|[to_subst ξ].|[to_subst ρ]]. by erewrite !subst_compose_x;
                                                                    rewrite ?map_length ?Heq1 ?Heq2.
    rewrite -(interp_subst_all _ T1) -?(interp_subst_all _ T2) ?Hrew //; by apply nclosed_σ_to_subst.
  Qed.

  Lemma alloc_sp T: (|==> ∃ γ, γ ⤇ dot_interp T)%I.
  Proof. by apply saved_interp_alloc. Qed.

  Lemma transferOne_base_inv gs s T:
      gs !! s = None → (allGs gs ==∗ ∃ gs', allGs gs' ∗ s ↝ ⟦ T ⟧ ∗ ⌜ gdom gs' ≡ gdom gs ∪ {[s]} ⌝)%I.
  Proof.
    iIntros (HsFresh) "Hown /=".
    iMod (alloc_sp T) as (γ) "#Hγ".
    iMod (gen_iheap_alloc _ s γ with "Hown") as "[H1 H2]" => //.
    iModIntro. iExists (<[s:=γ]> gs). iFrame. iSplitL.
    - iExists γ. by iFrame.
    - by rewrite dom_insert union_comm.
  Qed.

  (* To give a definitive version of wellMapped, we need stampHeap to be stored in a resource. Here it is: *)
  Definition wellMapped g : iProp Σ :=
    (□∀ s T,
        ⌜ g !! s = Some T⌝ → ∃ φ, s ↝ φ ∧ ⌜ ⟦ T ⟧ = φ ⌝)%I.
  Instance: Persistent (wellMapped g).
  Proof. apply _. Qed.

  (** We can transfer one mapping from [g] into Iris resources. Note that [gs ⊆
      gs'] in the outpu might not be ultimately needed; that's enforced indirectly
      by both wellMapped and by invariants. *)
  Lemma transferOne gs g s T:
      gs !! s = None → (wellMapped g → allGs gs ==∗ ∃ gs', wellMapped (<[s := T]> g) ∧ allGs gs' ∧ ⌜gdom gs' ≡ gdom gs ∪ {[s]}⌝)%I.
  Proof.
    iIntros (HsFresh) "#Hg Hown /=".
    iMod (transferOne_base_inv gs s T HsFresh with "Hown") as (gs') "(Hgs & #Hmaps & #Hdom)".
    iExists gs'; iModIntro; iFrame "Hgs".
    iSplit =>//.
    iIntros (s' T' Hlook) "!>".
    destruct (decide (s = s')) as [<-|Hne].
    - iExists (⟦ T ⟧).
      suff <-: T = T' by iSplit. rewrite lookup_insert in Hlook; by injection Hlook.
    - rewrite lookup_insert_ne //= in Hlook. by iApply "Hg".
  Qed.

  Lemma transfer' g gs: (∀ s, s ∈ gdom g → gs !! s = None) →
                       (allGs gs ==∗ ∃ gs', wellMapped g ∧ allGs gs' ∧ ⌜gdom gs' ≡ gdom gs ∪ gdom g⌝).
  Proof.
    elim g using map_ind.
    - iIntros "/=" (H) "Hgs !>". iExists gs. repeat iSplit => //.
      + by iIntros (???).
      + iPureIntro. rewrite dom_empty. set_solver.
    - move=> {g} /=. iIntros (s T g Hs IH Hdom) "Hallgs".
      setoid_rewrite dom_insert in Hdom.
      iPoseProof (IH with "Hallgs") as "IH".
      { move=> s' Hs'. apply Hdom. set_solver. }
      iMod "IH" as (gs') "[Hwm [Hgs %]]". move: H => Hgs'.

      iPoseProof (transferOne gs' g s T) as "HH".
      + cut (s ∉ dom (gset stamp) gs').
        * move=> Hsgs. by eapply not_elem_of_dom.
        * rewrite Hgs'. apply not_elem_of_union.
          split; eapply not_elem_of_dom =>//. apply Hdom. set_solver.
      + iMod ("HH" with "Hwm Hgs") as (gs'') "[H1 [H2 %]]". move: H => /= Hgs''.
        iExists gs''. iFrame; iPureIntro.
        rewrite dom_insert Hgs'' Hgs'. (* set_solver very slow, so: *)
        (* clear; set_solver. (* 0.2 s *) *)
        by rewrite -union_assoc [dom _ _ ∪ {[_]}]union_comm.
  Qed.

  Lemma transfer g gs: (∀ s, s ∈ gdom g → gs !! s = None) →
                       (allGs gs ==∗ wellMapped g)%I.
  Proof.
    iIntros (Hs) "H". by iMod (transfer' gs Hs with "H") as (gs') "[H ?]".
  Qed.
End interp_equiv.

Section typing_type_member_defs.
  Context `{!dotG Σ} Γ.

  Definition leadsto_envD_equiv (sσ: extractedTy) n (φ : envD Σ) : iProp Σ :=
    let '(s, σ) := sσ in
    (⌜nclosed_σ σ n⌝ ∧ ∃ (φ' : envD Σ), s ↝ φ' ∗ envD_equiv n φ (λ ρ, φ' (subst_sigma σ ρ)))%I.
  Arguments leadsto_envD_equiv /.
  Notation "sσ ↝[  n  ] φ" := (leadsto_envD_equiv sσ n φ) (at level 20).

  Lemma wellMapped_maps s T g: g !! s = Some T →
      wellMapped g -∗ s ↝ dot_interp T.
  Proof.
    iIntros (Hl) "/= #Hm".
    by iDestruct ("Hm" $! _ _ Hl) as (φ) "[? <-]".
  Qed.

  Lemma extraction_to_leadsto_envD_equiv T g sσ n: T ~[ n ] (g, sσ) →
    wellMapped g -∗ sσ ↝[ n ] ⟦ T ⟧.
  Proof.
    move: sσ => [s σ] [T'] [Hl] [<-] [Hclσ] HclT /=; iIntros "#Hm".
    iDestruct ("Hm" $! _ _ Hl) as (φ) "[Hm1 <-]"; iClear "Hm".
    iSplit => //; iExists ⟦ T' ⟧; iSplit => //.
    iIntros (ρ v <- Hclρ) "!%".
    by apply interp_subst_commute.
  Qed.

  (** XXX In fact, this lemma should be provable for any φ,
      not just ⟦ T ⟧, but we haven't actually defined the
      necessary notation to state it:
  Lemma D_Typ_Sem L U s σ l φ:
    Γ ⊨ [φ, 1] <: [U, 1] -∗
    Γ ⊨ [L, 1] <: [φ, 1] -∗
    (s, σ) ↝[ length Γ ] φ -∗
    Γ ⊨d dtysem σ s : TTMem l L U.
    *)
  Lemma D_Typ T L U s σ l:
    Γ ⊨ [T, 1] <: [U, 1] -∗
    Γ ⊨ [L, 1] <: [T, 1] -∗
    (s, σ) ↝[ length Γ ] ⟦ T ⟧ -∗
    Γ ⊨d dtysem σ s : TTMem l L U.
  Proof.
    iIntros "#HTU #HLT #[% Hs] /=". move: H => Hclσ.
    have Hclσs: nclosed (dtysem σ s) (length Γ). by apply fv_dtysem.
    iSplit => //.
    iIntros "!>" (ρ) "#Hg".
    iPoseProof (interp_env_len_agree with "Hg") as "%". move: H => Hlen. rewrite <- Hlen in *.
    iPoseProof (interp_env_ρ_closed with "Hg") as "%". move: H => Hfvρ.
    have Hclσss: nclosed (dtysem σ.|[to_subst ρ] s) 0. by eapply fv_to_subst'.
    iDestruct "Hs" as (φ) "[Hγ Hγφ]".
    iSplit => //; iExists (φ (σ.|[to_subst ρ]));
      iSplit; first by repeat iExists _; iSplit.
    iModIntro; repeat iSplitL; iIntros (v Hclv) "#HL";
      iSpecialize ("Hγφ" $! ρ v with "[#//] [#//]").
    - iSpecialize ("HLT" $! ρ v Hclv with "Hg").
      iDestruct ("HLT" with "HL") as "#HLT1".
      by repeat iModIntro; iApply (internal_eq_iff with "Hγφ").
    - iApply "HTU" => //.
      by repeat iModIntro; iApply (internal_eq_iff with "Hγφ").
  Qed.

  Lemma D_Typ_Concr T s σ l:
    (s, σ) ↝[ (length Γ) ] ⟦ T ⟧ -∗
    Γ ⊨d dtysem σ s : TTMem l T T.
  Proof. iIntros "#Hs"; iApply D_Typ; by [| iIntros "!> **"]. Qed.
End typing_type_member_defs.
