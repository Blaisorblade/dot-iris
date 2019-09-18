From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From D.DSub Require Import unary_lr typeExtractionSyn.

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
      σ in ρ. *)
  Definition interp_extractedTy: ty → env → envD Σ :=
    λ T σ ρ, ⟦ T ⟧ (σ >> ρ).
  Notation "⟦ T ⟧ [ σ ]" := (interp_extractedTy T σ).
  Global Arguments interp_extractedTy /.

  Lemma extraction_envD_equiv g s σ T n:
    T ~[ n ] (g, (s, σ)) →
    ∃ T', g !! s = Some T' ∧ ⟦ T ⟧ ≡ ⟦ T' ⟧ [ to_subst σ ].
  Proof.
    intros (T' & -> & <- & _ & _). eexists _; split => //.
    intros ρ v. exact: interp_subst_compose.
  Qed.

  (** [envD_equiv] commutes with infinite substitution. *)
  Lemma envD_equiv_infsubst {g T m n ξ s1 σ1 s2 σ2}:
    T ~[ m ] (g, (s1, σ1)) →
    T.|[ξ] ~[ n ] (g, (s2, σ2)) →
    ∃ T1 T2, g !! s1 = Some T1 ∧ g !! s2 = Some T2 ∧
    ⟦ T1 ⟧ [ to_subst σ1 >> ξ ] ≡ ⟦ T2 ⟧ [ to_subst σ2 ].
  Proof.
    intros (T1 & -> & <- & _ & _) (T2 & -> & Heq2 & _ & _).
    exists T1, T2; split_and! => // ρ v /=.
    rewrite (interp_subst_ids T1 _ _) (interp_subst_ids T2 _ _). f_equiv.
    move: Heq2 => /(f_equal (λ T, T.|[ρ])). by asimpl.
  Qed.

  (** [envD_equiv] commutes with finite substitution, but under extra
      assumptions on the substitutions in questions (on free variables and
      length). *)
  Lemma envD_equiv_subst g T m n ξ s1 σ1 s2 σ2:
    T ~[ m ] (g, (s1, σ1)) →
    T.|[to_subst ξ] ~[ n ] (g, (s2, σ2)) →
    length ξ = m →
    ∃ T1 T2, g !! s1 = Some T1 ∧ g !! s2 = Some T2 ∧
    ⟦ T1 ⟧ [ to_subst σ1.|[to_subst ξ] ] ≡ ⟦ T2 ⟧ [ to_subst σ2 ].
  Proof.
    intros (T1 & -> & <- & Hclσ1 & HclT1) (T2 & -> & Heq2 & Hclσ2 & HclT2) Hlenξ.
    exists T1, T2; split_and! => // ρ v /=.
    rewrite (interp_subst_ids T1 _ _) (interp_subst_ids T2 _ _). f_equiv.
    have: T1.|[to_subst σ1.|[to_subst ξ]] = T2.|[to_subst σ2].
    - by rewrite Heq2 (subst_compose _ _ HclT1).
    - move => /(f_equal (λ T, T.|[ρ])). by asimpl.
    (* Reusing envD_equiv_infsubst takes more work than proving it from scratch! *)
    (* Restart.
    intros Hext1 Hext2 Hlen.
    destruct (envD_equiv_infsubst Hext1 Hext2) as (T1 & T2 & Hgs1 & Hgs2 & Heq).
    destruct Hext1 as (T1' & Hgs1' & Heq1 & Hclσ1 & HclT1).
    have ?: T1' = T1 by simplify_eq. subst. simplify_eq.
    exists T1, T2; split_and! => // ρ v /=.
    move: (Heq ρ v) => /= <- {Heq}.
    have: T1.|[to_subst σ1.|[to_subst ξ]] = T1.|[to_subst σ1 >> to_subst ξ].
    - rewrite (subst_compose _ _ HclT1) //. by asimpl.
    - move => /(f_equal (λ T, T.|[ρ])). asimpl.
      rewrite !(interp_subst_ids T1 _ _). by move->. *)
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
