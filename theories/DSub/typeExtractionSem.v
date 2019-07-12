From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From D.DSub Require Import unary_lr typeExtractionSyn.

Set Implicit Arguments.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx) (g: stys) (n: nat) (s: stamp).

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
    nclosed_σ ξ n →
    ∃ T1 T2, g !! s1 = Some T1 ∧ g !! s2 = Some T2 ∧
    ⟦ T1 ⟧ [ to_subst σ1.|[to_subst ξ] ] ≡ ⟦ T2 ⟧ [ to_subst σ2 ].
  Proof.
    intros (T1 & -> & <- & Hclσ1 & HclT1) (T2 & -> & Heq2 & Hclσ2 & HclT2) Hlenξ Hclξ.
    exists T1, T2; split_and! => // ρ v /=.
    rewrite (interp_subst_ids T1 _ _) (interp_subst_ids T2 _ _). f_equiv.
    have: T1.|[to_subst σ1.|[to_subst ξ]] = T2.|[to_subst σ2].
    - by rewrite Heq2 (subst_compose HclT1 _ Hclσ1 _ Hclξ).
    - move => /(f_equal (λ T, T.|[ρ])). by asimpl.
    (* Reusing envD_equiv_infsubst takes more work than proving it from scratch! *)
    (* Restart.
    intros Hext1 Hext2 Hlen Hclξ.
    destruct (envD_equiv_infsubst Hext1 Hext2) as (T1 & T2 & Hgs1 & Hgs2 & Heq).
    destruct Hext1 as (T1' & Hgs1' & Heq1 & Hclσ1 & HclT1).
    have ?: T1' = T1 by simplify_eq. subst. simplify_eq.
    exists T1, T2; split_and! => // ρ v /=.
    move: (Heq ρ v) => /= <- {Heq}.
    have: T1.|[to_subst σ1.|[to_subst ξ]] = T1.|[to_subst σ1 >> to_subst ξ].
    - rewrite (subst_compose HclT1 _ Hclσ1 _ Hclξ) //. by asimpl.
    - move => /(f_equal (λ T, T.|[ρ])). asimpl.
      rewrite !(interp_subst_ids T1 _ _). by move->. *)
  Qed.

  Lemma alloc_sp T: (|==> ∃ γ, γ ⤇ ty_interp T)%I.
  Proof. exact: saved_ho_sem_type_alloc. Qed.

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
        (* code I quoted in https://gitlab.mpi-sws.org/iris/stdpp/issues/29 *)
        (* set_solver very slow, so: *)
        rewrite Hgs'' Hgs' dom_insert. by set_solver-.
        (* by rewrite -union_assoc [dom _ _ ∪ {[_]}]union_comm. *)
  Qed.

  Lemma transfer g gs: (∀ s, s ∈ gdom g → gs !! s = None) →
                       (allGs gs ==∗ wellMapped g)%I.
  Proof.
    iIntros (Hs) "H". by iMod (transfer' gs Hs with "H") as (gs') "[H ?]".
  Qed.
End interp_equiv.
