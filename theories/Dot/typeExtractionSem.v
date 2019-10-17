From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr typeExtractionSyn.

Set Implicit Arguments.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx) (n: nat) (s: stamp).
Notation sγmap := (gmap stamp gname).
Implicit Types (g : stys) (sγ : sγmap).

Section interp_equiv.
  Context `{!dlangG Σ}.

  Implicit Types (φ: envD Σ).

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

  (* Beware: here we must use [to_subst σ.|[ρ]], not [to_subst σ >> ρ],
     since the former is what we need to prove [D_Typ] below.
     Not sure that's still true if we change dm_to_type,
    but quite possibly yes.. *)
    (* use interp_extractedTy? *)
  Definition leadsto_envD_equiv s σ (φ : envD Σ) : iProp Σ :=
    (∃ (φ' : envD Σ),
      ⌜φ ≡ (λ ρ, φ' (to_subst σ.|[ρ]))⌝ ∗ s ↝ φ')%I.
  Arguments leadsto_envD_equiv /.
  Notation "s ↝[  σ  ] φ" := (leadsto_envD_equiv s σ φ) (at level 20).

  Lemma extraction_to_leadsto_envD_equiv T g s σ n: T ~[ n ] (g, (s, σ)) →
    wellMapped g -∗ s ↝[ σ ] ty_interp T.
  Proof.
    move => [T'] [Hl] [<- [_ /is_stamped_nclosed_ty HclT]].
    iIntros "Hm". iExists (ty_interp T'). iSplitR; [|by iApply "Hm"].
    iIntros "!%" (ρ v). exact: interp_subst_commute.
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
    Γ ⊨ [TLater T, 0] <: [TLater U, 0] -∗
    Γ ⊨ [TLater L, 0] <: [TLater T, 0] -∗
    s ↝[ σ ] ⟦ T ⟧ -∗
    Γ ⊨d{ l := dtysem σ s } : TTMem l L U.
  Proof.
    iIntros "#HTU #HLT #Hs /= !>" (ρ) "#Hg".
    iDestruct "Hs" as (φ Hγφ) "Hγ"; iSplit => //=.
    iExists (φ _); iSplit. by iApply (dm_to_type_intro with "Hγ").
    iModIntro; repeat iSplitL; iIntros (v) "#HL";
      rewrite later_intuitionistically.
    - iIntros "!>". iApply Hγφ. by iApply "HLT".
    - iApply "HTU" => //. by iApply Hγφ.
  Qed.

  Lemma D_Typ_Concr Γ T s σ l:
    s ↝[ σ ] ⟦ T ⟧ -∗
    Γ ⊨d{ l := dtysem σ s } : TTMem l T T.
  Proof. iIntros "#Hs"; iApply D_Typ => //; iApply Sub_Refl. Qed.
End typing_type_member_defs.
