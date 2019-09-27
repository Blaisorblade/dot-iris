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
