From stdpp Require Import gmap fin_map_dom.
From iris.proofmode Require Import tactics.
From D Require Import prelude asubst_intf dlang.

Set Implicit Arguments.

Module Type TypeTSig. Parameter ty : Type. End TypeTSig.

Module Type TypeExtraction
  (Import VS : VlSortsSig)
  (Import LWP : LiftWp VS)
  (Import TS : TypeTSig).

Definition stys := gmap stamp ty.

Implicit Types (s : stamp) (n: nat) (g : stys).
Implicit Types (T: ty) (v: vl).

Definition gdom {X} (g: gmap stamp X) := dom (gset stamp) g.
Arguments gdom /.

Section dlang_only.
  Context `{!dlangG Σ} `{!TyInterp ty Σ}.
  Implicit Types (φ: envD Σ).

  Definition wellMapped g : iProp Σ :=
    (□∀ s T,
        ⌜ g !! s = Some T⌝ → ∃ φ, s ↝ φ ∧ ⌜ ty_interp T = φ ⌝)%I.
  Instance: Persistent (wellMapped g) := _.

  (*( Unused *)
  Lemma wellMapped_maps s T g: g !! s = Some T →
      wellMapped g -∗ s ↝ ty_interp T.
  Proof.
    iIntros (Hl) "/= #Hm".
    by iDestruct ("Hm" $! _ _ Hl) as (φ) "[? <-]".
  Qed.

  Lemma transferOne_base_inv gs s T:
      gs !! s = None → (allGs gs ==∗ ∃ gs', allGs gs' ∗ s ↝ ty_interp T ∗ ⌜ gdom gs' ≡ gdom gs ∪ {[s]} ⌝)%I.
  Proof.
    iIntros (HsFresh) "Hown /=".
    iMod (saved_ho_sem_type_alloc 0 (vopen (ty_interp T))) as (γ) "#Hγ".
    iMod (gen_iheap_alloc _ s γ with "Hown") as "[H1 H2]" => //.
    iModIntro. iExists (<[s:=γ]> gs). iFrame. iSplitL.
    - iExists γ. by iFrame.
    - by rewrite dom_insert union_comm.
  Qed.

  (** We can transfer one mapping from [g] into Iris resources. *)
  Lemma transferOne gs g s T:
      gs !! s = None → (wellMapped g → allGs gs ==∗ ∃ gs', wellMapped (<[s := T]> g) ∧ allGs gs' ∧ ⌜gdom gs' ≡ gdom gs ∪ {[s]}⌝)%I.
  Proof.
    iIntros (HsFresh) "#Hg Hown /=".
    iMod (transferOne_base_inv gs s T HsFresh with "Hown") as (gs') "(Hgs & #Hmaps & #Hdom)".
    iExists gs'; iModIntro; iFrame "Hgs".
    iSplit =>//.
    iIntros (s' T' Hlook) "!>".
    destruct (decide (s = s')) as [<-|Hne].
    - iExists (ty_interp T).
      suff <-: T = T' by iSplit. rewrite lookup_insert in Hlook; by injection Hlook.
    - rewrite lookup_insert_ne //= in Hlook. by iApply "Hg".
  Qed.

  Lemma transfer' g gs: (∀ s, s ∈ gdom g → gs !! s = None) →
                       (allGs gs ==∗ ∃ gs', wellMapped g ∧ allGs gs' ∧ ⌜gdom gs' ≡ gdom gs ∪ gdom g⌝).
  Proof.
    elim g using map_ind.
    - iIntros "/=" (Hs) "Hgs !>". iExists gs. repeat iSplit => //.
      + by iIntros (???).
      + iPureIntro. rewrite dom_empty. set_solver-.
    - move=> {g} /= s T g Hs IH Hdom. iIntros "Hallgs".
      setoid_rewrite dom_insert in Hdom.
      iPoseProof (IH with "Hallgs") as "IH".
      { move=> s' Hs'. apply Hdom. set_solver- Hs. }
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
    iIntros (Hs) "H". by iMod (transfer' gs Hs with "H") as (gs') "[$ ?]".
  Qed.
End dlang_only.
End TypeExtraction.
