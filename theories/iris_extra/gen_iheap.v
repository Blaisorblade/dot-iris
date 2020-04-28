(** An "immutable" version of Iris's gen_heap, created by removing fractions from it. *)
From iris.algebra Require Import auth gmap agree.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Definition gen_iheapUR (L V : Type) `{Countable L} : ucmraT :=
  gmapUR L (agreeR (leibnizO V)).
Definition to_gen_iheap {L V} `{Countable L} : gmap L V → gen_iheapUR L V :=
  fmap (λ v, to_agree (v : leibnizO V)).

(** The CMRA we need. *)
Class gen_iheapG (L V : Type) (Σ : gFunctors) `{Countable L} := GenIHeapG {
  gen_iheap_inG :> inG Σ (authR (gen_iheapUR L V));
  gen_iheap_name : gname
}.
Arguments gen_iheap_name {_ _ _ _ _} _ : assert.

Class gen_iheapPreG (L V : Type) (Σ : gFunctors) `{Countable L} :=
  { gen_iheap_preG_inG :> inG Σ (authR (gen_iheapUR L V)) }.

Definition gen_iheapΣ (L V : Type) `{Countable L} : gFunctors :=
  #[GFunctor (authR (gen_iheapUR L V))].

Instance subG_gen_iheapPreG {Σ L V} `{Countable L} :
  subG (gen_iheapΣ L V) Σ → gen_iheapPreG L V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{hG : gen_iheapG L V Σ}.

  Definition gen_iheap_ctx (σ : gmap L V) : iProp Σ :=
    own (gen_iheap_name hG) (● (to_gen_iheap σ)).

  Definition mapsto_def (l : L) (v: V) : iProp Σ :=
    own (gen_iheap_name hG) (◯ {[ l := to_agree (v : leibnizO V) ]}).
  Definition mapsto_aux : seal (@mapsto_def). Proof. by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
End definitions.

Local Notation "l ↦ v" := (mapsto l v) (at level 20) : bi_scope.

Section to_gen_iheap.
  Context (L V : Type) `{Countable L}.
  Implicit Types σ : gmap L V.

  (** Conversion to heaps and back *)
  Lemma to_gen_iheap_valid σ : ✓ to_gen_iheap σ.
  Proof. intros l. rewrite lookup_fmap. by case (σ !! l). Qed.
  Lemma lookup_to_gen_iheap_None σ l : σ !! l = None → to_gen_iheap σ !! l = None.
  Proof. by rewrite /to_gen_iheap lookup_fmap=> ->. Qed.
  Lemma gen_iheap_singleton_included σ l v :
    {[l := to_agree v]} ≼ to_gen_iheap σ → σ !! l = Some v.
  Proof.
    rewrite singleton_included_l=> -[[q' av] []].
    rewrite /to_gen_iheap lookup_fmap fmap_Some_equiv. move => -[v' [Hl ->]].
    by move => /Some_included [ /to_agree_inj | /to_agree_included ] /leibniz_equiv_iff ->.
  Qed.

  Lemma to_gen_iheap_insert l v σ :
    to_gen_iheap (<[l:=v]> σ) = <[l:=(to_agree (v:leibnizO V))]> (to_gen_iheap σ).
  Proof. by rewrite /to_gen_iheap fmap_insert. Qed.
End to_gen_iheap.

Lemma gen_iheap_init `{hG : gen_iheapPreG L V Σ} σ :
  ⊢ |==> ∃ _ : gen_iheapG L V Σ, gen_iheap_ctx σ.
Proof.
  iMod (own_alloc (● to_gen_iheap σ)) as (γ) "Hh".
  { apply auth_auth_valid. exact: to_gen_iheap_valid. }
  iModIntro. by iExists (GenIHeapG L V Σ _ _ _ γ).
Qed.

Section gen_iheap.
  Context `{hG : gen_iheapG L V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap L V.
  Implicit Types h g : gen_iheapUR L V.
  Implicit Types l : L.
  Implicit Types v : V.

  Global Instance mapsto_timeless l v : Timeless (l ↦ v).
  Proof. rewrite mapsto_eq /mapsto_def. apply _. Qed.
  Global Instance mapsto_persistent l v: Persistent (l ↦ v).
  Proof. rewrite mapsto_eq /mapsto_def. apply _. Qed.

  Lemma mapsto_agree l v1 v2 : l ↦ v1 -∗ l ↦ v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply wand_intro_r.
    rewrite mapsto_eq /mapsto_def -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> /auth_frag_valid /=. rewrite singleton_op singleton_valid.
    by intros ?%agree_op_invL'.
  Qed.

  Lemma gen_iheap_alloc σ l (v: V):
    σ !! l = None → gen_iheap_ctx σ ==∗ gen_iheap_ctx (<[l:=v]>σ) ∗ l ↦ v.
  Proof.
    iIntros (?) "Hσ". rewrite /gen_iheap_ctx mapsto_eq /mapsto_def.
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc,
      (alloc_singleton_local_update _ _ (to_agree (v:leibnizO _)))=> //.
        by apply lookup_to_gen_iheap_None. }
    iModIntro. rewrite to_gen_iheap_insert. iFrame.
  Qed.

  Lemma gen_iheap_valid σ l v : gen_iheap_ctx σ -∗ l ↦ v -∗ ⌜σ !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl". rewrite /gen_iheap_ctx mapsto_eq /mapsto_def.
    by iDestruct (own_valid_2 with "Hσ Hl") as %[Hl%gen_iheap_singleton_included _]%auth_both_valid.
  Qed.

  (* Deallocation/update should be impossible. *)
End gen_iheap.
