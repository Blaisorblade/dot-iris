(** An "immutable" version of Iris's gen_heap, created by removing fractions from it. *)
From iris.algebra Require Import auth gmap agree.
From iris.base_logic.lib Require Export own.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Definition gen_iheapUR (L V : Type) `{Countable L} : ucmraT :=
  gmapUR L (agreeR (leibnizC V)).
Definition to_gen_iheap {L V} `{Countable L} : gmap L V → gen_iheapUR L V :=
  fmap (λ v, to_agree (v : leibnizC V)).

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
    own (gen_iheap_name hG) (◯ {[ l := to_agree (v : leibnizC V) ]}).
  Definition mapsto_aux : seal (@mapsto_def). by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).

  Local Notation "l ↦ v" := (mapsto l v) (at level 20) : bi_scope.

  Global Instance mapsto_timeless : Timeless (mapsto l v).
  Proof. rewrite mapsto_eq /mapsto_def. apply _. Qed.
  Global Instance mapsto_persistent : Persistent (mapsto l v).
  Proof. rewrite mapsto_eq /mapsto_def. apply _. Qed.

  Implicit Types σ : gmap L V.
  Lemma lookup_to_gen_iheap_None σ l : σ !! l = None → to_gen_iheap σ !! l = None.
  Proof. by rewrite /to_gen_iheap lookup_fmap=> ->. Qed.

  Lemma mapsto_agree l v1 v2 : l ↦ v1 -∗ l ↦ v2 -∗ ⌜v1 = v2⌝.
  Proof.
    apply wand_intro_r.
    rewrite mapsto_eq /mapsto_def -own_op -auth_frag_op own_valid discrete_valid.
    f_equiv=> /auth_own_valid /=. rewrite op_singleton singleton_valid.
    by intros ?%agree_op_invL'.
  Qed.

  Lemma to_gen_iheap_insert l (v: V) σ :
    to_gen_iheap (<[l:=v]> σ) = <[l:=(to_agree (v:leibnizC V))]> (to_gen_iheap σ).
  Proof. by rewrite /to_gen_iheap fmap_insert. Qed.

  Lemma gen_iheap_alloc σ l (v: V):
    σ !! l = None → gen_iheap_ctx σ ==∗ gen_iheap_ctx (<[l:=v]>σ) ∗ mapsto l v.
  Proof.
    iIntros (?) "Hσ". rewrite /gen_iheap_ctx mapsto_eq /mapsto_def.
    iMod (own_update with "Hσ") as "[Hσ Hl]".
    { eapply auth_update_alloc,
      (alloc_singleton_local_update _ _ (to_agree (v:leibnizC _)))=> //.
        by apply lookup_to_gen_iheap_None. }
    iModIntro. rewrite to_gen_iheap_insert. iFrame.
  Qed.
End definitions.