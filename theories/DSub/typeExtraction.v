(** *)
From stdpp Require Import gmap fin_map_dom.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import tactics.

From D Require Import tactics.
From D.DSub Require Import syn operational synLemmas unary_lr unary_lr_binding.

Set Primitive Projections.
Set Implicit Arguments.

Definition stys := gmap stamp ty.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx) (g: stys) (n: nat) (s: stamp).

Definition gdom {X} (g: gmap stamp X) := dom (gset stamp) g.
Arguments gdom /.

Definition fresh_stamp {X} (g: gmap stamp X): stamp := fresh (dom (gset stamp) g).

Lemma fresh_stamp_spec {X} (g: gmap stamp X) : fresh_stamp g ∉ gdom g.
Proof. apply is_fresh. Qed.
Hint Resolve fresh_stamp_spec.

Lemma ex_fresh_stamp {X} (g: gmap stamp X): { s | s ∉ gdom g }.
Proof. exists (fresh_stamp g). by apply fresh_stamp_spec. Qed.

Lemma insert_grow g s T: s ∉ gdom g → g ⊆ <[s:=T]> g.
Proof. intro Hfresh. eapply insert_subseteq, not_elem_of_dom, Hfresh. Qed.
Hint Resolve insert_grow.

Lemma ex_fresh_stamp_strong g T: { s | s ∉ gdom g ∧ g ⊆ <[s := T]> g }.
Proof.
  pose proof (ex_fresh_stamp g) as [s Hfresh].
  exists s; split; auto.
Qed.

Lemma ex_fresh_stamp_strong' g T: { s | s ∉ gdom g ∧ gdom g ⊆ gdom (<[s := T]> g) }.
Proof.
  pose proof (ex_fresh_stamp_strong g T) as [s []].
  exists s; split =>//=. by apply subseteq_dom.
Qed.

(** Next, we define "extraction", which is the core of stamping.
    Extraction (as defined by [extraction]) is a relation, stable under
    substitution, between a type and its extracted form.

    An extracted type is basically a stamp pointing into a table, where types
    are allocated. However, we cannot substitute into such opaque pointers
    directly, so how can we ensure stability under substitution?
    To this end, extracted types also contain an environment on which
    substitution can act.
    The function [extract] extracts types by allocating them into a table and
    creating an initial environment.
 *)
Definition extractedTy: Type := stamp * vls.
Definition extractionResult: Type := stys * extractedTy.

Implicit Types (sσ: extractedTy) (gsσ: extractionResult).

Definition extract g n T: stys * extractedTy :=
  let s := fresh_stamp g
  in (<[s := T]> g, (s, idsσ n)).

Definition extraction n T: (stys * extractedTy → Prop) :=
  λ '(g, (s, σ)),
  ∃ T', g !! s = Some T' ∧ T'.|[to_subst σ] = T ∧ nclosed_σ σ n ∧ nclosed T' (length σ).
Notation "T ~[ n  ] gsσ" := (extraction n T gsσ) (at level 70).

Lemma extract_spec g n T: nclosed T n → T ~[ n ] (extract g n T).
Proof. move => Hcl; exists T; by rewrite lookup_insert closed_subst_idsρ ?length_idsσ. Qed.
Hint Resolve extract_spec.

Lemma nclosed_σ_to_subst ξ σ n:
  nclosed_σ ξ (length σ) → nclosed_σ σ n →
  nclosed_σ (ξ.|[to_subst σ]) n.
Proof.
  intros.
  apply closed_vls_to_Forall, fv_to_subst => //. by apply Forall_to_closed_vls.
Qed.
Hint Resolve nclosed_σ_to_subst.

Lemma extraction_closed g n T s σ:
  T ~[ n ] (g, (s, σ)) →
  nclosed T n.
Proof. intros (T' & Hlook & <- & Hclσ & HclT'). by apply fv_to_subst. Qed.

Lemma extraction_subst g n T s σ m σ':
  T ~[ n ] (g, (s, σ)) →
  length σ' = n →
  nclosed_σ σ' m →
  T.|[to_subst σ'] ~[ m ] (g, (s, σ.|[to_subst σ'])).
Proof.
  intros (T' & Hlook & <- & Hclσ & HclT') <- => /=. rewrite map_length.
  exists T'; repeat split => //.
  - asimpl. apply HclT', to_subst_compose.
  - by apply nclosed_σ_to_subst.
Qed.
Hint Resolve extraction_subst.

Lemma extract_subst_spec g g' n T s σ m σ':
  nclosed T n →
  length σ' = n →
  nclosed_σ σ' m →
  (g', (s, σ)) = extract g n T →
  T.|[to_subst σ'] ~[ m ] (g', (s, σ.|[to_subst σ'])).
Proof.
  intros * HclT Hlen Hclσ Heq.
  eapply extraction_subst => //. rewrite Heq. by eapply extract_spec.
Qed.
Hint Resolve extract_subst_spec.

Lemma extraction_mono T g g' s σ n:
  g ⊆ g' →
  T ~[ n ] (g, (s, σ)) →
  T ~[ n ] (g', (s, σ)).
Proof.
  cbn. intros Hg (T' & Hlook & Heq & ?).
  exists T'; repeat split => //. by eapply map_subseteq_spec.
Qed.
Hint Extern 5 (_ ~[ _ ] (_, _)) => try_once extraction_mono.

Lemma extract_spec_growg g n T g' sσ:
  (g', sσ) = extract g n T → g ⊆ g'.
Proof.
  intros H; cinject H. apply insert_grow, fresh_stamp_spec.
Qed.
Hint Resolve extract_spec_growg.

Lemma lookup_mono g g' s T:
  g !! s = Some T →
  g ⊆ g' →
  g' !! s = Some T.
Proof.
  intros Hlook Hless. pose proof (Hless s) as H.
  rewrite Hlook /= in H; by (case_match; subst).
Qed.
Hint Extern 5 (_ !! _ = Some _) => try_once lookup_mono.

Hint Resolve @fv_to_subst fv_to_subst_vl.

Lemma extract_lookup g g' s σ n T:
  (g', (s, σ)) = extract g n T → g' !! s = Some T.
Proof. intros H; cinject H; by rewrite lookup_insert. Qed.
Hint Resolve extract_lookup.

Lemma extraction_lookup g s σ n T:
  T ~[ n ] (g, (s, σ)) → ∃ T', g !! s = Some T' ∧ T'.|[to_subst σ] = T.
Proof. naive_solver. Qed.

Lemma subst_compose_extract g g' T n m ξ σ s:
  nclosed T n →
  nclosed_σ ξ m →
  length ξ = n →
  (g', (s, σ)) = extract g n T →
  T.|[to_subst σ.|[to_subst ξ]] = T.|[to_subst σ].|[to_subst ξ].
Proof.
  intros HclT Hclξ Hlen Hext; cinject Hext. by eapply subst_compose_idsσ_x.
Qed.

Lemma extract_subst_commute g g' g'' T ξ n m s1 σ1 s2 σ2:
  nclosed T n →
  nclosed_σ ξ m →
  length ξ = n →
  (g', (s1, σ1)) = extract g n T →
  (g'', (s2, σ2)) = extract g' m (T.|[to_subst ξ]) →
  T.|[to_subst ξ] ~[ m ] (g'', (s1, σ1.|[to_subst ξ])) ∧
  ∃ T1 T2,
    g'' !! s1 = Some T1 ∧
    g'' !! s2 = Some T2 ∧
    (* T1.|[to_subst σ1].|[to_subst ξ] = T2.|[to_subst σ2]. *)
    T1.|[to_subst σ1.|[to_subst ξ]] = T2.|[to_subst σ2].
Proof.
  intros HclT Hclξ Hlen Hext1 Hext2. split; eauto.
  exists T, T.|[to_subst ξ]; split_and!; eauto.
  (* - apply (@lookup_mono g' g''); info_eauto. *)
  (*   cinject Hext1; by rewrite lookup_insert. *)
  (* - cinject Hext2; by rewrite lookup_insert. *)
  - erewrite subst_compose_extract => //.
    cinject Hext1; cinject Hext2.
    rewrite !closed_subst_idsρ => //.
    apply fv_to_subst; eauto. (* eauto with typeclass_instances. *)
Qed.

From iris.algebra Require Import auth gmap agree.
From iris.base_logic.lib Require Export own.

Section interp_equiv.
  Context `{!dsubG Σ}.

  Notation envD := (listVlC -n> vlC -n> iProp Σ).
  Implicit Types (φ: envD).

  (** This interpretation is too naive: it substitutes σ into T' *before* applying our semantics,
      but we will not be able to do this when we use saved propositions to pre-interpret T'. *)
  Definition interp_extractedTy_naive: extractionResult -> envD :=
    λ gsσ, λne ρ v,
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
  Definition interp_extractedTy: (ty * vls) → envD :=
    λ '(T, σ), λne ρ v,
    (⟦ T ⟧ (subst_sigma σ ρ) v)%I.
  Notation "⟦ T ⟧ [ σ ]" := (interp_extractedTy (T, σ)).

  Definition envD_equiv n φ1 φ2: iProp Σ :=
    (∀ ρ v, ⌜ length ρ = n ⌝ → ⌜ cl_ρ ρ ⌝ → φ1 ρ v ≡ φ2 ρ v)%I.
  Notation "φ1 ≈[  n  ] φ2" := (envD_equiv n φ1 φ2) (at level 70).

  (* Belongs in synLemmas. *)
  Lemma interp_subst_commute T σ ρ v:
    nclosed T (length σ) →
    nclosed_σ σ (length ρ) →
    cl_ρ ρ →
    ⟦ T.|[to_subst σ] ⟧ ρ v ≡ ⟦ T ⟧ σ.|[to_subst ρ] v.
  Proof.
    intros HclT Hclσ Hclρ.
    rewrite -(interp_subst_all ρ _ v) // -(interp_subst_all _ T v).
    - by erewrite subst_compose_x.
    - by apply nclosed_σ_to_subst.
  Qed.

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
    iExists _, _; repeat iSplit => //; iIntros (ρ v Hlenρ Hclρ) "/="; subst.
    assert (Hclσ1ξ: nclosed_σ σ1.|[to_subst ξ] (length ρ)). by apply nclosed_σ_to_subst.
    assert (Hrew: T2.|[to_subst σ2.|[to_subst ρ]] =
                  T1.|[to_subst σ1.|[to_subst ξ].|[to_subst ρ]]). by repeat erewrite subst_compose_x;
                                                                    rewrite ?map_length ?Heq1 ?Heq2.
    rewrite -(interp_subst_all _ T1) -?(interp_subst_all _ T2) ?Hrew //; by apply nclosed_σ_to_subst.
  Qed.

  Notation "¬ P" := (□ (P → False))%I : bi_scope.

  Section definitions.
    Context `{hG : gen_iheapG L V Σ}.

    Definition gen_iheap_ctx (σ : gmap L V) : iProp Σ :=
      own (gen_iheap_name hG) (● (to_gen_iheap σ)).

    Definition mapsto_def (l : L) (v: V) : iProp Σ :=
      own (gen_iheap_name hG) (◯ {[ l := to_agree (v : leibnizC V) ]}).
    Definition mapsto_aux : seal (@mapsto_def). by eexists. Qed.
    Definition mapsto := mapsto_aux.(unseal).
    Definition mapsto_eq : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).
    Global Instance mapsto_timeless : Timeless (mapsto l v).
    Proof. rewrite mapsto_eq /mapsto_def. apply _. Qed.
    Global Instance mapsto_persistent : Persistent (mapsto l v).
    Proof. rewrite mapsto_eq /mapsto_def. apply _. Qed.

    Implicit Types σ : gmap L V.
    Lemma lookup_to_gen_iheap_None σ l : σ !! l = None → to_gen_iheap σ !! l = None.
    Proof. by rewrite /to_gen_iheap lookup_fmap=> ->. Qed.

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

  Notation "s ↦ γ" := (mapsto (hG := dsubG_interpNames) s γ)  (at level 20) : bi_scope.
                           (* (◯ {[ s := to_agree (γ : leibnizC gname) ]})) *)
  (* Notation "s ⇨ γ" := (inv logN (s ↦ γ)%I) (at level 20) : bi_scope. *)
  Global Instance: Persistent (s ↦ γ).
  Proof. apply _. Qed.
  Global Instance: Timeless (s ↦ γ).
  Proof. apply _. Qed.

  Notation "s ↝ φ" := (∃ γ, s ↦ γ ∗ γ ⤇ φ)%I  (at level 20) : bi_scope.

  Definition allGs gs := (gen_iheap_ctx (hG := dsubG_interpNames) gs).
  Arguments allGs /.

  Lemma alloc_sp T: (|==> ∃ γ, γ ⤇ dsub_interp T)%I.
  Proof. by apply saved_interp_alloc. Qed.

  (*
    Prove "transfer" theorems:
    transferOne: s ↦ T → |==> s ↦ γ ∗ γ ⤇ ⟦ T ⟧
    transfer: (2) map (1) over a gmap, someHow.
   *)



  Lemma transferOne_base_inv gs s T:
      gs !! s = None → (allGs gs ==∗ ∃ gs', allGs gs' ∗ s ↝ (λ ρ, ⟦ T ⟧ ρ) ∗ ⌜ gdom gs' ≡ gdom gs ∪ {[s]} ⌝)%I.
  Proof.
    iIntros (HsFresh) "Hown /=".
    iMod (alloc_sp T) as (γ) "#Hγ".
    iMod (gen_iheap_alloc _ s γ with "Hown") as "[H1 H2]" => //.
    iModIntro. iExists (<[s:=γ]> gs). iFrame. iSplitL.
    - iExists γ. iFrame. done.
    - by rewrite dom_insert union_comm.
  Qed.

  (* Given a mapping from stamps to gnames, we can also define when a map is properly translated. *)
  (* Definition wellMapped g (stampHeap: gmap stamp gname) : iProp Σ := *)
  (*   (∀ s T ρ v, *)
  (*       ⌜ g !! s = Some T⌝ → *)
  (*       ∃ γ P, ⌜ stampHeap !! s = Some γ⌝ → γ ⤇ P ∧ ⟦ T ⟧ ρ v ≡ P ρ v)%I. *)

  (* To give a definitive version of wellMapped, we need stampHeap to be stored in a resource. Here it is: *)
  Definition wellMapped g : iProp Σ :=
    (□∀ s T ρ v,
        ⌜ g !! s = Some T⌝ → ∃ P, s ↝ P ∧ ⟦ T ⟧ ρ v ≡ P ρ v)%I.
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
    iIntros (s' T' ρ v Hlook) "!>".
    destruct (decide (s = s')) as [<-|Hne].
    - iExists (dsub_interp T).
      suff <-: T = T' by iSplit. by rewrite lookup_insert in Hlook; injection Hlook.
    - rewrite lookup_insert_ne //= in Hlook. by iApply "Hg".
  Qed.

  (* (* Not clearly needed. *) *)
  (* Lemma transferOne_empty gs s T: *)
  (*     gs !! s = None → (allGs gs ==∗ ∃ gs', wellMapped (<[s := T]> ∅) ∧ allGs gs' ∧ ⌜gs ⊆ gs'⌝)%I. *)
  (* Proof. *)
  (*   iIntros (HsFresh) "Hown /=". *)
  (*   iApply (transferOne gs ∅ s T) => //. *)
  (*   iIntros (s' T' ρ v Hlook); inverse Hlook. *)
  (* Qed. *)

  (** Next, I must prove that we can map transferOne over [gmap g], ensuring
      [wellMapped g]. To this end, I suspect we must convert [g] to a list using
      [map_to_list], prove that list contains no duplicate keys (maybe using
      [NoDup_map_to_list], or maybe actually extracting the set of keys)
      and use induction on that list.
      For the induction, we need a variant of wellMapped taking a list instead of  *)

  Definition wellMappedList (glist: list (stamp * ty)) : iProp Σ :=
    (∀ s T ρ v,
        ⌜ (s, T) ∈ glist ⌝ → ∃ P, s ↝ P ∧ ⟦ T ⟧ ρ v ≡ P ρ v)%I.

  (* I think we can delete this, right? -- leo *)
  (* Lemma transferList glist gs: (∀ s, s ∈ fmap fst glist → gs !! s = None) → (allGs gs ==∗ wellMappedList glist)%I. *)
  (* Abort. *)

  (* Lemma transfer g gs: ((∀ s, ⌜s ∈ gdom g⌝ -∗ ¬ ∃ γ, s ↦ γ) -∗ allGs gs ==∗ wellMapped g)%I. *)
  Lemma transfer' g gs: (∀ s, s ∈ gdom g → gs !! s = None) →
                       (allGs gs ==∗ ∃ gs', wellMapped g ∧ allGs gs' ∧ ⌜gdom gs' ≡ gdom gs ∪ gdom g⌝).
  Proof.
    elim g using map_ind.
    iIntros "/=" (H) "Hgs".
    - iModIntro. unfold wellMapped. iExists gs. iSplit.
      + iIntros (s T rho v HH). exfalso. done.
      + iFrame. iPureIntro. rewrite dom_empty. set_solver.
    - move=> {g}. iIntros (s T g Hs IH Hdom) "Hallgs".
      iPoseProof (IH with "Hallgs") as "IH".
      { move=> s' Hs'. apply Hdom. rewrite /gdom dom_insert. set_solver. }
      iMod "IH". iDestruct "IH" as (gs') "[Hwm [Hgs %]]".

      iPoseProof (transferOne gs' g s T) as "HH".
      + cut (s ∉ dom (gset stamp) gs').
        * move=> Hsgs. by eapply not_elem_of_dom.
        * unfold gdom in H. rewrite H. apply not_elem_of_union.
          split; eapply not_elem_of_dom =>//. apply Hdom. rewrite /gdom dom_insert. set_solver.
      + iMod ("HH" with "Hwm Hgs") as (gs'') "[H1 [H2 %]]". iModIntro. iExists gs''.
        iFrame. iPureIntro. rewrite /gdom.
        rewrite dom_insert union_comm -union_assoc [dom _ _ ∪ dom _ _]union_comm.
          by rewrite -H union_comm -H0. (* set_solver very slow *)
  Qed.

  Lemma transfer g gs: (∀ s, s ∈ gdom g → gs !! s = None) →
                       (allGs gs ==∗ wellMapped g)%I.
  Proof.
    iIntros (Hs) "H". iMod (transfer' gs Hs with "H") as (gs') "[H ?]". iModIntro. iFrame.
  Qed.
End interp_equiv.
