(** *)
From stdpp Require Import gmap.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import tactics.

From D Require Import tactics.
From D.DSub Require Import syn operational synLemmas unary_lr unary_lr_binding.

Set Primitive Projections.
Set Implicit Arguments.

Definition stys := gmap stamp ty.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx) (g: stys) (n: nat).

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

Section interp_equiv.
  Context `{!dsubG Σ}.

  Notation envD := (listVlC -n> vlC -n> iProp Σ).
  Implicit Types (φ: envD).

  Definition interp_extractedTy: extractionResult -> envD :=
    λ gsσ, λne ρ v,
    let '(g, (s, σ)) := gsσ in
    (∃ T' : ty, ⌜g !! s = Some T'⌝ ∧ ⟦ T' ⟧ (subst_sigma σ ρ) v)%I.
  Notation "⟦ s , σ ⟧ [ g ]" := (interp_extractedTy (g, (s, σ))).

  Definition envD_equiv n φ1 φ2: iProp Σ :=
    (∀ ρ v, ⌜ length ρ = n ⌝ → ⌜ cl_ρ ρ ⌝ → φ1 ρ v ↔ φ2 ρ v)%I.
  Notation "φ1 ≈[  n  ] φ2" := (envD_equiv n φ1 φ2) (at level 70).

  (* XXX I wanted to use ≡ not ↔ but I'm not sure how to prove this lemma: *)
  (* Definition envD_equiv n φ1 φ2: iProp Σ := (∀ ρ v, ⌜ length ρ = n ⌝ → φ1 ρ v ≡ φ2 ρ v)%I. *)
  Goal ∀ T (P : ty → iProp Σ), (P T ≡ ∃ T', ⌜Some T = Some T'⌝ ∧ P T')%I : iProp Σ.
  Abort.

  (* Belongs in synLemmas. *)
  Lemma interp_subst_commute T σ ρ v:
    nclosed T (length σ) →
    nclosed_σ σ (length ρ) →
    cl_ρ ρ →
    ⟦ T.|[to_subst σ] ⟧ ρ v ≡ ⟦ T ⟧ σ.|[to_subst ρ] v.
  Proof.
    intros HclT Hclσ Hclρ.
    rewrite -(interp_subst_all ρ _ v) // -(interp_subst_all _ T v) //.
    - by erewrite subst_compose_x.
    - by apply nclosed_σ_to_subst.
  Qed.

  Lemma extraction_envD_equiv g s σ T n:
    T ~[ n ] (g, (s, σ)) →
    ⟦ T ⟧ ≈[ n ] ⟦ s , σ ⟧ [ g ].
  Proof.
    rewrite /interp_extractedTy /envD_equiv /=.
    iIntros ((T' & -> & <- & HclT & HclT') ρ v <- Hclρ).
    iSplit; iIntros "H"; [| iDestruct "H" as (T'' Heq) "?" ];
      rewrite interp_subst_commute /subst_sigma //; naive_solver.
  Qed.

  (** envD_equiv commutes with substitution. *)
  Lemma envD_equiv_subst g T m n ξ s1 σ1 s2 σ2:
    T ~[ m ] (g, (s1, σ1)) →
    T.|[to_subst ξ] ~[ n ] (g, (s2, σ2)) →
    length ξ = m →
    nclosed_σ ξ n →
    ⟦ s1, σ1.|[to_subst ξ] ⟧ [ g ] ≈[ n ] ⟦ s2, σ2 ⟧ [ g ].
  Proof.
    rewrite /interp_extractedTy; iIntros ((T1 & -> & Heq1 & Hclσ1 & HclT1) (T2 & -> & Heq2 & Hclσ2 & HclT2) Hlenξ Hclξ ρ v Hlenρ Hclρ) "/="; subst.
    assert (Hclσ1ξ: nclosed_σ σ1.|[to_subst ξ] (length ρ)). by apply nclosed_σ_to_subst.
    assert (Hrew: T2.|[to_subst σ2.|[to_subst ρ]] =
                  T1.|[to_subst σ1.|[to_subst ξ].|[to_subst ρ]]). by repeat erewrite subst_compose_x; rewrite ?map_length ?Heq1 ?Heq2.
    iSplit; iIntros "#H"; iDestruct "H" as (T' Heq) "?"; injection Heq; intros <-; iExists _;
      iSplit => //; rewrite -(interp_subst_all _ T1) -?(interp_subst_all _ T2) ?Hrew //; by apply nclosed_σ_to_subst.
  Qed.

End interp_equiv.
