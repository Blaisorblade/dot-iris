From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.iprop (* For gname *)
     lib.saved_prop.
From iris.algebra Require Import agree excl gmap auth.

Import uPred.

Class SwapProp (PROP: sbi) := {
  impl_later : ∀ (P Q: PROP), (▷ P → ▷ Q) ⊢ ▷ (P → Q)
}.

Lemma impl_laterN n `{SwapProp PROP} (P Q: PROP) : (▷^n P → ▷^n Q) ⊢ ▷^n (P → Q).
Proof. elim: n => [//|n IHn]. by rewrite impl_later IHn. Qed.

Section derived_swap_lemmas.
  Context `{Σ: gFunctors}.
  Lemma mlater_pers (P: iProp Σ) : □ ▷ P ⊣⊢ ▷ □ P.
  Proof. iSplit; by iIntros "#? !>!>". Qed.
  Lemma mlaterN_pers (P: iProp Σ) i : □ ▷^i P ⊣⊢ ▷^i □ P.
  Proof. iSplit; by iIntros "#? !>!>". Qed.

  Context `{!SwapProp (iPropSI Σ)}.
  Lemma mlater_impl (P Q: iProp Σ) : (▷ P → ▷ Q) ⊣⊢ ▷ (P → Q).
  Proof. iSplit. iApply impl_later. iApply later_impl. Qed.
  Lemma mlaterN_impl (P Q: iProp Σ) i : (▷^i P → ▷^i Q) ⊣⊢ ▷^i (P → Q).
  Proof. iSplit. iApply impl_laterN. iApply laterN_impl. Qed.
End derived_swap_lemmas.

Class CmraSwappable (M : cmraT) := {
  (* TODO cmra_extend should really be cmra_extend_sep. *)
  (* cmra_extend_included: ∀ n (x x': A), ✓{S n} x → x ≼ x' → ✓{n} x' → ∃ x'', ✓{S n} x'' ∧ x ≼ x'' ∧ x' ≡{n}≡ x''; *)
  cmra_extend_included: ∀ n (mx : option M) z,
    ✓{S n} mx → ✓{n} (z ⋅? mx) → { z' | ✓{S n} (z' ⋅? mx) ∧ z ≡{n}≡ z' }
}.

Section SwapCmra.
(* Hints from Iris cmra.v, so that we can copy proofs unchanged. *)
Local Hint Extern 10 (_ ≤ _) => lia : core.
Arguments uPred_holds {_} !_ _ _ /.

Global Instance SwapCmra {M : ucmraT} `{!CmraSwappable M}: SwapProp (uPredSI M).
Proof.
  split.
  unseal; split => /= -[//|n] x ? HPQ n' ? [x' ->] ?? HP.
  specialize (HPQ (S n')); cbn in HPQ.
  case: (cmra_extend_included n' (Some x) x') => [||x'' []];
    rewrite /= ?[_ ⋅ x]comm ?Some_validN //=.
  - by eapply cmra_validN_le; eauto.
  - move => Hv Hnx'x''.
    rewrite Hnx'x''. apply HPQ; eauto using cmra_included_l.
    by rewrite -Hnx'x''.
Qed.
End SwapCmra.

(** * [CmraSwappable] Instances. *)

(** ** Discrete CMRAs. *)
Instance Swappable_discrete {A}: CmraDiscrete A → CmraSwappable A.
Proof. by split => n mx z _ Hv //; exists z; move: Hv; rewrite -!cmra_discrete_valid_iff. Qed.

(** ** Option. *)
Lemma validN_mjoin_option `{A: cmraT} n (mma: option (option A)): ✓{n} mjoin mma ↔ ✓{n} mma.
Proof. by destruct mma. Qed.
Lemma valid_mjoin_option `{A: cmraT} (mma: option (option A)): ✓ mjoin mma ↔ ✓ mma.
Proof. by destruct mma. Qed.
Lemma validN_opM_mjoin_option `{A: cmraT} n (a: A) mma:
  ✓{n} (a ⋅? mjoin mma) ↔ ✓{n} (Some a ⋅? mma).
Proof. by destruct mma; rewrite //= Some_op_opM. Qed.
Lemma valid_opM_mjoin_option `{A: cmraT} (a: A) mma:
  ✓ (a ⋅? mjoin mma) ↔ ✓ (Some a ⋅? mma).
Proof. by destruct mma; rewrite //= Some_op_opM. Qed.

Instance Swappable_optionUR `{!CmraSwappable A}: CmraSwappable (optionUR A).
Proof.
  split => n mmx [z|] /= Hx Hxz.
  - case: (cmra_extend_included n (mjoin mmx) z) => [||x [Hv Heq]]; last (exists (Some x); move: Hv);
    by rewrite ?validN_mjoin_option ?validN_opM_mjoin_option ?Heq //.
  - exists None; split_and!; destruct mmx; by rewrite /= ?left_id.
Qed.

(** ** Dependently-typed functions over a finite discrete domain *)
Instance Swappable_ofe_funUR {A} (B: A → ucmraT) (H: ∀ i, CmraSwappable (B i)): CmraSwappable (ofe_funUR B).
Proof.
  split => n mx z Hvmx Hvzmx.
  unshelve eassert (FUN := λ a, cmra_extend_included n (($ a) <$> mx) (z a) _ _).
  1-2: move: Hvzmx; destruct mx; rewrite /= -?ofe_fun_lookup_op ?Some_validN; eauto.
  exists (λ x, proj1_sig (FUN x)); split_and! => a;
  destruct mx; rewrite /= ?ofe_fun_lookup_op //; destruct (FUN a) as (?&HP1&HP2); eauto.

  (* Alternative proof. *)
  (* Restart.

  split => n [x|] /= z Hvmx Hvzmx.
  - assert (FUN := λ a, cmra_extend_included n (Some (x a)) (z a) (Hvmx a) (Hvzmx a)).
    exists (λ x, proj1_sig (FUN x)); split_and! => a;
    rewrite /= ?ofe_fun_lookup_op //; by destruct (FUN a) as (?&?&?).
  - assert (FUN := λ a, cmra_extend_included n None (z a) I (Hvzmx a)).
    exists (λ x, proj1_sig (FUN x)); split_and! => a;
    by destruct (FUN a) as (?&?&?). *)
Qed.

Section agree.
(** * Agreement CMRA. *)
Context {A : ofeT}.
Implicit Types a b : A.

Implicit Types x y : agree A.

Lemma elem_of_agree_sig x : { a | a ∈ agree_car x }.
Proof. destruct x as [[|a ?] ?]; last (exists a); set_solver+. Qed.

Lemma to_agree_uninjN_sig n x : ✓{n} x → { a | to_agree a ≡{n}≡ x }.
Proof.
  destruct (elem_of_agree_sig x) as [a H] => Hv.
  exists a.
  rewrite agree_validN_def in Hv*.
  split=> b /=; setoid_rewrite elem_of_list_singleton; naive_solver.
Qed.

Global Instance Swappable_agreeR: CmraSwappable (agreeR A).
Proof.
  split; move => n [x x' Hvx|x' _]; cbn => Hvx'.
  - exists x; rewrite cmra_core_l; split_and!;
    by [> | apply agree_op_invN].
  - case: (to_agree_uninjN_sig n x') => // a H.
    by exists (to_agree a).
Qed.
End agree.

(** * Exclusive CMRA. *)
Instance Swappable_exclR {A} : CmraSwappable (exclR A).
Proof. by split => n [x|] [z|] //; exists (Excl z). Qed.

Lemma gmap_cmra_extend_included n `{Countable A} `{!CmraSwappable T} (x: gmapUR A T) z:
  ✓{S n} x → ✓{n} (z ⋅ x) → { z' | ✓{S n} (z' ⋅ x) ∧ z ≡{n}≡ z' }.
Proof.
  move => Hvx Hvzx.
  unshelve eassert (FUN := (λ (i : A), cmra_extend_included n (Some (x !! i)) (z !! i) _ _)).
  by apply Hvx.
  by rewrite /= -lookup_op.
  exists (map_imap (λ i _, proj1_sig (FUN i)) z).
  split=>i; rewrite ?lookup_op lookup_imap /=;
  by case: (z !! i) (FUN i) => [?|] [?[?]]; rewrite /= ?left_id.
Qed.

Instance Swappable_gmapUR `{Countable A} `{!CmraSwappable T}: CmraSwappable (gmapUR A T).
Proof.
  split => n [x|] z; rewrite /= ?Some_validN.
  - by apply gmap_cmra_extend_included.
  - move => _ Hvz.
    case (gmap_cmra_extend_included n ∅ z) => [||z' Hv] //; last (exists z'; move: Hv); by rewrite right_id.
Qed.

Instance Swappable_iResUR (Σ: gFunctors): (∀ i, CmraSwappable (Σ i (iPreProp Σ))) → CmraSwappable (iResUR Σ) := _.
Instance Swappable_iResUR_manual (Σ: gFunctors): (∀ i, CmraSwappable (Σ i (iPreProp Σ))) → CmraSwappable (iResUR Σ).
Proof. move=>*. apply Swappable_ofe_funUR=>*. exact: Swappable_gmapUR. Qed.

Instance Swappable_iResUREmpty: CmraSwappable (iResUR #[]).
Proof.
  apply Swappable_iResUR. by apply fin_0_inv.
Qed.

From D Require Import tactics proofmode_extra saved_interp gen_iheap.
From iris.base_logic Require Import gen_heap.

Instance CmraSwappable_savedInterp Σ A B: CmraSwappable (savedInterpΣ A B Fin.F1 (iPreProp Σ)) := Swappable_agreeR.
Instance CmraSwappable_gen_iheap Σ `{Countable A} B: CmraSwappable (gen_iheapΣ A B Fin.F1 (iPreProp Σ)) := Swappable_discrete _.
Instance CmraSwappable_gen_heap Σ `{Countable A} B: CmraSwappable (gen_heapΣ A B Fin.F1 (iPreProp Σ)) := Swappable_discrete _.

Require Import Program.
From D.DSub Require Import operational.

Instance CmraSwappable_dsub: CmraSwappable (iResUR dsubΣ).
Proof.
  apply Swappable_iResUR.
  rewrite /gid; repeat (dependent destruction i; cbn; try apply _).
Qed.

From D.Dot Require Import operational.

Instance CmraSwappable_dot: CmraSwappable (iResUR dotΣ).
Proof.
  apply Swappable_iResUR.
  rewrite /gid; repeat (dependent destruction i; cbn; try apply _).
Qed.
