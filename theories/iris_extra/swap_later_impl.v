(** * Show proof rule [Impl-▷].
Swap later [▷] with Iris implication [→] and wand [-∗]. *)
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.iprop.
From iris.algebra Require Import agree excl gmap auth.

From D Require Import cmra_prop_lift.

Set Suggest Proof Using.
Set Default Proof Using "Type".

(** ** Interface to Swap laws for any [bi]. *)
Class SwapProp (PROP: bi) := {
  impl_later : ∀ (P Q: PROP), (▷ P → ▷ Q) ⊢ ▷ (P → Q);
  wand_later: ∀ (P Q: PROP), (▷ P -∗ ▷ Q) ⊢ ▷ (P -∗ Q)
}.

Notation SwapPropI Σ := (SwapProp (iPropI Σ)).

Class SwapBUpd (PROP: bi) `(BUpd PROP) := {
  later_bupd_commute: ∀(P:PROP), (|==> ▷ P) ⊣⊢ ▷ |==> P
}.

Lemma impl_laterN n `{SwapProp PROP} (P Q: PROP) : (▷^n P → ▷^n Q) ⊢ ▷^n (P → Q).
Proof. elim: n => [//|n IHn]. by rewrite impl_later IHn. Qed.

Lemma wand_laterN n `{SwapProp PROP} (P Q: PROP) : (▷^n P -∗ ▷^n Q) ⊢ ▷^n (P -∗ Q).
Proof. elim: n => [//|n IHn]. by rewrite wand_later IHn. Qed.

Lemma laterN_bupd_commute n `{SwapBUpd PROP} (P: PROP) : (▷^n |==> P) ⊣⊢ |==> ▷^n P.
Proof. elim: n => [//|n IHn]. by rewrite later_bupd_commute /= IHn. Qed.

(** Derived swap laws, for uniform predicates. *)
Import uPred.

Section derived_swap_lemmas.
  Context `{M : ucmraT} `{!SwapProp (uPredI M)}.
  Set Default Proof Using "Type*".
  Lemma mlater_impl (P Q: uPred M) : (▷ P → ▷ Q) ⊣⊢ ▷ (P → Q).
  Proof. iSplit. iApply impl_later. iApply later_impl. Qed.
  Lemma mlaterN_impl (P Q: uPred M) i : (▷^i P → ▷^i Q) ⊣⊢ ▷^i (P → Q).
  Proof. iSplit. iApply impl_laterN. iApply laterN_impl. Qed.

  Lemma mlater_wand (P Q: uPred M) : (▷ P -∗ ▷ Q) ⊣⊢ ▷ (P -∗ Q).
  Proof. iSplit. iApply wand_later. iApply later_wand. Qed.
  Lemma mlaterN_wand (P Q: uPred M) i : (▷^i P -∗ ▷^i Q) ⊣⊢ ▷^i (P -∗ Q).
  Proof. iSplit. iApply wand_laterN. iApply laterN_wand. Qed.
End derived_swap_lemmas.

(** ** Implementation of swap laws for uniform predicates. *)

Class CmraSwappable (M : cmraT) := {
  cmra_extend_included: ∀ n (mx : option M) z,
    ✓{S n} mx → ✓{n} (z ⋅? mx) → { z' | ✓{S n} (z' ⋅? mx) ∧ z ≡{n}≡ z' }
}.

Section SwapCmra.
(* Hints from Iris cmra.v, so that we can copy proofs unchanged. *)
Local Hint Extern 10 (_ ≤ _) => lia : core.
Local Arguments uPred_holds {_} !_ _ _.
Context {M : ucmraT}.
Implicit Types P Q : uPred M.

Lemma CmraSwappable_impl_later `{!CmraSwappable M} P Q : (▷ P → ▷ Q) ⊢ ▷ (P → Q).
Proof.
  unseal; split => /= -[//|n] x ? HPQ n' ? [x' ->] ?? HP.
  specialize (HPQ (S n')); cbn in HPQ.
  case: (cmra_extend_included n' (Some x) x') => [||x'' []];
    rewrite /= ?(comm _ _ x) ?Some_validN //.
  - by eapply cmra_validN_le; eauto.
  - move => ? Hnx'x''.
    rewrite Hnx'x''. apply HPQ; eauto using cmra_included_l.
    by rewrite -Hnx'x''.
Qed.

Lemma CmraSwappable_impl_wand `{!CmraSwappable M} P Q : (▷ P -∗ ▷ Q) ⊢ ▷ (P -∗ Q).
Proof.
  unseal; split => /= -[//|n] x ? HPQ n' x' ?? HP.
  specialize (HPQ (S n')); cbn in HPQ.
  case: (cmra_extend_included n' (Some x) x') => [||x'' []];
    rewrite /= ?(comm _ _ x) ?Some_validN //.
  - by eapply cmra_validN_le; eauto.
  - move => ? Hnx'x''.
    rewrite Hnx'x''. apply HPQ; eauto.
    by rewrite -Hnx'x''.
Qed.

Lemma CmraSwappable_later_bupd `{!CmraSwappable M} P : (▷ |==> P) ⊢ |==> ▷ P.
Proof.
  unseal; split => /= -[|n] x ? HP k yf Hkl.
  - have ->: k = 0 by lia. by eauto.
  - case: (decide (k ≤ n)) Hkl => [Hle _ Hv|Hn Hkl].
    + case (HP k yf Hle Hv) => [x' [Hv' HP']]. exists x'; split_and! => //.
      case: k Hle {Hv Hv'} HP' => [//|]. eauto using uPred_mono.
    + have ->: k = S n by lia. move => {Hn Hkl} Hv.
      case (HP n yf) => [||x' [Hv' HP']]; eauto using cmra_validN_le.
      case: (cmra_extend_included n (Some yf) x') => [||x'' []];
      rewrite /= ?(comm _ _ x) ?Some_validN; eauto using cmra_validN_op_r.
      move => Hv'' Hnx'x''.
      exists x''; split; first done.
      by rewrite -Hnx'x''.
Qed.

Lemma CmraSwappable_bupd_later `{!CmraSwappable M} P : (|==> ▷ P) ⊢ ▷ |==> P.
Proof.
  unseal; split => /= -[//|n] x ? HP k yf Hkl Hv.
  case: (cmra_extend_included k (Some x) yf) => [||yf' []];
    rewrite /= ?(comm _ _ x) ?Some_validN //.
  - by eapply cmra_validN_le; eauto.
  - move => ? HyfEq.
    case (HP (S k) yf') => [||x' [Hv' HP']]; eauto.
    exists x'; rewrite HyfEq; split_and!;
    eauto using cmra_validN_le.
Qed.

Global Instance SwapCmra `{!CmraSwappable M}: SwapProp (uPredI M).
Proof.
  split. exact: CmraSwappable_impl_later. exact: CmraSwappable_impl_wand.
Qed.

Global Instance SwapBUpdCmra `{!CmraSwappable M}: SwapBUpd (uPredI M) _.
Proof.
  split=>P; iSplit;
    [iApply CmraSwappable_bupd_later | iApply CmraSwappable_later_bupd].
Qed.

End SwapCmra.

(** *** Lift [cmra_prop_lift] infrastructure to [CmraSwappable]. *)
Notation SwappableRFunct F := (LiftCPropToRFunctor CmraSwappable F).
Notation SwappableGFunct Σ := (LiftCPropToGFunctors CmraSwappable Σ).

Instance SwappableGFunct_nil : LiftCPropToGFunctors_nil_type CmraSwappable.
Proof. apply LiftCPropToGFunctors_nil. Qed.

Instance SwappableGFunct_app : LiftCPropToGFunctors_app_type CmraSwappable.
Proof. apply LiftCPropToGFunctors_app. Qed.

Instance SwappableGFunct_GFunctor `{!rFunctorContractive F} :
  LiftCPropToGFunctors_GFunctor_type F CmraSwappable.
Proof. apply LiftCPropToGFunctors_GFunctor. Qed.


(** ** [CmraSwappable] Instances. *)

(** *** Option. *)
Lemma validN_mjoin_option `{A: cmraT} n (mma: option (option A)):
  ✓{n} mjoin mma ↔ ✓{n} mma.
Proof. by destruct mma. Qed.
Lemma valid_mjoin_option `{A: cmraT} (mma: option (option A)):
  ✓ mjoin mma ↔ ✓ mma.
Proof. by destruct mma. Qed.
Lemma validN_opM_mjoin_option `{A: cmraT} n (a: A) mma:
  ✓{n} (a ⋅? mjoin mma) ↔ ✓{n} (Some a ⋅? mma).
Proof. by destruct mma; rewrite //= Some_op_opM. Qed.
Lemma valid_opM_mjoin_option `{A: cmraT} (a: A) mma:
  ✓ (a ⋅? mjoin mma) ↔ ✓ (Some a ⋅? mma).
Proof. by destruct mma; rewrite //= Some_op_opM. Qed.

Instance CmraSwappable_optionUR `{!CmraSwappable A}: CmraSwappable (optionUR A).
Proof.
  split => n mmx [z|] /= Hx Hxz.
  - case: (cmra_extend_included n (mjoin mmx) z) => [||x [Hv Heq]];
    last (exists (Some x); move: Hv);
    by rewrite ?validN_mjoin_option ?validN_opM_mjoin_option ?Heq //.
  - exists None; split_and!; destruct mmx; by rewrite /= ?left_id.
Qed.

(** *** [gmap] *)
Lemma gmap_cmra_extend_included n `{Countable A} `{!CmraSwappable T}
  (x: gmapUR A T) z:
  ✓{S n} x → ✓{n} (z ⋅ x) → { z' | ✓{S n} (z' ⋅ x) ∧ z ≡{n}≡ z' }.
Proof.
  move => Hvx Hvzx.
  unshelve eassert (FUN := (λ (i : A),
    cmra_extend_included n (Some (x !! i)) (z !! i) _ _)).
  by apply Hvx.
  by rewrite /= -lookup_op.
  exists (map_imap (λ i _, proj1_sig (FUN i)) z).
  split=>i; rewrite ?lookup_op map_lookup_imap /=;
  by case: (z !! i) (FUN i) => [?|] [?[?]]; rewrite /= ?left_id.
Qed.

Instance CmraSwappable_gmapUR `{Countable A} `{!CmraSwappable T}:
  CmraSwappable (gmapUR A T).
Proof.
  split => n [x|] z; rewrite /= ?Some_validN.
  - by apply gmap_cmra_extend_included.
  - move => _ Hvz.
    case (gmap_cmra_extend_included n ∅ z) => [||z' Hv] //;
      last (exists z'; move: Hv); by rewrite right_id.
Qed.

(** *** Dependently-typed functions over a finite discrete domain *)
Instance CmraSwappable_discrete_funUR {A} (B: A → ucmraT)
  (H: ∀ i, CmraSwappable (B i)):
  CmraSwappable (discrete_funUR B).
Proof.
  split => n mx z Hvmx Hvzmx.
  unshelve eassert (FUN := λ a,
    cmra_extend_included n ((.$ a) <$> mx) (z a) _ _).
  1-2: move: Hvzmx; destruct mx;
    rewrite /= -?discrete_fun_lookup_op ?Some_validN; by eauto.
  exists (λ x, proj1_sig (FUN x)); split_and! => a;
  destruct mx; rewrite /= ?discrete_fun_lookup_op //;
  destruct (FUN a) as (?&HP1&HP2); eauto.
Qed.

Instance CmraSwappable_iResUR `(fp : SwappableGFunct Σ) :
  CmraSwappable (iResUR Σ) | 100 := lift_cprop_iResUR.

Section agree.
(** *** Agreement CMRA. *)
Context {A : ofeT}.
Implicit Types (a b : A) (x y : agree A).

Lemma elem_of_agree_sig x : { a | a ∈ agree_car x }.
Proof. destruct x as [[|a ?] ?]; last (exists a); set_solver+. Qed.

Lemma to_agree_uninjN_sig n x : ✓{n} x → { a | to_agree a ≡{n}≡ x }.
Proof.
  destruct (elem_of_agree_sig x) as [a H] => Hv.
  exists a.
  rewrite agree_validN_def in Hv*.
  split=> b /=; setoid_rewrite elem_of_list_singleton; naive_solver.
Qed.

Global Instance CmraSwappable_agreeR: CmraSwappable (agreeR A).
Proof.
  split; move => n [x x' Hvx|x' _]; cbn => Hvx'.
  - exists x; rewrite cmra_core_l; split_and!;
    by [> | apply agree_op_invN].
  - case: (to_agree_uninjN_sig n x') => // a H.
    by exists (to_agree a).
Qed.
End agree.

(* Currently unused instances. *)
(** *** Discrete CMRAs. *)
Instance CmraSwappable_discrete {A}: CmraDiscrete A → CmraSwappable A.
Proof.
  split => n mx z _ Hv //; exists z; move: Hv.
  by rewrite -!cmra_discrete_valid_iff.
Qed.

(** *** Exclusive CMRA. *)
Instance CmraSwappable_exclR {A} : CmraSwappable (exclR A).
Proof. by split => n [x|] [z|] //; exists (Excl z). Qed.
