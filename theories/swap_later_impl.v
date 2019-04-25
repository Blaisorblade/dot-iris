From D Require Import tactics proofmode_extra.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.iprop (* For gname *)
     lib.saved_prop.

Import uPred.

Class SwapProp (PROP: sbi) := {
  impl_later : ∀ (P Q: PROP), (▷ P → ▷ Q) ⊢ ▷ (P → Q)
}.

Lemma impl_laterN n `{SwapProp PROP} (P Q: PROP) : (▷^n P → ▷^n Q) ⊢ ▷^n (P → Q).
Proof. elim: n => [//|n IHn]. by rewrite impl_later IHn. Qed.

Class CmraSwappable (M : cmraT) := {
  (* TODO cmra_extend should really be cmra_extend_sep. *)
  cmra_extend_included: ∀ n (mx : option M) z,
    ✓{S n} mx → ✓{n} (z ⋅? mx) → ∃ z', ✓{S n} (z' ⋅? mx) ∧ z ≡{n}≡ z'
}.

Instance SwapCmra {M : ucmraT} `{!CmraSwappable M}: SwapProp (uPredSI M).
Proof.
  split.
  unseal; split => /= -[//|n] x ? HPQ n' ? [x' ->] ?? HP.
  specialize (HPQ (S n')); cbn in HPQ.
  case: (cmra_extend_included n' (Some x) x'); last move => x'' [];
    rewrite /= ?[_ ⋅ x]comm ?Some_validN //=.
  - by eapply cmra_validN_le; eauto with lia.
  - move => Hv Hnx'x''.
    rewrite Hnx'x''. apply HPQ; eauto using cmra_included_l with lia.
    rewrite /uPred_holds /=. by rewrite -Hnx'x''.
Qed.

Instance Swappable_iResUREmpty: CmraSwappable (iResUR #[]).
Proof.
  split. rewrite /iResUR /gid /= => n mx z Hvmx Hvzmx.
  exists z; split_and! => // ??. by apply fin_0_inv.
Qed.
