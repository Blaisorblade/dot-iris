From iris.program_logic Require Import ectx_language ectxi_language.
From iris.algebra Require Import ofe agree.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.iprop (* For gname *)
     lib.saved_prop.
From D.pure_program_logic Require Export weakestpre.

From D Require Import tactics.
From D.DSub Require Export syn.

From D Require Export gen_iheap saved_interp.

Class dsubG Σ := DsubG {
  dsubG_savior :> savedInterpG Σ vls vl;
  dsubG_interpNames : gen_iheapG stamp gname Σ;
}.

Instance dsubG_irisG `{dsubG Σ} : irisG dsub_lang Σ := {
  state_interp σ κs _ := True%I;
  fork_post _ := True%I;
}.

Class dsubPreG Σ := DsubPreG {
  dsubPreG_savior :> savedInterpG Σ vls vl;
  dsubPreG_interpNames : gen_iheapPreG stamp gname Σ;
}.

Definition dsubΣ := #[savedInterpΣ vls vl; gen_iheapΣ stamp gname].

Instance subG_dsubΣ {Σ} : subG dsubΣ Σ → dsubPreG Σ.
Proof. solve_inG. Qed.

(* For abstracting synToSem. *)
Class dsubInterpG Σ := DsubInterpG {
  dsub_interp: ty -> vls -> vl -> iProp Σ
}.

Notation "s ↦ γ" := (mapsto (hG := dsubG_interpNames) s γ)  (at level 20) : bi_scope.
Notation "s ↝ φ" := (∃ γ, s ↦ γ ∗ γ ⤇ φ)%I  (at level 20) : bi_scope.
Notation envD Σ := (vls -c> vl -c> iProp Σ).

Instance Inhϕ: Inhabited (envD Σ).
Proof. constructor. exact (λ _ _, False)%I. Qed.

Section mapsto.
  Context `{!dsubG Σ}.
  Global Instance: Persistent (s ↦ γ).
  Proof. apply _. Qed.
  Global Instance: Timeless (s ↦ γ).
  Proof. apply _. Qed.

  Definition allGs gs := (gen_iheap_ctx (hG := dsubG_interpNames) gs).
  Global Arguments allGs /.

  Lemma leadsto_agree s (φ1 φ2: envD Σ) ρ v: s ↝ φ1 -∗ s ↝ φ2 -∗ ▷ (φ1 ρ v ≡ φ2 ρ v).
  Proof.
    iIntros "/= #H1 #H2".
    iDestruct "H1" as (γ1) "[Hs1 Hg1]".
    iDestruct "H2" as (γ2) "[Hs2 Hg2]".
    iDestruct (mapsto_agree with "Hs1 Hs2") as %->.
    by iApply (saved_interp_agree _ φ1 φ2).
  Qed.
End mapsto.

(**
Possible future plan.

[s ↦ φ] defines when a stamp maps to a predicate in two steps:
1. s maps to γ in the logical heap.
2. and γ ⤇ φ through saved propositions.

Then, a non-Iris translation relation tells us that the stamped version of
[n]-closed AST [x] is [x']. That relation takes a stamp map [g]; the existence
of translation takes an input map [g] and produces an output map [g'] with new
entries.

That is, for each type definition [vty T] in [x], we have [vstamp vs s] in [x'],
with [s] pointing to [T'] where [T] stamps to [T'.|[to_subst vs]], and where
[nclosed T' (length vs)].

After translation [vs = idsσ n], but if [ξ] stamps to [ξ'] and [x] to [x'], we want
(x.|[ξ]) to stamp to (x'.|[ξ']).

Currently, there's a bug and the map contained unstamped [T], but that can be
fixed.

Finally, a persistent Iris predicate tells that entries [s -> T] in [g] are
properly reflected in Iris [s ↦ φ], where ⟦ T ⟧ and φ are related by a suitable
relation. That relation means that [∀ ρ v, ⟦ T ⟧ ρ v ≡ φ ρ v].

This is a family of
relations, one for each [n]; each of those relation seems to be a quasi-PER, an
asymmetric zig-zag relation which induces PERs (in fact, here equivalences) on
source and target:
on source [∀ ρ v, length ρ = n → ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v].
on target [∀ ρ v, length ρ = n → φ1 ρ v ≡ φ2 ρ v].
That is, if T n-relates to [φ1] and to [φ2], then [φ1] and [φ2] are related by
the target relation.

In the current translation we require a stronger relation, if [x] n-stamps to [x1] and
[x2], types in [x1] and [x2] are equivalent in this sense. Beware that if [x]
stamps to [x1] and [x2] but with different [n]s, types [x1] and [x2] are not
necessarily related.

Note we might not need that multiple translations are equivalent, if we manage
to translate entire typing derivations. However, it's best if we manage to
ensure that.

The current equivalence for stamping directly means that
[∀ ρ v, length ρ = n → ⟦ T ⟧ ρ v ≡ φ (vs.|[to_subst ρ]) v]. Substitution
preserves this relation, because it affects [T] on one side and [vs] on the
other. No substituion happens inside the map, but in this setting it might
happen at translation time.

XXX
Does substitution commute with translation at different times?
What happens if we we stamp [x.[ξ1]] to get [x1], or we stamp [x] to [x2] and
then substitute in it to get [x1.|[ξ2]], assuming [ξ1] stamps to [ξ2]?
Those are probably related in a suitable sense, tho that'd be a different
theorem from what we're needing yet; plus, the relation needs to use substitution.
If [x1] contains [vstamp s1 vs1] with [s1 -> T1] and [x2] contains [vstamp s2
vs2] with [s2 -> T2], we should only expect that
[T1.|[to_subst vs1]] equals [T2.|[to_subst vs2]]. Moreover, we need to make sure
we always substitute unstamped values before stamping and stamped values
afterwards.

*)
