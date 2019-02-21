From iris.program_logic Require Import ectx_language ectxi_language.
From iris.algebra Require Import ofe agree.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.iprop (* For gname *)
     lib.saved_prop invariants.
From iris.program_logic Require Import weakestpre.

From D Require Import tactics.
From D.DSub Require Export syn.

(** Instantiating iris with DSub *)
Module lang.

Definition to_val (t: tm) : option vl :=
  match t with
  | tv v => Some v
  | _ => None
  end.

Definition of_val: vl -> tm := tv.

Inductive ectx_item :=
| AppLCtx (e2: tm)
| AppRCtx (v1: vl).

Definition fill_item (Ki : ectx_item) (e : tm) : tm :=
  match Ki with
  | AppLCtx e2 => tapp e e2
  | AppRCtx v1 => tapp (tv v1) e
  end.

Definition state := unit.
Definition observation := unit.

Inductive head_step : tm -> state -> list observation -> tm -> state -> list tm -> Prop :=
| st_beta t1 v2 σ:
    head_step (tapp (tv (vabs t1)) (tv v2)) σ [] (t1.|[v2/]) σ []
| st_skip t σ:
    head_step (tskip t) σ [] t σ [].

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. done. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros; simplify_option_eq; auto with f_equal.
Qed.

Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

Lemma val_stuck e1 σ1 k e2 σ2 ef :
  head_step e1 σ1 k e2 σ2 ef → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 k e2 σ2 ef :
  head_step (fill_item Ki e) σ1 k e2 σ2 ef → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
           end; auto.
Qed.

Lemma dsub_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
split; apply _ || eauto using to_of_val, of_to_val, val_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.

End lang.

Export lang.

Canonical Structure dsub_ectxi_lang := EctxiLanguage lang.dsub_lang_mixin.
Canonical Structure dsub_ectx_lang := EctxLanguageOfEctxi dsub_ectxi_lang.
Canonical Structure dsub_lang := LanguageOfEctx dsub_ectx_lang.

Canonical Structure vlC := leibnizC vl.
Canonical Structure tmC := leibnizC tm.
Canonical Structure tyC := leibnizC ty.

Canonical Structure listVlC := leibnizC (list vl).

From D Require Import gen_iheap.

Class dsubG Σ := DsubG {
  dsubG_invG : invG Σ;
  dsubG_savior :> savedAnythingG Σ (vls -c> vl -c> ▶ ∙);
  dsubG_interpNames : gen_iheapG stamp gname Σ;
}.

Instance dsubG_irisG `{dsubG Σ} : irisG dsub_lang Σ := {
  iris_invG := dsubG_invG;
  state_interp σ κs _ := True%I;
  fork_post _ := True%I;
}.

Class dsubPreG Σ := DsubPreG {
  dsubPreG_invG : invPreG Σ;
  dsubPreG_savior :> savedAnythingG Σ (vls -c> vl -c> ▶ ∙);
  dsubPreG_interpNames : gen_iheapPreG stamp gname Σ;
}.

Definition dsubΣ := #[invΣ; savedAnythingΣ (vls -c> vl -c> ▶ ∙); gen_iheapΣ stamp gname].

Instance subG_dsubΣ {Σ} : subG dsubΣ Σ → dsubPreG Σ.
Proof. solve_inG. Qed.

(* For abstracting synToSem. *)
Class dsubInterpG Σ := DsubInterpG {
  dsub_interp: ty -> vls -> vl -> iProp Σ
}.

(** saved interpretations *)

Section saved_interp.
  Context `{!dsubG Σ}.

  Definition saved_interp_own (γ : gname) (Φ : vls → vl → iProp Σ) :=
    saved_anything_own
      (F := vls -c> vl -c> ▶ ∙) γ (λ vs v, CofeMor Next (Φ vs v)).

Instance saved_interp_own_contractive γ :
  Contractive (saved_interp_own γ : (vls -c> vl -c> iProp Σ) → iProp Σ).
Proof.
  intros n X Y HXY.
  rewrite /saved_interp_own /saved_anything_own /=.
  f_equiv. apply to_agree_ne; f_equiv.
  intros x y.
  apply Next_contractive.
  destruct n; simpl in *; auto.
  apply HXY.
Qed.

Lemma saved_interp_alloc_strong (G : gset gname) (Φ : vls → vl → iProp Σ) :
  (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ saved_interp_own γ Φ)%I.
Proof. iApply saved_anything_alloc_strong. Qed.

Lemma saved_interp_alloc (Φ : vls → vl → iProp Σ) :
  (|==> ∃ γ, saved_interp_own γ Φ)%I.
Proof. iApply saved_anything_alloc. Qed.

Lemma saved_interp_agree γ Φ Ψ vs v :
  saved_interp_own γ Φ -∗ saved_interp_own γ Ψ -∗ ▷ (Φ vs v ≡ Ψ vs v).
Proof.
  unfold saved_pred_own. iIntros "#HΦ #HΨ /=". iApply bi.later_equivI.
  iDestruct (saved_anything_agree with "HΦ HΨ") as "Heq".
  rewrite bi.ofe_fun_equivI; iSpecialize ("Heq" $! vs).
  by rewrite bi.ofe_fun_equivI; iSpecialize ("Heq" $! v); simpl.
Qed.

Lemma saved_interp_agree_eta γ Φ Ψ vs v :
  saved_interp_own γ (λ (vs : vls) (v : vl), (Φ vs) v) -∗
  saved_interp_own γ (λ (vs : vls) (v : vl), (Ψ vs) v) -∗
  ▷ (Φ vs v ≡ Ψ vs v).
Proof.
  iIntros "#H1 #H2".  
  repeat change (fun x => ?h x) with h.
  by iApply saved_interp_agree.
Qed.

Lemma saved_interp_impl γ Φ Ψ vs v :
  saved_interp_own γ Φ -∗ saved_interp_own γ Ψ -∗ □ (▷ Φ vs v -∗ ▷ Ψ vs v).
Proof.
  unfold saved_pred_own. iIntros "#HΦ #HΨ /= !# H1".
  iDestruct (saved_anything_agree with "HΦ HΨ") as "Heq".
  rewrite bi.ofe_fun_equivI; iSpecialize ("Heq" $! vs).
  rewrite bi.ofe_fun_equivI; iSpecialize ("Heq" $! v); simpl.
  rewrite bi.later_equivI.
  by iNext; iRewrite -"Heq".
Qed.

End saved_interp.

Notation "g ⤇ p" := (saved_interp_own g p) (at level 20).

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
