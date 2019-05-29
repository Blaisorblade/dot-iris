From iris.program_logic Require Import ectx_language ectxi_language.
From iris.algebra Require Import ofe agree.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.iprop (* For gname *)
     lib.saved_prop.
From D.pure_program_logic Require Export weakestpre.

From D Require Import tactics.
From D.Dot Require Export syn.

Implicit Types
         (T: ty) (v: vl) (t e: tm) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx).
(** Substitute object inside itself (to give semantics to the "self"
    variable). To use when descending under the [vobj] binder. *)
Definition selfSubst ds: dms := ds.|[vobj ds/].

(* Unset Program Cases. *)
(* Definition gmap_of_dms ds: gmap label dm := map_of_list ds. *)
(* Definition dms_lookup l ds := gmap_of_dms ds !! l. *)
(* Arguments gmap_of_dms /. *)
(* Arguments dms_lookup /. *)

Definition objLookup v (l: label) d: Prop :=
  ∃ ds, v = vobj ds ∧ (dms_lookup l (selfSubst ds)) = Some d.
Notation "v @ l ↘ d" := (objLookup v l d) (at level 20).

(** Instead of letting obj_opens_to autounfold,
    provide tactics to show it's deterministic and so on. *)

(** Rewrite v ↗ ds to vobj ds' ↗ ds. *)
Ltac simplOpen ds :=
  lazymatch goal with
  | H: ?v @ ?l ↘ ?d |-_=>
    inversion H as (ds & -> & _)
  end.

(** Determinacy of obj_opens_to. *)
Lemma objLookupDet v l d1 d2: v @ l ↘ d1 -> v @ l ↘ d2 -> d1 = d2.
Proof. rewrite /objLookup => *; ev. by simplify_eq. Qed.
Ltac objLookupDet :=
  lazymatch goal with
  | H1: ?v @ ?l ↘ ?d1, H2: ?v @ ?l ↘ ?d2 |- _=>
    assert (d2 = d1) as ? by (eapply objLookupDet; eassumption); injectHyps
  end.

From D Require Export gen_iheap saved_interp.

Class dotG Σ := DotG {
  dotG_savior :> savedInterpG Σ vls vl;
  dotG_interpNames : gen_iheapG stamp gname Σ;
}.

Instance dotG_irisG `{dotG Σ} : irisG dot_lang Σ := {
  state_interp σ κs _ := True%I;
  fork_post _ := True%I;
}.

Class dotPreG Σ := DotPreG {
  dotPreG_savior :> savedInterpG Σ vls vl;
  dotPreG_interpNames : gen_iheapPreG stamp gname Σ;
}.

Definition dotΣ := #[savedInterpΣ vls vl; gen_iheapΣ stamp gname].

Instance subG_dotΣ {Σ} : subG dotΣ Σ → dotPreG Σ.
Proof. solve_inG. Qed.

(* For abstracting synToSem. *)
Class dotInterpG Σ := DotInterpG {
  dot_interp: ty -> vls -> vl -> iProp Σ
}.

Notation "s ↦ γ" := (mapsto (hG := dotG_interpNames) s γ)  (at level 20) : bi_scope.
Notation "s ↝ φ" := (∃ γ, s ↦ γ ∗ γ ⤇ φ)%I  (at level 20) : bi_scope.
Notation envD Σ := (vls -c> vl -c> iProp Σ).

Instance Inhϕ: Inhabited (envD Σ).
Proof. constructor. exact (λ _ _, False)%I. Qed.

Section mapsto.
  Context `{!dotG Σ}.
  Global Instance: Persistent (s ↦ γ).
  Proof. apply _. Qed.
  Global Instance: Timeless (s ↦ γ).
  Proof. apply _. Qed.

  Definition allGs gs := (gen_iheap_ctx (hG := dotG_interpNames) gs).
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
