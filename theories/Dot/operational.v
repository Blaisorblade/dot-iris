From iris.program_logic Require Import ectx_language ectxi_language.
From iris.algebra Require Import ofe agree.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import lib.iprop (* For gname *)
     lib.saved_prop.
From D.pure_program_logic Require Export weakestpre.

From D Require Import tactics.
From D.Dot Require Export syn.
Export field_lookup.

Implicit Types
         (T: ty) (v: vl) (t e: tm) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx).

From D Require Export gen_iheap saved_interp.

Class dotG Σ := DotG {
  dotG_savior :> savedInterpG Σ vls vl;
  dotG_interpNames : gen_iheapG stamp gname Σ;
}.

Instance dotG_irisG `{dotG Σ} : irisG dlang_lang Σ := {
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
