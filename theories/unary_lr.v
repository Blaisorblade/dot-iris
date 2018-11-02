Require Import Dot.dotsyn.
Require Import Dot.operational.
Import lang.

From iris Require Import base_logic.lib.saved_prop.
(* From iris Require Import base_logic.base_logic. *)

From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.algebra Require Import list.
From iris.base_logic Require Import invariants.

Definition logN : namespace := nroot .@ "logN".

Class dotG Σ := DotG {
  dotG_invG : invG Σ;
  dotG_savior :> savedPredG Σ vl
}.

Instance dotG_irisG `{dotG Σ} : irisG dot_lang Σ := {
  iris_invG := dotG_invG;
  state_interp σ κs _ := True%I;
  fork_post _ := True%I;
}.

Section Sec.
  Context `{dotG Σ}.
  (* Check savedPredG0. *)
  (* Print savedPredG. *)
  (* Print savedAnythingG. *)

  Definition SP γ ϕ := saved_pred_own γ ϕ.
  Notation "g ⤇ p" := (SP g p) (at level 20).

  Definition object_proj_semtype v l φ : iProp Σ :=
    (∃ γ ds, ⌜ v = vobj ds ∧ index_dms l (selfSubst ds) = Some(dtysem γ) ⌝ ∗ γ ⤇ φ)%I.

  Definition object_proj_val v l w : iProp Σ :=
    (∃ ds, ⌜ v = vobj ds ∧ dms_proj_val ds l w ⌝)%I.

  Notation "v ; l ↘ φ" := (object_proj_semtype v l φ)%I (at level 20).
  Notation "v ;; l ↘ w" := (object_proj_val v l w)%I (at level 20).

  Canonical Structure vlC := leibnizC vl.
  Canonical Structure tmC := leibnizC tm.
  Notation D := (vlC -n> iProp Σ).
  Implicit Types τi : D.

  SearchAbout Wp.

  Program Definition interp_expr (φ: D) (e: tm) : iProp Σ :=
    (WP e {{ v, φ v }} % I).

  Program Definition interp_and (interp1 interp2 : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
    (interp1 ρ v  ∧  interp2 ρ v) % I.
  Solve Obligations with solve_proper.


  Program Definition interp_or (interp1 interp2 : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
    (interp1 ρ v  ∨  interp2 ρ v) % I.
  Solve Obligations with solve_proper.

  Notation inclusion P Q := (∀ v, P v -∗ Q v)%I.

  Program Definition interp_mem (l: label) (interp1 interp2 : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
    (∃ φ, (v;l ↘ φ) ∗ (inclusion (interp1 ρ) φ) ∗ inclusion φ (interp2 ρ) )%I.
  Solve Obligations with solve_proper.

  Program Definition interp_later (interp : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
         (▷ (interp ρ v)) % I.
  Solve Obligations with solve_proper.

  Program Definition interp_forall (interp1 interp2 : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
    (▷ ∀ v', interp1 ρ v' -∗ interp_expr (interp2 (v :: ρ)) (tapp (tv v) (tv v'))) % I.
  Solve Obligations with solve_proper.
  Next Obligation. admit. Admitted.

  Program Definition interp_val_mem l (interp : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
    (∃ vmem, v;;l ↘ vmem ∧ ▷ interp ρ vmem) % I.
  Solve Obligations with solve_proper.

  Program Definition interp_mu (interp : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
    (interp (v::ρ) v) % I.
  Solve Obligations with solve_proper.
  
  Program Definition interp_true : listC vlC -n> D := λne ρ v, True % I.
  Program Definition interp_false : listC vlC -n> D := λne ρ v, False % I.

  Fixpoint interp (T: ty) : listC vlC -n> D := 
    match T with
    | TAnd T1 T2 => interp_and (interp T1) (interp T2)
    | TOr T1 T2 => interp_or (interp T1) (interp T2)
    | TTMem l L U => interp_mem l (interp L) (interp U)
    | TLater T => interp_later (interp T)
    | TTop => interp_true
    | TBot => interp_false
    | TAll T1 T2 => interp_forall (interp T1) (interp T2)
    | TMu T => interp_mu (interp T)
    | TSel p l => interp_true (* ∃ γ ϕ ds, ⌜ v = vobj ds ∧ index_dms l ds = Some(dtysem γ) ⌝ ∧ (SP γ ϕ) *)
    | TSelA p l L U => interp_false
    | TVMem l T' => interp_val_mem l (interp T')
  end % I.

  Notation "⟦ T ⟧" := (interp T).

  (* use foldr? *)
  Fixpoint interp_env (Γ : list ty): list vl -> iProp Σ :=
    match Γ with
    | nil => (fun l => (⌜ l = nil ⌝) % I)
    | T::Γ' => (fun l => match l with
                         | nil => False
                         | v::ρ => (interp_env Γ') ρ ∗ ⟦ T ⟧ (v::ρ) v
                         end
               )%I
    end.
  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  (* Some subtyping lemmas, directly in terms of interp. *)
  Lemma stp_later T ρ v (H: interp T ρ v): interp (TLater T) ρ v.
  Proof. simpl; iNext. iApply H. Qed.

  Lemma stp_and1 T1 T2 ρ v: interp (TAnd T1 T2) ρ v -> interp T1 ρ v.
  Proof.
    simpl in *. intros Hv.
    iDestruct Hv as "[H1 H2]".
    iAssumption.
  Qed.

  Lemma stp_and2 T1 T2 ρ v: interp (TAnd T1 T2) ρ v -> interp T2 ρ v.
  Proof.
    simpl in *. intros Hv.
    iDestruct Hv as "[H1 H2]".
    iAssumption.
  Qed.

  Lemma stp_and1_fails T1 T2 ρ v: interp (TAnd T1 T2) ρ v -∗ interp T2 ρ v.
  Proof.
    simpl in *. iIntros "Hv".
    (* This would turn P ∧ Q into P, Q in the Iris context (that is, P * Q), but
    this is illegal unless P and Q are persistent. *)
    Fail iDestruct "Hv" as "[H1 H2]".
    Fail iAssumption.
   Abort.

  Lemma stp_and_w T1 T2 ρ v:
    interp T1 ρ v ->
    interp T2 ρ v ->
    interp (TAnd T1 T2) ρ v.
  Proof.
    simpl in *. intros.
    iSplit.
    iApply H.
    iApply H0.
  Qed.

  Lemma stp_and T1 T2 ρ v:
    interp T1 ρ v -∗
    interp T2 ρ v -∗
    interp (TAnd T1 T2) ρ v.
  Proof. iIntros; by iSplit. Qed.
End Sec.
