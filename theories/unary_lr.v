Require Import Dot.dotsyn.
Require Import Dot.operational.
Import lang.

From iris Require Import base_logic.lib.saved_prop.
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

  Definition SP γ ϕ := saved_pred_own γ ϕ.
  Notation "g ⤇ p" := (SP g p) (at level 20).

  Definition object_proj_semtype v l φ : iProp Σ :=
    (∃ γ ds, ⌜ v = vobj ds ∧ index_dms l (selfSubst ds) = Some(dtysem γ) ⌝ ∗ γ ⤇ φ)%I.
  Global Arguments object_proj_semtype /.

  Definition object_proj_val v l w : iProp Σ :=
    (∃ ds, ⌜ v = vobj ds ∧ dms_proj_val ds l w ⌝)%I.
  Global Arguments object_proj_val /.

  Notation "v ; l ↘ φ" := (object_proj_semtype v l φ)%I (at level 20).
  Notation "v ;; l ↘ w" := (object_proj_val v l w)%I (at level 20).

  Canonical Structure vlC := leibnizC vl.
  Canonical Structure tmC := leibnizC tm.
  Notation D := (vlC -n> iProp Σ).
  Notation envD := (list vl -> D).
  Implicit Types τi : D.

  Definition interp_expr (φ: D) (e: tm) : iProp Σ :=
    (WP e {{ v, φ v }} % I).

  Definition interp_and (interp1 interp2 : envD): envD := λ ρ, λne v,
    (interp1 ρ v ∧ interp2 ρ v) % I.

  Definition interp_or (interp1 interp2 : envD) : envD := λ ρ, λne v,
    (interp1 ρ v ∨ interp2 ρ v) % I.

  Notation inclusion P Q := (∀ v, P v -∗ Q v)%I.

  (* XXX on paper we need to check inclusion later, I expect we'll need this in
     one of the lemmas. *)
  Definition interp_mem (l: label) (interp1 interp2 : envD) : envD := λ ρ, λne  v,
  (□ ∃ φ, (v;l ↘ φ) ∗ (inclusion (interp1 ρ) φ) ∗ inclusion φ (interp2 ρ) )%I.

  Definition interp_later (interp : envD) : envD := λ ρ, λne v,
         (▷ (interp ρ v)) % I.

  Definition interp_forall (interp1 interp2 : envD) : envD := λ ρ, λne v,
    (□ ▷ ∀ v', interp1 ρ v' -∗ interp_expr (interp2 (v :: ρ)) (tapp (tv v) (tv v'))) % I.

  Definition interp_val_mem l (interp : envD) : envD := λ ρ, λne v,
    (∃ vmem, v;;l ↘ vmem ∧ ▷ interp ρ vmem) % I.

  Definition interp_mu (interp : envD) : envD := λ ρ, λne v,
    (interp (v::ρ) v) % I.

  Definition close_vl (va: vl): list vl -> option vl :=
    λ ρ,
    match va with
    | var_vl n => ρ !! n
    | vabs t => Some (vabs t)
    | vobj ds => Some (vobj ds)
    end.

  Fixpoint split_path (p: path): vl * list label :=
    match p with
    | pv va => (va, [])
    | pself p l =>
      let '(v, ls) := split_path p in (v, ls ++ [l])
    end.

  Definition eval_split_path (p: path): list vl -> (option vl) * (list label) :=
    λ ρ,
    let '(v, ls) := split_path p in
    (close_vl v ρ, ls).
  Arguments eval_split_path /.

  Canonical Structure dmC := leibnizC dm.

  Program Definition interp_selA_final (l: label) (L U: D): option vl -> D :=
    λ optVa, λne v,
    (∃ γ ϕ ds, ⌜ optVa = Some (vobj ds) ∧ index_dms l (selfSubst ds) = Some(dtysem γ) ⌝ ∧ (SP γ ϕ) ∧ U v ∧ (L v ∨ ▷ ϕ v))%I.

  Fixpoint interp_sel_rec (ls: list label) (interp_k: option vl -> D): option vl -> D :=
    λ optVa, λne v,
    match ls with
    | l :: ls =>
      (∃ ds vb, ⌜ optVa = Some (vobj ds) ∧ index_dms l (selfSubst ds) = Some (dvl vb) ⌝ ∧ interp_k (Some vb) v)%I
    | [] => interp_k optVa v
    end.

  Definition interp_selA (p: path) (l: label) (L U : envD): envD :=
    (λ ρ, λne v,
     let (optVa, ls) := eval_split_path p ρ in
     □ interp_sel_rec ls (interp_selA_final l (L ρ) (U ρ)) optVa v
    )%I.

  Definition interp_true : envD := λ ρ, λne v, True % I.
  Definition interp_false : envD := λ ρ, λne v, False % I.

  Definition interp_sel (p: path) (l: label) : envD :=
    interp_selA p l interp_false interp_true.

  Fixpoint interp (T: ty) : envD :=
    match T with
    | TAnd T1 T2 => interp_and (interp T1) (interp T2)
    | TOr T1 T2 => interp_or (interp T1) (interp T2)
    | TTMem l L U => interp_mem l (interp L) (interp U)
    | TLater T => interp_later (interp T)
    | TTop => interp_true
    | TBot => interp_false
    | TAll T1 T2 => interp_forall (interp T1) (interp T2)
    | TMu T => interp_mu (interp T)
    | TSel p l =>
      interp_sel p l
    | TSelA p l L U =>
      interp_selA p l (interp L) (interp U)
    | TVMem l T' => interp_val_mem l (interp T')
  end % I.

  Notation "⟦ T ⟧" := (interp T).

  (* use foldr? *)
  (* PG: Or use a judgment that we can invert? *)
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

  Global Instance interp_persistent T ρ v :
    Persistent (⟦ T ⟧ ρ v).
  Proof.
    revert v ρ; induction T; try move => v Δ HΔ; simpl;
                                          try destruct (split_path p);
                                          try apply _.
  Qed.

  Global Instance interp_env_persistent Γ ρ :
    Persistent (⟦ Γ ⟧* ρ) := _.
  Proof.
    revert ρ. induction Γ.
    - rewrite /Persistent /interp_env. eauto.
    - simpl. destruct ρ; rewrite /Persistent; eauto.
  Qed.
End Sec.
