Require Export Dot.operational.
Export lang.

From iris Require Export base_logic.lib.saved_prop.
From iris.proofmode Require Export tactics.
From iris.program_logic Require Export weakestpre.
From iris.algebra Require Export list.
From iris.base_logic Require Export invariants.

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
End Sec.
Notation "g ⤇ p" := (SP g p) (at level 20).

Section Sec2.
  Context `{dotG Σ}.

  Canonical Structure vlC := leibnizC vl.
  Canonical Structure tmC := leibnizC tm.
  Canonical Structure dmsC := leibnizC dms.
  Canonical Structure listVlC := leibnizC (list vl).

  (* Semantic types *)
  Notation D := (vlC -n> iProp Σ).
  Notation envD := (listVlC -n> D).
  Implicit Types τi : D.

  (* Definition semantic types *)
  Notation MD := (dmsC -n> iProp Σ).
  Notation envMD := (listVlC -n> MD).

  Notation inclusion P Q := (□∀ v, P v -∗ Q v)%I.

  Definition idms_proj_semtype ds l σ' φ : iProp Σ :=
    (∃ γ, ⌜ index_dms l ds = Some(dtysem σ' γ) ⌝ ∗ γ ⤇ φ)%I.
  Global Arguments idms_proj_semtype /.
  Notation "ds ; l ↘ σ , φ" := (idms_proj_semtype ds l σ φ) (at level 20).

  Definition idms_proj_val ds l w : iProp Σ :=
    (⌜ dms_proj_val ds l w ⌝)%I.
  Global Arguments idms_proj_val /.
  Notation "ds ;; l ↘ w" := (idms_proj_val ds l w) (at level 20).

  Definition defs_interp_vmem l (interp : envD): envMD := λne ρ, λne ds,
    (∃ vmem, ds ;; l ↘ vmem ∧ ▷ interp ρ vmem)%I.

  Definition interp_vmem l (interp : envD) : envD := λne ρ, λne v,
    (∃ ds, ⌜ v ↗ ds ⌝ ∧ defs_interp_vmem l interp ρ ds)%I.

  Definition to_subst (ρ: list vl) i: vl :=
    match ρ !! i with
      | Some v => v
      | None => var_vl i
    end.

  Definition defs_interp_tmem l (interp1 interp2: envD): envMD := λne ρ, λne ds,
    (∃ φ σ, (ds;l ↘ σ , φ) ∗ ▷ inclusion (interp1 ρ) φ ∗ ▷ inclusion φ (interp2 ρ) ∗ inclusion (interp1 ρ) (interp2 ρ) )%I.
    (* (∃ φ σ, (ds;l ↘ σ , φ) ∗ (inclusion (interp1 ρ) (φ (σ.[to_subst ρ]))) ∗ inclusion φ (interp2 ρ) )%I. *)

  Definition interp_tmem l (interp1 interp2 : envD) : envD := λne ρ, λne v,
    (∃ ds, ⌜ v ↗ ds ⌝ ∧ defs_interp_tmem l interp1 interp2 ρ ds)%I.

  Definition interp_and (interp1 interp2 : envD): envD := λne ρ, λne v,
    (interp1 ρ v ∧ interp2 ρ v) % I.

  Definition interp_or (interp1 interp2 : envD) : envD := λne ρ, λne v,
    (interp1 ρ v ∨ interp2 ρ v) % I.

  Definition interp_later (interp : envD) : envD := λne ρ, λne v,
         (▷ (interp ρ v)) % I.

  Definition expr_of_pred (φ: D) (e: tm) : iProp Σ :=
    (WP e {{ v, φ v }} % I).

  Definition interp_forall (interp1 interp2 : envD) : envD := λne ρ, λne v,
    (□ ▷ ∀ v', interp1 ρ v' -∗ expr_of_pred (interp2 (v :: ρ)) (tapp (tv v) (tv v'))) % I.

  Program Definition interp_mu (interp : envD) : envD := λne ρ, λne v,
    (interp (v::ρ) v) % I.

  Canonical Structure optionVlC := leibnizC (option vl).
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
    (∃ va σ ϕ ds, ⌜ optVa = Some va ⌝ ∧ ⌜ va ↗ ds ⌝ ∧ ds;l ↘ σ , ϕ ∧ U v ∧ (L v ∨ ▷ ϕ v))%I.

  Fixpoint interp_sel_rec (ls: list label) (interp_k: option vl -> D): option vl -> D :=
    λ optVa, λne v,
    match ls with
    | l :: ls =>
      (∃ va ds vb, ⌜ optVa = Some va ⌝ ∧ ⌜ va ↗ ds ⌝ ∧ ds;;l ↘ vb ∧ interp_k (Some vb) v)%I
    | [] => interp_k optVa v
    end.

  Program Definition interp_selA (p: path) (l: label) (L U : envD): envD :=
    (λne ρ, λne v,
     let (optVa, ls) := eval_split_path p ρ in
     □ interp_sel_rec ls (interp_selA_final l (L ρ) (U ρ)) optVa v
    )%I.

  Definition interp_true : envD := λne ρ, λne v, True % I.
  Definition interp_false : envD := λne ρ, λne v, False % I.

  Definition interp_sel (p: path) (l: label) : envD :=
    interp_selA p l interp_false interp_true.

  Fixpoint interp (T: ty) : envD :=
    match T with
    | TTMem l L U => interp_tmem l (interp L) (interp U)
    | TVMem l T' => interp_vmem l (interp T')
    | TAnd T1 T2 => interp_and (interp T1) (interp T2)
    | TOr T1 T2 => interp_or (interp T1) (interp T2)
    | TLater T => interp_later (interp T)
    | TTop => interp_true
    | TBot => interp_false
    | TAll T1 T2 => interp_forall (interp T1) (interp T2)
    | TMu T => interp_mu (interp T)
    | TSel p l =>
      interp_sel p l
    | TSelA p l L U =>
      interp_selA p l (interp L) (interp U)
  end % I.

  Definition defs_interp_and (interp1 interp2 : envMD): envMD := λne ρ, λne ds,
    (interp1 ρ ds ∧ interp2 ρ ds) % I.
  Definition defs_interp_false : envMD := λne ρ, λne ds, False % I.
  (* Taken from code for OOPSLA16 DOT paper. *)
  Definition defs_interp_top : envMD := λne ρ, λne ds, True % I.

  Fixpoint defs_interp (T: ty) : envMD :=
    match T with
    | TTMem l L U => defs_interp_tmem l (interp L) (interp U)
    | TVMem l T' => defs_interp_vmem l (interp T')
    | TAnd T1 T2 => defs_interp_and (defs_interp T1) (defs_interp T2)
    | TTop => defs_interp_top
    | _ => defs_interp_false
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
    revert v ρ; induction T; simpl;
                                       try destruct (split_path p);
                                       try apply _.
  Qed.

  Global Instance defs_interp_persistent T ρ v :
    Persistent (defs_interp T ρ v).
  Proof.
    revert v ρ; induction T; simpl; try apply _.
  Qed.

  Global Instance interp_env_persistent Γ ρ :
    Persistent (⟦ Γ ⟧* ρ) := _.
  Proof.
    revert ρ. induction Γ.
    - rewrite /Persistent /interp_env. eauto.
    - simpl. destruct ρ; rewrite /Persistent; eauto.
  Qed.

  Implicit Types T: ty.

  (* Definitions for semantic (definition) (sub)typing *)
  Definition vstp Γ T1 T2 := ∀ v ρ, ⟦Γ⟧* ρ -> ⟦T1⟧ ρ v -> ⟦T2⟧ ρ v.
  Definition ivstp Γ T1 T2: iProp Σ := (□∀ v ρ, ⟦Γ⟧* ρ -∗ ⟦T1⟧ ρ v -∗ ⟦T2⟧ ρ v)%I.
  Global Arguments vstp /.
  Global Arguments ivstp /.

  Definition ivtp Γ T v : iProp Σ := (□∀ ρ, ⟦Γ⟧* ρ -∗ ⟦T⟧ ρ v)%I.
  Global Arguments ivtp /.

  Definition idtp Γ T ds : iProp Σ := (□∀ ρ, ⟦Γ⟧* ρ -∗ defs_interp T ρ ds)%I.
  Global Arguments idtp /.

End Sec2.

Notation "⟦ T ⟧" := (interp T).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
Notation "⟦ T ⟧ₑ" := (expr_of_pred ⟦T⟧).

Notation "Γ ⊨ T1 <: T2" := (ivstp Γ T1 T2) (at level 74, T1, T2 at next level).
