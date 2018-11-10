From iris.proofmode Require Export tactics.
From Dot Require Export operational.
Export lang.

Definition logN : namespace := nroot .@ "logN".

Section Sec.
  Context `{dotG Σ}.

  (* Semantic types *)
  Notation D := (vlC -n> iProp Σ).
  Notation envD := (listVlVlC -n> iProp Σ).

  Program Definition curryD {A B cC}: (leibnizC (A * B) -n> cC) -n> leibnizC A -n> (leibnizC B -n> cC) := λne φ ρ v, φ (ρ, v).
  Solve Obligations with solve_proper.

  Program Definition uncurryD {A B cC}: (leibnizC A -n> leibnizC B -n> cC) -n> (leibnizC (A * B) -n> cC) := λne φ ρv, let '(ρ, v) := ρv in φ ρ v.
  Next Obligation. intros; by move => [? ?] [? ?] [-> ->] /=. Qed.
  Next Obligation. intros; move => ? ? ? [? ?] /=. by solve_proper. Qed.
  Lemma curryDuncurryD {A B cC} (f: leibnizC A -n> leibnizC B -n> cC): curryD (uncurryD f) ≡ f.
  Proof. by intros ? ?. Qed.
  Lemma uncurryDcurryD {A B cC} (f: leibnizC (A * B) -n> cC): uncurryD (curryD f) ≡ f.
  Proof. by intros [? ?]. Qed.

  Definition curryD1: envD -n> listVlC -n> D := curryD.
  Definition uncurryD1: (listVlC -n> D) -n> envD := uncurryD.

  Implicit Types τi : D.

  Canonical Structure listVlDmsC := leibnizC (list vl * dms).
  (* Definition semantic types *)
  Notation MD := (dmsC -n> iProp Σ).
  Notation envMD := (listVlDmsC -n> iProp Σ).

  Notation inclusion P Q := (□∀ v, P v -∗ Q v)%I.

  Definition idms_proj_semtype ds l σ' φ : iProp Σ :=
    (∃ γ, ⌜ index_dms l ds = Some(dtysem σ' γ) ⌝ ∗ γ ⤇ φ)%I.
  Global Arguments idms_proj_semtype /.
  Notation "ds ; l ↘ σ , φ" := (idms_proj_semtype ds l σ φ) (at level 20).

  Definition idms_proj_val ds l w : iProp Σ :=
    (⌜ dms_proj_val ds l w ⌝)%I.
  Global Arguments idms_proj_val /.
  Notation "ds ;; l ↘ w" := (idms_proj_val ds l w) (at level 20).

  Definition defs_interp_vmem l (interp : envD): envMD := uncurryD (λne ρ, λne ds,
    (∃ vmem, ds ;; l ↘ vmem ∧ ▷ curryD interp ρ vmem))%I.

  Definition interp_vmem l (interp : envD) : envD := uncurryD (λne ρ, λne v,
    (∃ ds, ⌜ v ↗ ds ⌝ ∧ curryD (defs_interp_vmem l interp) ρ ds))%I.

  Definition subst_phi (σ: vls) (ρ: list vl) (φ: list vl * vl -> iProp Σ): D := λne v, φ  (vls_to_list (σ.[to_subst ρ]), v).

  Definition defs_interp_tmem l (interp1 interp2: envD): envMD := uncurryD (λne ρ, λne ds,
    (∃ φ σ, (ds;l ↘ σ , φ) ∗ ▷ inclusion (curryD interp1 ρ) (subst_phi σ ρ φ) ∗ ▷ inclusion (subst_phi σ ρ φ) (curryD interp2 ρ) ∗ inclusion (curryD interp1 ρ) (curryD interp2 ρ) ))%I.
    (* (∃ φ σ, (ds;l ↘ σ , φ) ∗ (inclusion (interp1 ρ) (φ (σ.[to_subst ρ]))) ∗ inclusion φ (interp2 ρ) )%I. *)

  Definition interp_tmem l (interp1 interp2 : envD) : envD := uncurryD (λne ρ, λne v,
    (∃ ds, ⌜ v ↗ ds ⌝ ∧ curryD (defs_interp_tmem l interp1 interp2) ρ ds))%I.

  Definition interp_and (interp1 interp2 : envD): envD := λne ρv,
    (interp1 ρv ∧ interp2 ρv) % I.

  Definition interp_or (interp1 interp2 : envD) : envD := λne ρv,
    (interp1 ρv ∨ interp2 ρv) % I.

  Definition interp_later (interp : envD) : envD := λne ρv,
         (▷ (interp ρv)) % I.

  Definition expr_of_pred (φ: D) (e: tm) : iProp Σ :=
    (WP e {{ v, φ v }} % I).

  Definition interp_forall (interp1 interp2 : envD) : envD := uncurryD (λne ρ, λne v,
    (□ ▷ ∀ v', curryD interp1 ρ v' -∗ expr_of_pred (curryD interp2 (v :: ρ)) (tapp (tv v) (tv v')))) % I.

  Program Definition interp_mu (interp : envD) : envD := uncurryD (λne ρ, λne v,
    (curryD interp (v::ρ) v)) % I.

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

  Definition subst_phi0 (σ: vls) (φ: list vl * vl -> iProp Σ): D := λne v, φ  (vls_to_list σ, v).
  Lemma subst_phi0_subst_phi σ φ: subst_phi0 σ φ ≡ subst_phi σ [] φ.
  Proof. move => ? /=; by asimpl. Qed.

  Program Definition interp_selA_final (l: label) (L U: D): list vl -> option vl -> D :=
    λ ρ optVa, λne v,
    (∃ va σ ϕ ds, ⌜ optVa = Some va ⌝ ∧ ⌜ va ↗ ds ⌝ ∧ ds;l ↘ σ , ϕ ∧ U v ∧ (L v ∨ ▷  subst_phi σ ρ ϕ v))%I.
  (* I first assumed that va and hence ϕ is closed, but it's not obvious I can. In fact, if va comes from within the type, it can probably be open. *)
    (* (∃ va σ ϕ ds, ⌜ optVa = Some va ⌝ ∧ ⌜ va ↗ ds ⌝ ∧ ds;l ↘ σ , ϕ ∧ U v ∧ (L v ∨ ▷  subst_phi0 σ ϕ v))%I. *)

  Fixpoint interp_sel_rec (ls: list label) (interp_k: option vl -> D): option vl -> D :=
    λ optVa, λne v,
    match ls with
    | l :: ls =>
      (∃ va ds vb, ⌜ optVa = Some va ⌝ ∧ ⌜ va ↗ ds ⌝ ∧ ds;;l ↘ vb ∧ interp_k (Some vb) v)%I
    | [] => interp_k optVa v
    end.

  Program Definition interp_selA (p: path) (l: label) (L U : envD): envD :=
    uncurryD (λne ρ, λne v,
     let (optVa, ls) := eval_split_path p ρ in
     □ interp_sel_rec ls (interp_selA_final l (curryD L ρ) (curryD U ρ) ρ) optVa v
    )%I.

  Definition interp_true : envD := λne ρv, True % I.
  Definition interp_false : envD := λne ρv, False % I.

  Definition interp_sel (p: path) (l: label) : envD :=
    interp_selA p l interp_false interp_true.

  (** Uncurried interpretation. *)
  Fixpoint uinterp (T: ty) : envD :=
    match T with
    | TTMem l L U => interp_tmem l (uinterp L) (uinterp U)
    | TVMem l T' => interp_vmem l (uinterp T')
    | TAnd T1 T2 => interp_and (uinterp T1) (uinterp T2)
    | TOr T1 T2 => interp_or (uinterp T1) (uinterp T2)
    | TLater T => interp_later (uinterp T)
    | TTop => interp_true
    | TBot => interp_false
    | TAll T1 T2 => interp_forall (uinterp T1) (uinterp T2)
    | TMu T => interp_mu (uinterp T)
    | TSel p l =>
      interp_sel p l
    | TSelA p l L U =>
      interp_selA p l (uinterp L) (uinterp U)
  end % I.

  (* It's important that this is a plain function: in proofs we want v and rho
     to be a plain vl, not a vlC, so that (ρ, v) is a plain pair and *then* it
     can be wrapped in a listVlVlC. Otherwise, I ended up with (list vl * vlC)
     in a rewrite lemma and (list vl * vl) in what I needed to rewrite, and
     rewrite was not happy.
     This requires eta-expansion to convert A -n> B to A -> B. *)
  Definition interp (T: ty): list vl -> vl -> iProp Σ :=
    λ ρ, curryD (uinterp T) ρ.
  (* Restore reduction behavior that interp had as a fixpoint. *)
  Global Arguments interp T /.

  Definition defs_interp_and (interp1 interp2 : envMD): envMD := λne ρds,
    (interp1 ρds ∧ interp2 ρds) % I.
  Definition defs_interp_false : envMD := λne ρds, False % I.
  Definition defs_interp_top : envMD := λne ρds, True % I.

  Fixpoint defs_uinterp (T: ty) : envMD :=
    match T with
    | TTMem l L U => defs_interp_tmem l (uinterp L) (uinterp U)
    | TVMem l T' => defs_interp_vmem l (uinterp T')
    | TAnd T1 T2 => defs_interp_and (defs_uinterp T1) (defs_uinterp T2)
    | TTop => defs_interp_top
    | _ => defs_interp_false
    end % I.

  Definition defs_interp (T: ty): list vl -> dms -> iProp Σ :=
    λ ρ, curryD (defs_uinterp T) ρ.
  Global Arguments defs_interp T /.

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

End Sec.

Notation "⟦ T ⟧" := (interp T).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
Notation "⟦ T ⟧ₑ" := (expr_of_pred ⟦T⟧).

Notation "Γ ⊨ T1 <: T2" := (ivstp Γ T1 T2) (at level 74, T1, T2 at next level).
