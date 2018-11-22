From iris.proofmode Require Export tactics.
From Dot Require Export operational.
Export lang.

Definition logN : namespace := nroot .@ "logN".

(** Deduce types from variable names, like on paper, for readability and to help
    type inference for some overloaded operations (e.g. substitution). *)
Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Section Sec.
  Context `{dotG Σ}.

  (* Semantic types *)
  Notation D := (vlC -n> iProp Σ).
  Notation envD := (listVlVlC -n> iProp Σ).
  Implicit Types τi : D.

  Canonical Structure listVlDmsC := leibnizC (list vl * dms).
  (* Definition semantic types *)
  Notation MD := (dmsC -n> iProp Σ).
  Notation envMD := (listVlDmsC -n> iProp Σ).

  (* Semantic types for expressions. *)
  Notation ED := (tmC -n> iProp Σ).

  Program Definition curryD {A B cC}: (leibnizC (A * B) -n> cC) -n> leibnizC A -n> (leibnizC B -n> cC) := λne φ a b, φ (a, b).
  Solve Obligations with solve_proper.

  Program Definition uncurryD {A B cC}: (leibnizC A -n> leibnizC B -n> cC) -n> (leibnizC (A * B) -n> cC) := λne φ ab, let '(a, b) := ab in φ a b.
  Next Obligation. intros; by move => [? ?] [? ?] [-> ->] /=. Qed.
  Next Obligation. intros; move => ? ? ? [? ?] /=. by solve_proper. Qed.
  Lemma curryDuncurryD {A B cC} (f: leibnizC A -n> leibnizC B -n> cC): curryD (uncurryD f) ≡ f.
  Proof. by intros ? ?. Qed.
  Lemma uncurryDcurryD {A B cC} (f: leibnizC (A * B) -n> cC): uncurryD (curryD f) ≡ f.
  Proof. by intros [? ?]. Qed.

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

  (** Pointwise lifting of later to predicates. *)
  Program Definition delayPred `(P: A -n> iProp Σ): A -n> iProp Σ := λne a, (▷ P a)%I.
  Solve Obligations with solve_proper.
  Global Arguments delayPred /.

  (** Expression closure from [D] to [ED]. *)
  Definition expr_of_pred (φ: D): ED := λne e, WP e {{ φ }} % I.
  Global Arguments expr_of_pred /.
  Definition interp_expr (φ: envD): listVlC -n> ED := λne ρ, expr_of_pred (curryD φ ρ).

  Definition D_stp (P Q: D) : iProp Σ := (□ ∀ v, P v → |={⊤}=> Q v)%I.
  Global Arguments D_stp /.
  (* Recall that ▷(P ⇒ Q) ⊢ ▷ P ⇒ ▷ Q but not viceversa. Use the weaker choice to enable
     proving the definition typing lemma dtp_tmem_abs_i. *)
  Definition D_stp_later P Q := D_stp (delayPred P) (delayPred Q).
  Global Arguments D_stp_later /.

  (** Substitute into saved predicate [φ] to obtain a value predicate in [D].
      XXX instead of using persistence on ϕ, we might want to require that [ϕ]
      is persistent, here or elsewhere.
   *)
  Definition subst_phi (σ: vls) (ρ: list vl) (φ: list vl * vl -> iProp Σ): D := λne v, (□ φ (vls_to_list (σ.[to_subst ρ]), v))%I.
  Definition subst_phi0 (σ: vls) (φ: list vl * vl -> iProp Σ): D :=
    λne v, (□φ (vls_to_list σ, v))%I.
  Lemma subst_phi0_subst_phi σ φ: subst_phi0 σ φ ≡ subst_phi σ [] φ.
  Proof. move => ? /=; by asimpl. Qed.


  Definition defs_interp_tmem l (interp1 interp2: envD): envMD := uncurryD (λne ρ, λne ds,
    (∃ φ σ, (ds;l ↘ σ , φ) ∗
                           D_stp_later (curryD interp1 ρ) (subst_phi σ ρ φ) ∗
                           D_stp_later (subst_phi σ ρ φ) (curryD interp2 ρ) ∗
                           D_stp (curryD interp1 ρ) (curryD interp2 ρ)))%I.

  Definition interp_tmem l (interp1 interp2 : envD) : envD := uncurryD (λne ρ, λne v,
    (∃ ds, ⌜ v ↗ ds ⌝ ∧ curryD (defs_interp_tmem l interp1 interp2) ρ ds))%I.

  Definition interp_and (interp1 interp2 : envD): envD := λne ρv,
    (interp1 ρv ∧ interp2 ρv) % I.

  Definition interp_or (interp1 interp2 : envD) : envD := λne ρv,
    (interp1 ρv ∨ interp2 ρv) % I.

  Definition interp_later (interp : envD) : envD := λne ρv,
         (▷ (interp ρv)) % I.

  Definition interp_forall (interp1 interp2 : envD) : envD := uncurryD (λne ρ, λne v,
    (□ ▷ ∀ v', curryD interp1 ρ v' -∗ interp_expr interp2 (v :: ρ) (tapp (tv v) (tv v')))) % I.

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

  Program Definition interp_selA_final (l: label) (interpL interpU: D): list vl -> option vl -> D :=
    λ ρ optVa, λne v,
    (∃ va σ ϕ ds, ⌜ optVa = Some va ⌝ ∧ ⌜ va ↗ ds ⌝ ∧ ds;l ↘ σ , ϕ ∧ interpU v ∧ (interpL v ∨ ▷ subst_phi σ ρ ϕ v))%I.
  (* I first assumed that va and hence ϕ is closed, but it's not obvious I can. In fact, if va comes from within the type, it can probably be open. *)
    (* (∃ va σ ϕ ds, ⌜ optVa = Some va ⌝ ∧ ⌜ va ↗ ds ⌝ ∧ ds;l ↘ σ , ϕ ∧ U v ∧ (L v ∨ ▷  subst_phi0 σ ϕ v))%I. *)

  (** XXX Pretty confusing that we only go a step down at the end. *)
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
  Definition defs_interp_true : envMD := λne ρds, True % I.

  Fixpoint defs_uinterp (T: ty) : envMD :=
    match T with
    | TTMem l L U => defs_interp_tmem l (uinterp L) (uinterp U)
    | TVMem l T' => defs_interp_vmem l (uinterp T')
    | TAnd T1 T2 => defs_interp_and (defs_uinterp T1) (defs_uinterp T2)
    | TTop => defs_interp_true
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

  Global Instance defs_interp_persistent T ρ ds :
    Persistent (defs_interp T ρ ds).
  Proof.
    revert ds ρ; induction T; simpl; try apply _.
  Qed.

  Global Instance interp_env_persistent Γ ρ :
    Persistent (⟦ Γ ⟧* ρ) := _.
  Proof.
    revert ρ. induction Γ.
    - rewrite /Persistent /interp_env. eauto.
    - simpl. destruct ρ; rewrite /Persistent; eauto.
  Qed.

  (* Definitions for semantic (definition) (sub)typing *)
  Definition idtp Γ T ds : iProp Σ := (□∀ ρ, ⟦Γ⟧* ρ → defs_interp T ρ ds)%I.
  Global Arguments idtp /.

  Notation "⟦ T ⟧ₑ" := (interp_expr (uinterp T)).
  Definition istp Γ T1 T2 : iProp Σ := (□∀ ρ e, ⟦Γ⟧* ρ → ⟦T1⟧ₑ ρ e → ⟦T2⟧ₑ ρ e)%I.
  Global Arguments istp /.

  Definition ivtp Γ T v : iProp Σ := (□∀ ρ, ⟦Γ⟧* ρ → ⟦T⟧ ρ v)%I.
  Global Arguments ivtp /.

  Definition ietp Γ T e : iProp Σ := (□∀ ρ, ⟦Γ⟧* ρ → ⟦T⟧ₑ ρ (e.[to_subst ρ]))%I.
  Global Arguments ietp /.

  (* Pretty clearly, this isn't quite what we want. *)
  Definition ivstp Γ T1 T2: iProp Σ := (□∀ ρ v, ⟦Γ⟧* ρ → ⟦T1⟧ ρ v → ⟦T2⟧ ρ v)%I.
  Global Arguments ivstp /.

  (* Value subtyping, defined to be equivalent to (expression) subtyping. *)
  Definition uvstp Γ T1 T2: iProp Σ :=
    (□∀ ρ v, ⟦Γ⟧*ρ -∗ ((*|={⊤}=>*) ⟦T1⟧ ρ v) → |={⊤}=> ⟦T2⟧ ρ v)%I.
  Global Arguments uvstp /.
End Sec.

Notation "⟦ T ⟧" := (interp T).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
Notation "⟦ T ⟧ₑ" := (interp_expr (uinterp T)).

Notation "Γ ⊨ T1 <: T2" := (istp Γ T1 T2) (at level 74, T1, T2 at next level).
Notation "Γ ⊨ e : T" := (ietp Γ e T) (at level 74, e, T at next level).

Notation "Γ ⊨v T1 <: T2" := (ivstp Γ T1 T2) (at level 74, T1, T2 at next level).
Notation "Γ ⊨> T1 <: T2" := (uvstp Γ T1 T2) (at level 74, T1, T2 at next level).

Section SubTypingEquiv.
  Context `{HdotG: dotG Σ} (Γ: list ty).

  (** We prove that vstp and stp are equivalent, so that we can use them
      interchangeably; and in my previous proofs, proving uvstp was easier. *)

  Lemma iStpUvstp T1 T2: (Γ ⊨ T1 <: T2 → Γ ⊨> T1 <: T2)%I.
  Proof.
    (* Inspired by the proof of wp_value_inv'! *)

    (* More manual.*)
    (* iIntros "/= #Hsub !> * #Hg *". *)
    (* iSpecialize ("Hsub" $! (of_val v) with "Hg"). *)
    (* rewrite !wp_unfold /wp_pre /=. iIntros. by iApply "Hsub". *)
    (* Restart. *)
    iIntros "/= #Hsub !> * #Hg *".
    setoid_rewrite wp_unfold.
    iIntros.
    by iApply ("Hsub" $! _ (of_val v)).
  Qed.

  (* And subtyping later is enough to imply expression subtyping: *)
  Lemma iVstpUpdatedStp T1 T2: (Γ ⊨> T1 <: T2 → Γ ⊨ T1 <: T2)%I.
  Proof.
    iIntros "/= #Hstp !> * #Hg HeT1".
    (* Low level: *)
    (* by iApply (wp_strong_mono with "HeT1"); *)
    (*   last (iIntros "* HT1"; iApply "Hstp"). *)
    (* Just with proof rules documented in the appendix. *)
    iApply wp_fupd.
    iApply (wp_wand with " [-]"); try iApply "HeT1".
    iIntros "* HT1". by iApply "Hstp".
  Qed.

  Lemma istpEqIvstp T1 T2: (Γ ⊨ T1 <: T2) ≡ (Γ ⊨> T1 <: T2).
  Proof. iSplit; iIntros; by [iApply iStpUvstp| iApply iVstpUpdatedStp]. Qed.
End SubTypingEquiv.
