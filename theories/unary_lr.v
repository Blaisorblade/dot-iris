From iris.proofmode Require Export tactics.
From Dot Require Export operational.
Export lang.

(** Deduce types from variable names, like on paper, for readability and to help
    type inference for some overloaded operations (e.g. substitution). *)
Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms)
         (Γ : ctx) (ρ : leibnizC vls).


Section logrel.
  Context `{dotG Σ}.

  Notation D := (vlC -n> iProp Σ).
  Implicit Types τi : D.

  Definition subst_phi (σ: vls) (ρ: vls) (φ : listVlC -n> D) : D :=
    λne v, (□ φ σ.|[to_subst ρ] v)%I.

  Lemma subst_phi0_subst_phi (φ : listVlC -n> D) σ v :
    subst_phi σ [] φ v ≡ (□ φ σ v)%I.
  Proof. by intros; rewrite /= to_subst_nil; asimpl. Qed.

  Definition def_interp_vmem (interp : listVlC -n> D) :
    listVlC -n> dmC -n> iProp Σ :=
    λne ρ d, (∃ vmem, ⌜d = dvl vmem⌝ ∧ ▷ interp ρ vmem)%I.

  Definition interp_vmem l (interp : listVlC -n> D) : listVlC -n> D :=
    λne ρ v, (∃ d, ⌜v @ l ↘ d⌝ ∧ def_interp_vmem interp ρ d)%I.

  Definition idm_proj_semtype d σ' (φ : listVlC -n> D) : iProp Σ :=
    (∃ γ, ⌜ d = dtysem σ' γ ⌝ ∗ γ ⤇ (λ vs w, φ vs w))%I.
  Global Arguments idm_proj_semtype /.
  Notation "d ↗ σ , φ" := (idm_proj_semtype d σ φ) (at level 20).

  Definition def_interp_tmem (interp1 interp2 : listVlC -n> D) :
    listVlC -n> dmC -n> iProp Σ :=
    λne ρ d,
    (∃ φ σ, (d ↗ σ , φ) ∗
       □ ((∀ v, ▷ interp1 ρ v → ▷ subst_phi σ ρ φ v) ∗
          (∀ v, ▷ subst_phi σ ρ φ v → ▷ interp2 ρ v) ∗
          (∀ v, interp1 ρ v → interp2 ρ v)))%I.

  Definition interp_tmem l (interp1 interp2 : listVlC -n> D) : listVlC -n> D :=
    λne ρ v,
    (∃ d, ⌜ v @ l ↘ d ⌝ ∧ def_interp_tmem interp1 interp2 ρ d)%I.

  Definition interp_expr (φ : listVlC -n> D) : listVlC -n> tmC -n> iProp Σ :=
    λne ρ t, WP t {{ φ ρ }} %I.

  Definition interp_and (interp1 interp2 : listVlC -n> D): listVlC -n> D :=
    λne ρ v, (interp1 ρ v ∧ interp2 ρ v) %I.

  Definition interp_or (interp1 interp2 : listVlC -n> D) : listVlC -n> D :=
    λne ρ v, (interp1 ρ v ∨ interp2 ρ v) %I.

  Definition interp_later (interp : listVlC -n> D) : listVlC -n> D :=
    λne ρ v, (▷ (interp ρ v)) % I.

  Definition interp_nat : listVlC -n> D := λne ρ v, (∃ n, ⌜v = vnat n⌝) %I.

  Definition interp_top : listVlC -n> D := λne ρ v, True%I.

  Definition interp_bot : listVlC -n> D := λne ρ v, False%I.

  Definition interp_forall (interp1 interp2 : listVlC -n> D) : listVlC -n> D :=
    λne ρ v,
    (□ ∀ w, interp1 ρ w -∗ interp_expr interp2 (w :: ρ) (tapp (tv v) (tv w)))%I.

  Program Definition interp_mu (interp : listVlC -n> D) : listVlC -n> D :=
    λne ρ v, interp (v::ρ) v.

  Fixpoint split_path (p: path): vl * list label :=
    match p with
    | pv va => (va, [])
    | pself p l =>
      let '(v, ls) := split_path p in (v, ls ++ [l])
    end.

  Definition eval_split_path (p: path): list vl -> vl * (list label) :=
    λ ρ, let '(v, ls) := split_path p in (v.[to_subst ρ], ls).
  Arguments eval_split_path /.

  Program Definition interp_selA_final
          (l: label) (interpL interpU: listVlC -n> D) :
    listVlC -n> vlC -n> vlC -n> iProp Σ :=
    λne ρ w v,
    (∃ σ ϕ d,  ⌜w @ l ↘ d⌝ ∧ d ↗ σ , ϕ ∧
      interpU ρ v ∧ (interpL ρ v ∨ ▷ subst_phi σ ρ ϕ v))%I.

  Fixpoint interp_sel_rec (ls: list label) (interp_k: vlC -n> D): vlC -n> D :=
    λne Va v,
    match ls with
    | l :: ls => (∃ vb, ⌜Va @ l ↘ dvl vb⌝ ∧ ▷ interp_k vb v)%I
    | [] => interp_k Va v
    end.

  Definition interp_selA (p: path) (l: label) (L U : listVlC -n> D) :
    listVlC -n> D :=
    λne ρ v,
    let (Va, ls) := eval_split_path p ρ in
    interp_sel_rec ls (interp_selA_final l L U ρ) Va v.

  Definition interp_sel (p: path) (l: label) : listVlC -n> D :=
    interp_selA p l interp_bot interp_top.

  Fixpoint interp (T: ty) : listVlC -n> D :=
    match T with
    | TTMem l L U => interp_tmem l (interp L) (interp U)
    | TVMem l T' => interp_vmem l (interp T')
    | TAnd T1 T2 => interp_and (interp T1) (interp T2)
    | TOr T1 T2 => interp_or (interp T1) (interp T2)
    | TLater T => interp_later (interp T)
    | TNat => interp_nat
    | TTop => interp_top
    | TBot => interp_bot
    | TAll T1 T2 => interp_forall (interp T1) (interp T2)
    | TMu T => interp_mu (interp T)
    | TSel p l => interp_sel p l
    | TSelA p l L U => interp_selA p l (interp L) (interp U)
  end % I.

  Fixpoint def_interp (T: ty) (l : label): listVlC -n> dmC -n> iProp Σ :=
    λne ρ d,
    match T with
    | TTMem l' L U => ⌜ l = l' ⌝ ∧ def_interp_tmem (interp L) (interp U) ρ d
    | TVMem l' T' => ⌜ l = l' ⌝ ∧ def_interp_vmem (interp T') ρ d
    | _ => False
    end%I.

  Definition defs_interp_and
             (interp1 : listVlC -n> dmsC -n> iProp Σ)
             (interp2: label -> listVlC -n> dmC -n> iProp Σ)
    : listVlC -n> dmsC -n> iProp Σ :=
    λne ρ ds,
    match ds with
    | [] => False
    | d :: ds => interp1 ρ ds ∧ (interp2 (length ds)) ρ d
    end%I.

  Fixpoint defs_interp (T: ty) : listVlC -n> dmsC -n> iProp Σ :=
    match T with
    | TAnd T1 T2 => defs_interp_and (defs_interp T1) (def_interp T2)
    | TTop => λne ρ ds, True
    | _ => λne ρ ds, False
    end % I.

  Notation "⟦ T ⟧" := (interp T).

  Fixpoint interp_env (Γ : ctx) (vs : vls) : iProp Σ :=
    match Γ with
    | nil => ⌜vs = nil⌝
    | T :: Γ' =>
      match vs with
      | nil => False
      | v :: ρ => interp_env Γ' ρ ∗ ⟦ T ⟧ (v::ρ) v
      end
    end%I.

  Notation "⟦ Γ ⟧*" := (interp_env Γ).

  Global Instance interp_persistent T ρ v :
    Persistent (⟦ T ⟧ ρ v).
  Proof.
    revert v ρ; induction T => v ρ; simpl; try apply _.
    - destruct (split_path p) as [w ls].
      induction ls; simpl; apply _.
    - destruct (split_path p) as [w ls].
      induction ls; simpl; apply _.
  Qed.

  Global Instance def_interp_persistent T l ρ d :
    Persistent (def_interp T l ρ d).
  Proof.
    revert ρ d; induction T; simpl; try apply _.
  Qed.

  Global Instance defs_interp_persistent T ρ ds :
    Persistent (defs_interp T ρ ds).
  Proof.
    revert ds ρ; induction T; simpl; intros; try case_match; try apply _.
  Qed.

  Global Instance interp_env_persistent Γ ρ :
    Persistent (⟦ Γ ⟧* ρ) := _.
  Proof.
    revert ρ. induction Γ.
    - rewrite /Persistent /interp_env. eauto.
    - simpl. destruct ρ; rewrite /Persistent; eauto.
  Qed.

  (* Definitions for semantic (definition) (sub)typing *)
  Definition idtp Γ T l d : iProp Σ := (□∀ ρ, ⟦Γ⟧* ρ → def_interp T l ρ d)%I.
  Global Arguments idtp /.

  Definition idstp Γ T ds : iProp Σ :=
    (□∀ ρ, ⟦Γ⟧* ρ → defs_interp T ρ ds.|[to_subst ρ])%I.
  Global Arguments idstp /.

  Notation "⟦ T ⟧ₑ" := (interp_expr (interp T)).

  Definition ivtp Γ T v : iProp Σ := (□∀ ρ, ⟦Γ⟧* ρ → ⟦T⟧ ρ v)%I.
  Global Arguments ivtp /.

  Definition ietp Γ T e : iProp Σ := (□∀ ρ, ⟦Γ⟧* ρ → ⟦T⟧ₑ ρ (e.|[to_subst ρ]))%I.
  Global Arguments ietp /.

  (* Value subtyping. *)
  Definition ivstp Γ T1 T2: iProp Σ := (□∀ ρ v, ⟦Γ⟧* ρ → ⟦T1⟧ ρ v → ⟦T2⟧ ρ v)%I.
  Global Arguments ivstp /.

  (* (Expression) subtyping, strengthened to be equivalent to valye subtyping. *)
  Definition istp Γ T1 T2 : iProp Σ :=
    (ivstp Γ T1 T2 ∧ □∀ ρ e, ⟦Γ⟧* ρ → ⟦T1⟧ₑ ρ e → ⟦T2⟧ₑ ρ e)%I.
  Global Arguments istp /.

  Definition uvstp Γ T1 T2: iProp Σ :=
    (□∀ ρ v, ⟦Γ⟧*ρ -∗ ((*|={⊤}=>*) ⟦T1⟧ ρ v) → |={⊤}=> ⟦T2⟧ ρ v)%I.
  Global Arguments uvstp /.
End logrel.

Notation "⟦ T ⟧" := (interp T).
Notation "⟦ Γ ⟧*" := (interp_env Γ).
Notation "⟦ T ⟧ₑ" := (interp_expr (interp T)).

Notation "Γ ⊨ T1 <: T2" := (istp Γ T1 T2) (at level 74, T1, T2 at next level).
Notation "Γ ⊨ e : T" := (ietp Γ e T) (at level 74, e, T at next level).

Notation "Γ ⊨v T1 <: T2" := (ivstp Γ T1 T2) (at level 74, T1, T2 at next level).
Notation "Γ ⊨> T1 <: T2" := (uvstp Γ T1 T2) (at level 74, T1, T2 at next level).

Section SubTypingEquiv.
  Context `{HdotG: dotG Σ} (Γ: list ty).

  (** We prove that vstp and stp are equivalent, so that we can use them
      interchangeably; and in my previous proofs, proving uvstp was easier. *)

  Lemma istp2ivstp T1 T2: (Γ ⊨ T1 <: T2 → Γ ⊨v T1 <: T2)%I.
  Proof. by iIntros "/= [#? _]". Qed.

  Lemma ivstp2istp T1 T2: (Γ ⊨v T1 <: T2 → Γ ⊨ T1 <: T2)%I.
  Proof.
    iIntros "/= #Hstp". iFrame "Hstp".
    iIntros " !> * #Hg HeT1".
    iApply wp_fupd.
    iApply (wp_wand with " [-]"); try iApply "HeT1".
    iIntros "* HT1". by iApply "Hstp".
  Qed.

  Lemma istpEqIvstp T1 T2: (Γ ⊨ T1 <: T2) ≡ (Γ ⊨v T1 <: T2).
  Proof. iSplit; iIntros; by [iApply istp2ivstp| iApply ivstp2istp]. Qed.

  Lemma iStpUvstp T1 T2: (Γ ⊨ T1 <: T2 → Γ ⊨> T1 <: T2)%I.
  Proof.
    (* Inspired by the proof of wp_value_inv'! *)

    (* More manual.*)
    (* iIntros "/= #Hsub !> * #Hg *". *)
    (* iSpecialize ("Hsub" $! (of_val v) with "Hg"). *)
    (* rewrite !wp_unfold /wp_pre /=. iIntros. by iApply "Hsub". *)
    (* Restart. *)
    iIntros "/= [#Hsub1 #Hsub2] !> * #Hg * #?".
    by iApply "Hsub1".
    (* Or *)
    (* setoid_rewrite wp_unfold. *)
    (* by iApply ("Hsub2" $! _ (of_val v)). *)
  Qed.
End SubTypingEquiv.
