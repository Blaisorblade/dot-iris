(** * Semantic lemmas for double-delay subtyping. *)
From iris.proofmode Require Import proofmode.

From D Require Import iris_prelude swap_later_impl.
From D.Dot Require Import rules path_repl unary_lr dsub_lr defs_lr binding_lr sub_lr.

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : env) (l : label).

Section defs.
  Context {Σ}.

  Definition istpi `{!dlangG Σ} Γ T1 T2 i j := sstpi i j V⟦Γ⟧* V⟦T1⟧ V⟦T2⟧.
End defs.

Notation "Γ ⊨ T1 , i <: T2 , j" := (istpi Γ T1 T2 i j) (at level 74, T1, T2, i, j at next level).

Section judgment_lemmas.
  Context `{!dlangG Σ}.

  (** ** Show this typing judgment is equivalent to the more direct definition. *)
  Lemma istpi_eq Γ T1 i T2 j :
    Γ ⊨ T1, i <: T2, j ⊣⊢
    <PB> ∀ ρ v, G⟦Γ⟧ ρ → ▷^i V⟦T1⟧ anil ρ v → ▷^j V⟦T2⟧ anil ρ v.
  Proof. reflexivity. Qed.
End judgment_lemmas.
