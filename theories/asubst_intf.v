(** Basic interfaces for Iris languages with Autosubst substitution operations. *)

From iris.program_logic Require Import language.
From D Require Import prelude.

Module Type ValuesSig.
  Parameter dlang_lang : language.
  Definition vl : Type := val dlang_lang.
  Definition vls := list vl.
  Declare Instance inh_vl : Inhabited vl.
  Declare Instance ids_vl : Ids vl.
  Declare Instance inj_ids : Inj (=) (=@{vl}) ids.

  Declare Instance rename_vl : Rename vl.
  Declare Instance subst_vl : Subst vl.
  Declare Instance subst_lemmas_vl : SubstLemmas vl.

  Notation tm := (expr dlang_lang).
  Declare Instance inh_tm : Inhabited tm.
  Declare Instance ids_tm : Ids tm.

  Declare Instance rename_tm : Rename tm.

  Declare Instance hsubst_tm : HSubst vl tm.
  Declare Instance hsubst_lemmas_tm : HSubstLemmas vl tm.

  Parameter hsubst_of_val : ∀ (v : vl) s, (of_val v).|[s] = of_val (v.[s]).
End ValuesSig.

Module Type SortsSig (Import V : ValuesSig).
  Fixpoint to_subst σ : var → vl :=
    match σ with
    | [] => ids
    | v :: σ => v .: to_subst σ
    end.
  (* Tighter precedence than [>>], which has level 56. *)
  Notation "∞ σ" := (to_subst σ) (at level 50).

  Definition to_subst_nil : to_subst [] = ids := reflexivity _.

  Definition to_subst_cons v σ : to_subst (v :: σ) = v .: to_subst σ :=
    reflexivity _.
End SortsSig.

Module Type VlSortsSig := ValuesSig <+ SortsSig.
