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
  Class Sort (s : Type)
    {inh_s : Inhabited s}
    {ids_s : Ids s} {ren_s : Rename s} {hsubst_vl_s : HSubst vl s}
    {hsubst_lemmas_vl_s : HSubstLemmas vl s} := {}.

  Instance sort_tm : Sort tm := {}.

  Definition eq_n_s (s1 s2 : var → vl) n := ∀ x, x < n → s1 x = s2 x.
  Global Arguments eq_n_s /.

  Definition nclosed_vl (v : vl) n :=
    ∀ s1 s2, eq_n_s s1 s2 n → v.[s1] = v.[s2].

  Definition nclosed `{HSubst vl X} (x : X) n :=
    ∀ s1 s2, eq_n_s s1 s2 n → x.|[s1] = x.|[s2].

  Definition to_subst (ρ : vls) : var → vl := foldr (λ v s, v .: s) ids ρ.
  Parameter to_subst_nil : to_subst [] = ids.

  Parameter to_subst_cons : ∀ v ρ, to_subst (v :: ρ) = v .: to_subst ρ.

  Parameter to_subst_weaken : ∀ ρ1 ρ2 ρ3,
    upn (length ρ1) (ren (+length ρ2)) >> to_subst (ρ1 ++ ρ2 ++ ρ3) =
    to_subst (ρ1 ++ ρ3).

  Parameter to_subst_up : ∀ ρ1 ρ2 v,
    upn (length ρ1) (v.[ren (+length ρ2)] .: ids) >> to_subst (ρ1 ++ ρ2) =
    to_subst (ρ1 ++ v :: ρ2).

  Definition nclosed_sub n m s :=
    ∀ i, i < n → nclosed_vl (s i) m.
  Parameter compose_sub_closed : ∀ s s1 s2 i j,
    nclosed_sub i j s → eq_n_s s1 s2 j → eq_n_s (s >> s1) (s >> s2) i.

  Parameter nclosed_sub_app_vl : ∀ v s i j,
    nclosed_sub i j s →
    nclosed_vl v i → nclosed_vl v.[s] j.

  Parameter nclosed_sub_app : ∀ `{Ids X} `{HSubst vl X} `{!HSubstLemmas vl X} (x : X) s i j,
    nclosed_sub i j s →
    nclosed x i → nclosed x.|[s] j.
End SortsSig.

Module Type VlSortsSig := ValuesSig <+ SortsSig.
