(* Basic interfaces. *)

(* From iris.program_logic Require Import ectx_language ectxi_language. *)
From iris.program_logic Require Import language.
From D Require Import prelude.

Module Type Values.
  (* XXX do we need them? *)
  (* Parameter dlang_ectxi_lang : ectxiLanguage.
  Parameter dlang_ectx_lang : ectxLanguage. *)
  Parameter dlang_lang : language.
  Definition vl : Type := val dlang_lang.
  Definition vls := list vl.
  Declare Instance inh_vl : Inhabited vl.
  Declare Instance ids_vl : Ids vl.
  Declare Instance inj_ids : Inj (=) (=@{vl}) ids.

  Declare Instance rename_vl : Rename vl.
  Declare Instance subst_vl : Subst vl.
  Declare Instance subst_lemmas_vl : SubstLemmas vl.
End Values.

Module Type SortsIntf (values: Values).
  Import values.

  Class Sort (s : Type)
    {inh_s : Inhabited s}
    {ids_s : Ids s} {ren_s : Rename s} {hsubst_vl_s : HSubst vl s}
    {hsubst_lemmas_vl_s : HSubstLemmas vl s} := {}.

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
End SortsIntf.
