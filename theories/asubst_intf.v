(* Basic interfaces. *)

From iris.program_logic Require Import language ectx_language ectxi_language.
From D Require Import prelude.

Module Type Values.
  Parameter dlang_ectxi_lang : ectxiLanguage.
  Parameter dlang_ectx_lang : ectxLanguage.
  Parameter dlang_lang : language.
  Definition vl : Type := val dlang_ectxi_lang.
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
End SortsIntf.
