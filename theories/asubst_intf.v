(** Basic interfaces for D* languages (such as D<:, Dot).
We abstract over such languages to implement reusable infrastructure.

As we make significant use of Coq's ML-style module system, which is not
well-known, our comments explain our usage.
*)

From iris.program_logic Require Import language.
From D Require Import prelude.

(** * Parameters that each D* language must implement.
For our purposes here, a D* language is
- an Iris language,
- supporting substitution of values in values,
- supporting substitution of values in terms.
Substitution must be implemented using Autosubst.

This module type is used as an interface and not as a "mixin module" (so, not
[Include]d), so it only contains declarations: any definitions here would
have to be repeated in each language definition. *)
Module Type ValuesSig.
  Parameter dlang_lang : iris.program_logic.language.language.

  Definition vl : Type := val dlang_lang.

  Declare Instance inh_vl : Inhabited vl.
  Declare Instance ids_vl : Ids vl.
  Declare Instance inj_ids : Inj (=) (=@{vl}) ids.

  Declare Instance rename_vl : Rename vl.
  Declare Instance subst_vl : Subst vl.
  Declare Instance subst_lemmas_vl : SubstLemmas vl.

  (** The abbreviation [tm] is available in importing modules but not
  required in implementing modules. *)
  Notation tm := (expr dlang_lang).

  Declare Instance inh_tm : Inhabited tm.
  Declare Instance ids_tm : Ids tm.

  Declare Instance rename_tm : Rename tm.

  Declare Instance hsubst_tm : HSubst vl tm.
  Declare Instance hsubst_lemmas_tm : HSubstLemmas vl tm.

  Parameter hsubst_of_val : ∀ (v : vl) s, (of_val v).|[s] = of_val (v.[s]).
End ValuesSig.

(** * This module type contains minimal infrastructure for D*-languages.
It is a "mixin module": that is, it is [Include]d (indirectly) in each language
implementing [ValuesSig], yet functors can abstract over implementing modules.
Mixin module [Sorts] in [asubst_base] defines additional infrastructure.
*)
Module Type SortsSig (Import V : ValuesSig).
  Definition vls := list vl.
  Definition env := var → vl.

  Implicit Types (v : vl) (vs σ : vls) (ρ : env).

  Fixpoint to_subst σ : var → vl :=
    match σ with
    | [] => ids
    | v :: σ => v .: to_subst σ
    end.
  (* Tighter precedence than [>>], which has level 56. *)
  Notation "∞ σ" := (to_subst σ) (at level 50).

  Definition to_subst_nil : ∞ [] = ids := reflexivity _.

  Definition to_subst_cons v σ : ∞ (v :: σ) = v .: ∞ σ :=
    reflexivity _.
End SortsSig.

(** [VlSortsSig] mixes in [ValuesSig] and [SortsSig], and most infrastructure
is defined in functors abstracting over [VlSortsSig].
Module [VlSortsFullSig] in [asubst_base] defines additional infrastructure, but
to minimize compile-time dependencies, most such functors should abstract over
[VlSortsSig] and not [VlSortsFullSig].
*)
Module Type VlSortsSig := ValuesSig <+ SortsSig.

(** Autosubst extensions, and utilities useful when defining languages and implementing
[ValuesSig]. *)
Module ASubstLangDefUtils.
(* Not an instance because it should *not* be used automatically. *)
Definition inh_ids `{Inhabited X} : Ids X := λ _, inhabitant.
Instance list_ids {X} : Ids (list X) := inh_ids.

Section rename_instances.
  Context `{Ids X} `{Rename X}.
  Global Instance list_rename : Rename (list X) :=
    λ sb, map (rename sb).
  Definition list_rename_fold (sb : var → var) (xs : list X) :
    map (rename sb) xs = rename sb xs := eq_refl.
  (* Hint Rewrite @list_rename_fold : autosubst. *)
End rename_instances.

Section vls_subst_instances.
  Context `{Ids vl} `{Subst vl} `{SubstLemmas vl}.
  Set Default Proof Using "Type*".

  Global Instance vls_hsubst : HSubst vl (list vl) :=
    λ sb, map (subst sb).
  Global Arguments vls_hsubst /.

  Definition vls_subst_fold (sb : var → vl) (vs : list vl) :
    map (subst sb) vs = hsubst sb vs := eq_refl.
  Hint Rewrite @vls_subst_fold : autosubst.

  Global Instance hsubst_lemmas_vls : HSubstLemmas vl (list vl).
  Proof.
    split => // [|theta eta] vs; rewrite /hsubst;
      elim: vs => [//|v vs /= ->]; f_equal; autosubst.
  Qed.
End vls_subst_instances.

Section list_hsubst_instances.
  Context `{Ids vl} `{Subst vl}.
  Context `{Ids X} `{Rename X} `{HSubst vl X} {hsl : HSubstLemmas vl X}.
  Set Default Proof Using "Type*".

  Global Instance list_hsubst : HSubst vl (list X) :=
    λ sb, map (hsubst sb).
  Global Arguments list_hsubst /.

  Definition list_hsubst_fold sb (xs : list X) :
    map (hsubst sb) xs = hsubst sb xs := eq_refl.
  Hint Rewrite @list_hsubst_fold : autosubst.

  Global Instance hsubst_lemmas_list : HSubstLemmas vl (list X).
  Proof.
    split => // [|theta eta] vs; rewrite /hsubst;
      elim: vs => [//|v vs /= ->]; f_equal; autosubst.
  Qed.
  Section pair_instances.
    Context `{Inhabited A}.
    Implicit Types (x : X) (a : A).

    (** [Sort X → Sort (A, X)] *)
    Global Instance pair_ids : Ids (A * X) := λ n, (inhabitant, ids n).
    Global Instance pair_rename : Rename (A * X) :=
      λ sb, mapsnd (rename sb).
    Global Instance pair_hsubst : HSubst vl (A * X) :=
      λ sb, mapsnd (hsubst sb).
    Global Arguments pair_hsubst /.

    Definition pair_rename_fold sb (ax : A * X) :
      mapsnd (rename sb) ax = rename sb ax := eq_refl.
    Definition pair_hsubst_fold sb (ax : A * X) :
      mapsnd (hsubst sb) ax = hsubst sb ax := eq_refl.

    Global Instance hsubst_lemmas_pair : HSubstLemmas vl (A * X).
    Proof.
      split; intros; rewrite /hsubst /pair_hsubst /mapsnd /=;
        repeat case_match; simplify_eq; autosubst.
    Qed.
    Definition list_pair_rename_fold sb (axs : list (A * X)) :
      map (mapsnd (rename sb)) axs = rename sb axs := eq_refl.

    Lemma list_pair_swap_snd_rename r axs :
      map snd (rename r axs) = map (rename r) (map snd axs).
    Proof.
      rewrite !map_map. by elim: axs => [| [a x] axs /= ->].
    Qed.
  End pair_instances.
End list_hsubst_instances.

Definition list_pair_hsubst_fold {A} `{HSubst vl X} sb (xs : list (A * X)) :
  map (mapsnd (hsubst sb)) xs = hsubst sb xs := eq_refl.

Hint Rewrite @vls_subst_fold @list_hsubst_fold : autosubst.
(* The hints in the previous line are needed; for the next ones, that's less clear. *)
Hint Rewrite @pair_rename_fold @pair_hsubst_fold : autosubst.
Hint Rewrite @list_rename_fold @list_hsubst_fold : autosubst.
Hint Rewrite @list_pair_rename_fold @list_pair_hsubst_fold : autosubst.

(* Now type inference solves HSubst vl ? by infering HSubst vl ty infers unspecified asts to be [path]s. *)
(* Goal ∀ s x, x.|[s] = x. *)
(* Abort. *)
Hint Mode HSubst - + : typeclass_instances.
(* That Hint stops that. *)
(* Fail Goal ∀ s x, x.|[s] = x. *)
(* Goal ∀ s (x : ty), x.|[s] = x. Abort. *)
End ASubstLangDefUtils.
