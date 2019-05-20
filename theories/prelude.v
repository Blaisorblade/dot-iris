(* Base Coq settings (ssreflect and setup): *)
From iris.algebra Require Export base.
From Autosubst Require Export Autosubst.

Definition stamp := positive.
(* Not an instance because it should *not* be used automatically. *)
Definition inh_ids `{Inhabited X}: Ids X := λ _, inhabitant.
Instance list_ids {X}: Ids (list X) := inh_ids.

Section rename_instances.
  Context `{Ids X} `{Rename X}.
  Global Instance list_rename: Rename (list X) :=
    λ sb, map (rename sb).
  Definition list_rename_fold (sb : var → var) (xs : list X) : map (rename sb) xs = rename sb xs := eq_refl.
  (* Hint Rewrite @list_rename_fold : autosubst. *)
End rename_instances.

Section subst_instances.
  Context `{Ids vl} `{Subst vl} `{SubstLemmas vl}.
  Context `{Ids X} `{Rename X} `{HSubst vl X} {hsl: HSubstLemmas vl X}.

  Global Instance vls_hsubst: HSubst vl (list vl) :=
    λ sb, map (subst sb).
  Global Instance list_hsubst: HSubst vl (list X) :=
    λ sb, map (hsubst sb).
  Global Arguments list_hsubst /.
  Global Arguments vls_hsubst /.

  Definition vls_subst_fold (sb : var → vl) (vs : list vl) : map (subst sb) vs = hsubst sb vs := eq_refl.
  Definition list_hsubst_fold sb (xs : list X) : map (hsubst sb) xs = hsubst sb xs := eq_refl.

  Hint Rewrite @vls_subst_fold @list_hsubst_fold : autosubst.

  Global Instance hsubst_lemmas_vls: HSubstLemmas vl (list vl).
  Proof.
    split; trivial; intros; rewrite /hsubst;
      induction s; asimpl; by f_equal.
  Qed.
  Global Instance hsubst_lemmas_list: HSubstLemmas vl (list X).
  Proof.
    split; trivial; intros; rewrite /hsubst;
      induction s; asimpl; by f_equal.
  Qed.
  Section pair_instances.
    Context `{Inhabited A}.
    Implicit Types (x: X) (a: A).

    (** [Sort X → Sort (A, X)] *)
    Definition mapsnd `(f: B → C) : A * B → A * C := λ '(a, b), (a, f b).
    Global Instance pair_ids: Ids (A * X) := λ n, (inhabitant, ids n).
    Global Instance pair_rename: Rename (A * X) :=
      λ sb, mapsnd (rename sb).
    Global Instance pair_hsubst: HSubst vl (A * X) :=
      λ sb, mapsnd (hsubst sb).
    Global Arguments pair_hsubst /.

    Definition pair_rename_fold sb (ax: A * X): mapsnd (rename sb) ax = rename sb ax := eq_refl.
    Definition pair_hsubst_fold sb (ax: A * X): mapsnd (hsubst sb) ax = hsubst sb ax := eq_refl.

    Global Instance hsubst_lemmas_pair: HSubstLemmas vl (A * X).
    Proof.
      split; intros; rewrite /hsubst /pair_hsubst /mapsnd /=;
        repeat case_match; simplify_eq; asimpl; by [].
    Qed.
    Definition list_pair_rename_fold sb (axs: list (A * X)): map (mapsnd (rename sb)) axs = rename sb axs := eq_refl.

    Lemma list_pair_swap_snd_rename r axs: map snd (rename r axs) = map (rename r) (map snd axs).
    Proof.
      rewrite !map_map; elim: axs => [//| [a x] axs IHaxs /=]. by f_equal.
    Qed.
  End pair_instances.
End subst_instances.
Definition list_pair_hsubst_fold {A} `{HSubst vl X} sb (xs: list (A * X)): map (mapsnd (hsubst sb)) xs = hsubst sb xs := eq_refl.

Global Hint Rewrite @vls_subst_fold @list_hsubst_fold : autosubst.
(* The hints in the previous line are needed; for the next ones, that's less clear. *)
Global Hint Rewrite @pair_rename_fold @pair_hsubst_fold : autosubst.
Global Hint Rewrite @list_rename_fold @list_hsubst_fold : autosubst.
Global Hint Rewrite @list_pair_rename_fold @list_pair_hsubst_fold : autosubst.

(* Now type inference solves HSubst vl ? by infering HSubst vl ty infers unspecified asts to be [path]s. *)
(* Goal ∀ s x, x.|[s] = x. *)
(* Abort. *)
Hint Mode HSubst - + : typeclass_instances.
(* That Hint stops that. *)
(* Fail Goal ∀ s x, x.|[s] = x. *)
(* Goal ∀ s (x: ty) , x.|[s] = x. Abort. *)

Section Autosubst_Lemmas.
  Context {term : Type} {ids_term : Ids term}
          {rename_term : Rename term} {subst_term : Subst term}
          {subst_lemmas_term : SubstLemmas term}.

  Lemma iter_up (m x : nat) (f : var → term) :
    upn m f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
  Proof.
    revert x; induction m as [|m IH]=> -[|x];
      case_match => //; asimpl; rewrite // IH; case_match; asimpl.
    (* lia fails here, because some inequalities are used
       in other hypotheses. *)
    all: by [|omega].
  Qed.

  Lemma upn_comp n m f: upn n (upn m f) = upn (n + m) f.
  Proof.
    revert m; induction n => m; first done.
    rewrite -fold_upn_up fold_up_upn; simpl.
    replace (S (n + m)) with (n + S m) by lia; auto.
  Qed.

End Autosubst_Lemmas.

Inductive ForallT {A : Type} (P : A → Type) : list A → Type :=
    Forall_nil : ForallT P [] | Forall_cons : ∀ (x : A) (l : list A), P x → ForallT P l → ForallT P (x :: l).
Hint Constructors ForallT.

(** To be able to reuse lemmas on Forall, show that ForallT is equivalent to Forall for predicates in Prop.
    The proof is a bit subtler than you'd think because it can't look into Prop
    to produce proof-relevant part of the result (and that's why I can't inversion until very late.
 *)
Lemma ForallT_Forall {X} (P: X → Prop) xs: (ForallT P xs -> Forall P xs) * (Forall P xs -> ForallT P xs).
Proof.
  split; (elim: xs => [|x xs IHxs] H; constructor; [|apply IHxs]; by inversion H).
Qed.
