(* Base Coq settings (ssreflect and setup): *)
From iris.algebra Require Export base.
From Autosubst Require Export Autosubst.

Definition stamp := positive.

(* Now type inference solves HSubst vl ? by infering HSubst vl ty infers unspecified asts to be [path]s. *)
(* Goal ∀ s x, x.|[s] = x. *)
(* Abort. *)
Hint Mode HSubst - + : typeclass_instances.
(* That Hint stops that. *)
(* Fail Goal ∀ s x, x.|[s] = x. *)
(* Goal ∀ s (x: ty) , x.|[s] = x. Abort. *)

Section Autosubst_Lemmas.
  Context {term : Type} {Ids_term : Ids term}
          {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}.

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
