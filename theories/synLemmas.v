(*
Lemmas on SynFuncs.v needed for proofs on the operational semantics.
To reduce compile times, unary_lr should not depend on this file.
This file should load as little Iris code as possible, to reduce compile times. But we must import operational.
 *)
Require Import Dot.tactics.
Require Export Dot.dotsyn.
Require Export Dot.operational.
(* Require Export Dot.synFuncs. *)

(* Require Import ssreflect. *)
(* From stdpp Require Import tactics. *)

(* Module SynLemmas (gnameMod: type). *)
(* Import gnameMod. *)
(* Module SynFuncsG := SynFuncs gnameMod. *)
(* Import SynFuncsG. *)

Bind Scope dms_scope with dms.
Open Scope dms_scope.
Notation " [@ ] " := dnil (format "[@ ]") : dms_scope.
Notation " [@ x ] " := (dcons x dnil) : dms_scope.
Notation " [@ x ; y ; .. ; z ] " := (dcons x (dcons y .. (dcons z dnil) ..))
                                    : dms_scope.

Lemma indexr_max {X} (T: X) i vs:
                       indexr i vs = Some T ->
                       i < length vs.
Proof.
  induction vs; first done; rewrite /lt in IHvs |- *; move => /= H.
  case_decide; subst; [ lia | eauto ].
Qed.
Hint Resolve indexr_max.

Lemma indexr_extend {X} vs n x (T: X):
                       indexr n vs = Some T ->
                       indexr n (x::vs) = Some T.
Proof.
  move => H /=; assert (n < length vs) by naive_solver; by case_decide; first lia.
Qed.

Lemma index_dms_extend l d ds dr:
  index_dms l ds = Some dr ->
  index_dms l (dcons d ds) = Some dr.
Proof. rewrite /index_dms; cbn -[indexr]. by apply indexr_extend. Qed.

Lemma index_dcons d ds: index_dms (dms_length ds) (dcons d ds) = Some d.
Proof. rewrite /index_dms /dms_length /=; by case_decide. Qed.
Hint Resolve index_dcons.

(** Rewrite v ↗ ds to vobj ds' ↗ ds. *)
Ltac simplOpen ds' :=
  lazymatch goal with
  | H: ?v ↗ ?ds |-_=>
    inversion H as (ds' & -> & _)
  end.

(** Determinacy of obj_opens_to. *)
Lemma openDet v ds1 ds2: v ↗ ds1 -> v ↗ ds2 -> ds1 = ds2.
Proof.
  rewrite /obj_opens_to; intros; ev; by optFuncs_det.
Qed.
Ltac openDet :=
  lazymatch goal with
  | H1: ?v ↗ ?ds1, H2: ?v ↗ ?ds2 |- _=>
    assert (ds1 = ds2) as <- by (eapply openDet; eassumption)
  end.

Arguments dms_proj_val /.

Fixpoint idsσ1 i (ρ: list vl): vls :=
  match ρ with
  | [] => vnil
  | _ :: ρ1 => vcons (var_vl i) (idsσ1 (S i) ρ1)
  end.
(* Goal idsσ1 ρ !! i. *)

Definition idv := vabs (tv (var_vl 0)).
Definition fst := vabs (tv (vabs (tv (var_vl 1)))).
Definition snd := vabs (tv (vabs (tv (var_vl 0)))).
(* Eval compute in idsσ [fst; idv]. *)

Definition testProp ρ := ρ = vls_to_list (idsσ ρ).[to_subst ρ].

Goal testProp [idv]. reflexivity. Qed.
Goal testProp [idv; idv]. reflexivity. Qed.
Goal testProp [idv; fst]. reflexivity. Qed.
Goal testProp [fst; idv]. reflexivity. Qed.
Goal testProp [fst; snd; idv]. reflexivity. Qed.
Goal testProp [fst; snd; fst; snd; idv; snd; idv; fst; idv]. reflexivity. Qed.

(* Arguments to_subst /. *)
Lemma idsσ_is_id ρ: ρ = vls_to_list (idsσ ρ).[to_subst ρ].
Proof.
  induction ρ.
  by simpl.
  simpl.
  asimpl.
  f_equal.
  rewrite IHρ.
  f_equal.
  rewrite <- IHρ.
Admitted.

  (* We're left with:
     (idsσ ρ).[to_subst ρ] = (idsσ ρ).[(+1) >>> to_subst (a :: ρ)]
     Using f_equal and enough simplifications shows us that the two substitutions agree only for the first [length ρ] elements.
     But that's enough for the theorem to be true!
   *)
(*   (* clear IHρ. *) *)

(*   unfold lift. *)
(*   unfold funcomp. *)
(*   simpl. *)
(*   unfold to_subst. *)
(*   simpl. *)
(*   (* (* This turns the goal into something false?! *) *) *)
(*   (* f_equal. *) *)
(*   unfold lift. *)
(*   unfold funcomp. *)
(*   simpl. *)
(*   unfold to_subst. *)
(*   simpl. *)
(*   Require Import Dot.axioms. *)
(*   fext; intros. *)
(* fold (to_subst ρ). *)

(*   (* Lemma aux a ρ: (idsσ ρ).[to_subst ρ] = (ren_vls S (idsσ (vls_to_list (idsσ ρ).[to_subst ρ]))).[to_subst (a :: vls_to_list (idsσ ρ).[to_subst ρ])]. *) *)
(*   Lemma aux a ρ: (idsσ ρ).[to_subst ρ] = (idsσ (vls_to_list (idsσ ρ).[to_subst ρ])).[(+1) >>> to_subst (a :: vls_to_list (idsσ ρ).[to_subst ρ])] *)
(*   Proof. *)
(*     asimpl. *)


(*   asimpl. *)
(*   simpl. *)
(*   f_equal. *)
(*   fold idsσ. *)
(*   unfold to_subst. *)
(*   fold (to_subst ρ). *)
(*   unfold lookup. *)
(*   unfold list_lookup. *)
(*   simpl. *)
(*   Locate "!!". *)

  (* cbn. *)
  (* asimpl. *)
  (* simpl. *)
  (* f_equal. *)
  (* f_equal. *)
  (* cbn. *)
  (* asimpl. *)
  (* cbn. *)
  (* unfold *)

(* End SynLemmas. *)
