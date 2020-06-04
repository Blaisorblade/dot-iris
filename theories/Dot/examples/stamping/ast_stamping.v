(** Define "stamping" (what we used to call translation) in a purely syntactic
    way, without involving Iris. *)
From stdpp Require Import gmap.
From D Require Import tactics.
From D.Dot Require Import syn syn_lemmas type_extraction_syn core_stamping_defs
  skeleton unstampedness_binding lr_syn_aux.

Set Implicit Arguments.

Implicit Types
         (T: ty) (v: vl) (e: tm) (p: path) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx) (g: stys) (n: nat).

Lemma unstamped_stamped_var n b g x :
  is_unstamped_vl n b (var_vl x) → is_stamped_vl n g (var_vl x).
Proof. inversion_clear 1; auto. Qed.

(** Unstamped types are already stamped, because they can't contain type
    definitions to stamp. *)
Lemma unstamped_stamped_path p g n:
  is_unstamped_path' n p → is_stamped_path n g p.
Proof.
  intros Hus; induction p; repeat with_is_unstamped ltac:(fun H => nosplit inverse H; clear H);
    naive_solver eauto using unstamped_stamped_var.
Qed.

Lemma unstamped_stamped_type T g n b:
  is_unstamped_ty n b T →
  is_stamped_ty n g T.
Proof.
  move: n. induction T => n Hus; inverse Hus; constructor;
    try by [|eapply IHT || eapply IHT1 || eapply IHT2; auto 2; auto with fv];
    exact: unstamped_stamped_path.
Qed.
