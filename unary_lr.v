Require Import tactics.

Require Import dotsyn.

From iris Require Import base_logic.lib.saved_prop.
(* From iris Require Import base_logic.base_logic. *)

From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.algebra Require Import list.
From iris.base_logic Require Import invariants.

Definition logN : namespace := nroot .@ "logN".

Section Sec.
  Context `{savedPredG Σ vl}.
  (* Check savedPredG0. *)
  (* Print savedPredG. *)
  (* Print savedAnythingG. *)

  Definition SP γ ϕ := saved_pred_own γ ϕ.
  Notation "γ ⤇ ϕ" := (SP γ ϕ) (at level 200).

  (* Check SP. *)
  (* Check (SP: gname -> DotPred -> iProp Σ). *)
  (* Notation "'DotPred'" := (vr -> iProp Σ) (at level 100). *)
  (* Definition vr_prop := vr -> iProp Σ. *)
  (* Arguments vr_prop /. *)
  (* Print solve_decision. *)
  (* Instance id_dec_eq (i i' : id) : Decision (i = i'). *)
  (* Proof. solve_decision. Defined. *)
  (* Instance gname_dec_eq (i i' : gname) : Decision (i = i'). *)
  (* Proof. solve_decision. Defined. *)
  
  (* Fixpoint vr_dec_eq (v v' : vr) : Decision (v = v') *)
  (*   with ty_dec_eq (t t' : ty) : Decision (t = t') *)
  (*   with tm_dec_eq (t t' : tm) : Decision (t = t') *)
  (*   with dm_dec_eq (t t' : dm) : Decision (t = t') *)
  (*   with dms_dec_eq (t t' : dms) : Decision (t = t'). *)
  (* Proof. *)
  (*   all: unfold Decision in *. *)
  (*   all: decide equality; try apply id_dec_eq; try apply gname_dec_eq. *)
  (* Defined. *)
  (* (*   decide equality; try typeclasses eauto. try apply id_dec_eq. *) *)
  (* (*   decide equality. *) *)
  (* (* Print solve_decision. *) *)
  (* (*   solve *) *)
  (* (*   all: solve_decision. Defined. *) *)


  (* Canonical Structure vrC3 := discreteC vr. *)
  Canonical Structure vlC := leibnizC vl.
  Canonical Structure tmC := leibnizC tm.
  (* Canonical Structure vrC := discreteC vr. *)
  Notation D := (vlC -n> iProp Σ).
  Implicit Types τi : D.

  Program Definition expr_sem (A: D) (e: tm) : iProp Σ :=
    (False % I).
  Fixpoint interp (T: ty) : D := λne v,
    match T with
    | TAnd T1 T2 => interp T1 v ∧ interp T2 v
    | TOr T1 T2 => interp T1 v ∨ interp T2 v
    | TTMem l L U => False
    | _ => False
    end % I.
  
  (* V􏰃p.A􏰄ρ= 􏰋v 􏰍 ∃φ.ρ(p).A↘φ∧▷(v∈φ)􏰌 *)
  
  (* Set Implicit Arguments. *)
  (* Definition indexL {X: Type} := @dot_storeless_tidy.index X. *)
  (* Check indexL. *)
  Definition interp_mem1
      (interp : ty -> D) (τi : D) l L U : D := λne w,
                                        (∃ ds, w ≡ (tv (vobj ds)) ∧
                                              ∃ TX g, indexL l (dms_to_list (subst_dms ds ds)) ≡ Some (dty TX g) /\ False)%I.
    (* (□ (∃ v, ⌜w = FoldV v⌝ ∧ ▷ interp (τi :: Δ) v))%I. *)

  (* Global Instance interp_rec1_contractive *)
  (*   (interp : listC D -n> D) (Δ : listC D) : Contractive (interp_rec1 interp Δ). *)
  (* Proof. by solve_contractive. Qed. *)

  (* Lemma fixpoint_interp_rec1_eq (interp : listC D -n> D) Δ x : *)
  (*   fixpoint (interp_rec1 interp Δ) x ≡ interp_rec1 interp Δ (fixpoint (interp_rec1 interp Δ)) x. *)
  (* Proof. exact: (fixpoint_unfold (interp_rec1 interp Δ) x). Qed. *)

  (* Program Definition interp_rec (interp : listC D -n> D) : listC D -n> D := λne Δ, *)
  (*   fixpoint (interp_rec1 interp Δ). *)
  (* Next Obligation. *)
  (*   intros interp n Δ1 Δ2 HΔ; apply fixpoint_ne => τi w. solve_proper. *)
  (* Qed. *)
  