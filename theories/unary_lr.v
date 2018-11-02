Require Import Dot.dotsyn.

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
  Notation "g ⤇ p" := (SP g p) (at level 20).

  Canonical Structure vlC := leibnizC vl.
  Canonical Structure tmC := leibnizC tm.
  Notation D := (vlC -n> iProp Σ).
  Implicit Types τi : D.

  Fixpoint dms_to_list (ds: dms) : list dm :=
    match ds with
    | dnil => []
    | dcons d ds => d :: dms_to_list ds
    end.

  Definition index_dms (i: label) (ds: dms): option dm :=
    dms_to_list ds !! i.

  Program Definition expr_sem (A: D) (e: tm) : iProp Σ :=
    (False % I).

  Program Definition interp_and (interp1 interp2 : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
    (interp1 ρ v  ∧  interp2 ρ v) % I.
  Solve Obligations with solve_proper.


  Program Definition interp_or (interp1 interp2 : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
    (interp1 ρ v  ∨  interp2 ρ v) % I.
  Solve Obligations with solve_proper.

  Notation inclusion P Q := (∀ v, P v -∗ Q v)%I.

  Program Definition interp_mem (l: label) (interp1 interp2 : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
                                                                                                    (∃ γ ϕ ds, ⌜ v = vobj ds ∧ index_dms l ds = Some(dtysem γ) ⌝ ∗ γ ⤇ ϕ ∗ (inclusion (interp1 ρ) ϕ) ∗ inclusion ϕ (interp2 ρ) )%I.
  Solve Obligations with solve_proper.

  Program Definition interp_later (interp : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
         (▷ (interp ρ v)) % I.
  Solve Obligations with solve_proper.

  Program Definition interp_forall (interp1 interp2 : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
    (▷ ∀ v', interp1 ρ v' -∗ expr_sem (interp2 (v :: ρ)) (tapp (tv v) (tv v'))) % I.
  Solve Obligations with solve_proper.

  Program Definition interp_val_mem l (interp : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
    (∃ ds vmem, ⌜ v = vobj ds ∧ index_dms l ds = Some(dvl vmem) ⌝ ∧ ▷ interp ρ vmem) % I.
  Solve Obligations with solve_proper.

  Program Definition interp_bind (interp : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
    (interp (v::ρ) v) % I.
  Solve Obligations with solve_proper.
  
  Program Definition interp_true : listC vlC -n> D := λne ρ v, True % I.
  Program Definition interp_false : listC vlC -n> D := λne ρ v, False % I.

  Fixpoint interp (T: ty) : listC vlC -n> D := 
    match T with
    | TAnd T1 T2 => interp_and (interp T1) (interp T2)
    | TOr T1 T2 => interp_or (interp T1) (interp T2)
    | TTMem l L U => interp_mem l (interp L) (interp U)
    | TLater T => interp_later (interp T)
    | TTop => interp_true
    | TBot => interp_false
    | TAll T1 T2 => interp_forall (interp T1) (interp T2)
    | TBind T => interp_bind (interp T)
    | TSel value (* l *) => interp_true (* ∃ γ ϕ ds, ⌜ v = vobj ds ∧ index_dms l ds = Some(dtysem γ) ⌝ ∧ (SP γ ϕ) *)
    | TSelA _ _ _ => interp_false
    | TVMem l T' => interp_val_mem l (interp T')
  end % I.


  (* V􏰃p.A􏰄ρ= 􏰋v 􏰍 ∃φ.ρ(p).A↘φ∧▷(v∈φ)􏰌 *)
  
  (* Set Implicit Arguments. *)
  (* Definition indexL {X: Type} := @dot_storeless_tidy.index X. *)
  (* Check indexL. *)
  (* Definition interp_mem1 *)
  (*     (interp : ty -> D) (τi : D) l L U : D := λne w, *)
  (*                                       (∃ ds, w ≡ (tv (vobj ds)) ∧ *)
  (*                                             ∃ TX g, index_dms l (subst_dms ds ds) ≡ Some (dtysem g) /\ False)%I. *)
  (*   (□ (∃ v, ⌜w = FoldV v⌝ ∧ ▷ interp (τi :: Δ) v))%I. *)

  (* Global Instance interp_rec1_contractive *)
  (*   (interp : listC vlC -n> D) (Δ : listC vlC) : Contractive (interp_rec1 interp Δ). *)
  (* Proof. by solve_contractive. Qed. *)

  (* Lemma fixpoint_interp_rec1_eq (interp : listC vlC -n> D) Δ x : *)
  (*   fixpoint (interp_rec1 interp Δ) x ≡ interp_rec1 interp Δ (fixpoint (interp_rec1 interp Δ)) x. *)
  (* Proof. exact: (fixpoint_unfold (interp_rec1 interp Δ) x). Qed. *)

  (* Program Definition interp_rec (interp : listC vlC -n> D) : listC vlC -n> D := λne Δ, *)
  (*   fixpoint (interp_rec1 interp Δ). *)
  (* Next Obligation. *)
  (*   intros interp n Δ1 Δ2 HΔ; apply fixpoint_ne => τi w. solve_proper. *)
  (* Qed. *)
End Sec.
