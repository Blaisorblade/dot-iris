Require Import Dot.dotsyn.

From iris Require Import base_logic.lib.saved_prop.
(* From iris Require Import base_logic.base_logic. *)

From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.algebra Require Import list.
From iris.base_logic Require Import invariants.

Definition logN : namespace := nroot .@ "logN".

Fixpoint dms_to_list (ds: dms) : list dm :=
  match ds with
  | dnil => []
  | dcons d ds => d :: dms_to_list ds
  end.

Definition index_dms (i: label) (ds: dms): option dm :=
  dms_to_list ds !! i.

Section Sec.
  Context `{savedPredG Σ vl}.
  (* Check savedPredG0. *)
  (* Print savedPredG. *)
  (* Print savedAnythingG. *)

  Definition SP γ ϕ := saved_pred_own γ ϕ.
  Notation "g ⤇ p" := (SP g p) (at level 20).

  Definition object_proj_semtype v l φ : iProp Σ :=
    (∃ γ ds, ⌜ v = vobj ds ∧ index_dms l ds = Some(dtysem γ) ⌝ ∗ γ ⤇ φ)%I.

  Definition object_proj_val v l w : iProp Σ :=
    (∃ ds, ⌜ v = vobj ds ∧ index_dms l ds = Some(dvl w) ⌝)%I.

  Notation "v ; l ↘ φ" := (object_proj_semtype v l φ)%I (at level 20).
  Notation "v ;; l ↘ w" := (object_proj_val v l w)%I (at level 20).

  Canonical Structure vlC := leibnizC vl.
  Canonical Structure tmC := leibnizC tm.
  Notation D := (vlC -n> iProp Σ).
  Implicit Types τi : D.

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
    (∃ φ, (v;l ↘ φ) ∗ (inclusion (interp1 ρ) φ) ∗ inclusion φ (interp2 ρ) )%I.
  Solve Obligations with solve_proper.

  Program Definition interp_later (interp : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
         (▷ (interp ρ v)) % I.
  Solve Obligations with solve_proper.

  Program Definition interp_forall (interp1 interp2 : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
    (▷ ∀ v', interp1 ρ v' -∗ expr_sem (interp2 (v :: ρ)) (tapp (tv v) (tv v'))) % I.
  Solve Obligations with solve_proper.

  Program Definition interp_val_mem l (interp : listC vlC -n> D) : listC vlC -n> D := λne ρ v,
    (∃ vmem, v;;l ↘ vmem ∧ ▷ interp ρ vmem) % I.
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

  Notation "⟦ T ⟧" := (interp T).

  (* use foldr? *)
  Fixpoint interp_env (Γ : list ty): list vl -> iProp Σ :=
    match Γ with
    | nil => (fun l => (⌜ l = nil ⌝) % I)
    | T::Γ' => (fun l => match l with
                         | nil => False
                         | v::ρ => (interp_env Γ') ρ ∗ ⟦ T ⟧ (v::ρ) v
                         end
               )%I
    end.
  Notation "⟦ Γ ⟧*" := (interp_env Γ).

End Sec.
