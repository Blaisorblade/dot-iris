Require Import Dot.tactics.
Require Import Dot.unary_lr.
Require Import Dot.synLemmas.

Section Sec.
  Context `{HdotG: dotG Σ}.

  Definition subst_sigma (σ: vls) (ρ: list vl) := vls_to_list (σ.[to_subst ρ]).
  Definition push_var (σ: vls): vls := vlcons (var_vl 0) σ.[(+1) >>> var_vl].

  (** Translation between syntactic and semantic values, defined as a relation.
   * First, we have the interesting case, the one for type members.
   *)
  Definition t_dty_syn2sem (t_ty: vls -> ty -> ty -> iProp Σ) (T1: ty) (σ σ2: vls) γ2: iProp Σ :=
    (∃ φ T2, γ2 ⤇ φ ∧ t_ty σ T1 T2 ∧
             ∀ ρ v,
               (* We should demand that ρ is closed, and we should check that FV (T) ⊂ dom σ *)
               uinterp T2 (subst_sigma σ ρ, v) ≡ φ (subst_sigma σ2 ρ, v))%I.

  (** Lift [t_dty_syn2sem] throughout the syntax of terms and types, checking tht otherwise the terms are equal.
   *)
  Fixpoint t_tm (σ: vls) (t1 t2: tm): iProp Σ :=
    match (t1, t2) with
    | (tv v1, tv v2) => t_vl σ v1 v2
    | (tapp t11 t12, tapp t21 t22) =>
      t_tm σ t11 t21 ∧ t_tm σ t12 t22
    | (tproj t1 l1, tproj t2 l2) =>
      t_tm σ t1 t2 ∧ l1 ≡ l2
    | _ => False
    end%I
  with
  t_vl (σ: vls) (v1 v2: vl): iProp Σ :=
    match (v1, v2) with
    | (var_vl i1, var_vl i2) => i1 ≡ i2
    | (vabs t1, vabs t2) => t_tm (push_var σ) t1 t2
    | (vobj ds1, vobj ds2) => t_dms (push_var σ) ds1 ds2
    | _ => False
    end%I
  with
  t_dms (σ: vls) (ds1 ds2: dms): iProp Σ :=
    match (ds1, ds2) with
    | (dnil, dnil) => True
    | (dcons d1 ds1, dcons d2 ds2) =>
      t_dm σ d1 d2 ∧ t_dms σ ds1 ds2
    | _ => False
    end%I
  with
  t_dm (σ: vls) (d1 d2: dm): iProp Σ :=
    match (d1, d2) with
    | (dtysyn T1, dtysem σ2 γ2) =>
      (* Only nontrivial case *)
      t_dty_syn2sem t_ty T1 σ σ2 γ2
    | (dvl v1, dvl v2) => t_vl σ v1 v2
    | _ => False
    end%I
  with
  t_path (σ: vls) (p1 p2: path): iProp Σ :=
    match (p1, p2) with
    | (pv v1, pv v2) => t_vl σ v1 v2
    | (pself p1 l1, pself p2 l2) => t_path σ p1 p2 ∧ l1 ≡ l2
    | _ => False
    end%I
  with
  t_ty (σ: vls) (T1 T2: ty): iProp Σ :=
    match (T1, T2) with
    | (TTop, TTop) => True
    | (TBot, TBot) => True
    | (TAnd T11 T12, TAnd T21 T22) =>
      t_ty σ T11 T21 ∧ t_ty σ T12 T22
    | (TOr T11 T12, TOr T21 T22) =>
      t_ty σ T11 T21 ∧ t_ty σ T12 T22
    | (TLater T1, TLater T2) =>
      t_ty σ T1 T2
    | (TAll T11 T12, TAll T21 T22) =>
      t_ty σ T11 T21 ∧ t_ty (push_var σ) T12 T22
    | (TMu T1, TMu T2) =>
      t_ty (push_var σ) T1 T2
    | (TVMem l1 T1, TVMem l2 T2) => l1 ≡ l2 ∧ t_ty σ T1 T2
    | (TTMem l1 T11 T12, TTMem l2 T21 T22) => l1 ≡ l2 ∧ t_ty σ T11 T21 ∧ t_ty σ T12 T22
    | (TSel p1 l1, TSel p2 l2) => t_path σ p1 p2 ∧ l1 ≡ l2
    | (TSelA p1 l1 T11 T12, TSelA p2 l2 T21 T22) => t_path σ p1 p2 ∧ l1 ≡ l2 ∧ t_ty σ T11 T21 ∧ t_ty σ T12 T22
    | _ => False
    end%I
  .

  (* Probably unused. *)
  Fixpoint t_vls (σ: vls) (vs1 vs2: vls): iProp Σ :=
    match (vs1, vs2) with
    | (vlnil, vlnil) => True
    | (vlcons d1 ds1, vlcons d2 ds2) =>
      t_vl σ d1 d2 ∧ t_vls σ ds1 ds2
    | _ => False
    end%I.

End Sec.
