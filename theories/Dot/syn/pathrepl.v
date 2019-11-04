From D.Dot.syn Require Import syn.

Implicit Types
         (T : ty) (v : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (Γ : ctx) (vs : vls) (l : label).

Reserved Notation "p1 .p[ p := q  ]" (at level 65).
Definition psubst_path p q : path → path := fix F p1 :=
  match (decide (p1 = p)) with
  | left _ => q
  | _ =>
    match p1 with
    | pv _ => p1 (* no, values can contain paths! *)
    | pself p1' l => pself (F p1') l
    end
  end.
Notation "p1 .p[ p := q  ]" := (psubst_path p q p1).

Lemma psubst_path_id p p1: psubst_path p p p1 = p1.
Proof. elim: p1 => /= *; case_decide; by f_equal. Qed.

From D.Dot.lr Require Import path_wp unary_lr.
From iris.proofmode Require Import tactics.

Section foo.
  Context `{dlangG Σ}.
  Lemma rewrite_tsel_psubst p l ρ v vr:
    interp (TSel p l) ρ v -∗
    path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) -∗ interp (TSel (pv vr) l) ρ v.
  Proof.
    rewrite /= {1}path_wp_eq.
    iDestruct 1 as (vr') "[Hp H]"; iDestruct "H" as (ψ d Hl) "H"; iIntros "Hp'".
    iDestruct (path_wp_det with "Hp Hp'") as %->; iClear "Hp Hp'".
    iExists ψ, d. iFrame (Hl) "H".
  Qed.
End foo.
