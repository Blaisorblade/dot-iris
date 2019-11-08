From iris.proofmode Require Import tactics.

From D.Dot.syn Require Import syn.
From D.Dot.lr Require Import unary_lr.

Implicit Types
         (T : ty) (v w : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (Γ : ctx) (vs : vls) (l : label) (Pv : vl → Prop).
Set Nested Proofs Allowed.

Lemma ren_scons v ρ : ren (+1) >> v .: ρ = ρ.
Proof. done. Qed.

(* XXX Unclear why is the substitution built-in. But beware of dropping that, as substitution and path replacement don't swap. *)
Definition alias_paths p q ρ :=
  path_wp_pure p.|[ρ] (λ vp, path_wp_pure q.|[ρ] (λ vq, vp = vq)).

Lemma alias_paths_pv_eq_1 p vr ρ :
  alias_paths p (pv vr) ρ ↔ path_wp_pure p.|[ρ] (λ w, w = vr.[ρ]).
Proof. done. Qed.

Lemma alias_paths_pv_eq_2 p vr ρ :
  alias_paths (pv vr) p ρ ↔ path_wp_pure p.|[ρ] (λ w, w = vr.[ρ]).
Proof. by rewrite -path_wp_pure_swap. Qed.

Lemma alias_paths_weaken p q ρ v:
  alias_paths p.|[ren (+1)] q.|[ren (+1)] (v .: ρ) =
  alias_paths p q ρ.
Proof.
  by rewrite /alias_paths; f_equiv; rewrite hsubst_comp ren_scons.
Qed.

Lemma alias_paths_refl_vl v ρ :
  alias_paths (pv v) (pv v) ρ.
Proof. done. Qed.

Lemma alias_paths_sameres p q ρ:
  alias_paths p q ρ ↔
  ∃ v,
    path_wp_pure p.|[ρ] (λ vp, vp = v) ∧
    path_wp_pure q.|[ρ] (λ vq, vq = v).
Proof.
  rewrite /= /alias_paths !path_wp_pure_eq. split => -[vp];
    [ rewrite (path_wp_pure_swap q.|[_]) |
      rewrite -(path_wp_pure_swap q.|[_]) ]; eauto.
Qed.

Lemma alias_paths_symm p q ρ :
  alias_paths p q ρ → alias_paths q p ρ.
Proof. rewrite !alias_paths_sameres. intros; ev; eauto. Qed.

Lemma alias_paths_equiv_pure p q ρ:
  alias_paths p q ρ ↔
    (∃ u, path_wp_pure p.|[ρ] (λ vp, vp = u)) ∧
    ∀ Pv, path_wp_pure p.|[ρ] Pv ↔ path_wp_pure q.|[ρ] Pv.
Proof.
  rewrite alias_paths_sameres; split.
  - destruct 1 as (v & Hp & Hq).
    split. by eauto. intros Pv.
    rewrite !path_wp_pure_eq.
    f_equiv => w; split => -[Hr];
      [ rewrite -(path_wp_pure_det Hp Hr)
      | rewrite -(path_wp_pure_det Hq Hr)]; auto.
  - intros [[u Hp] Heq]. exists u.
    split; by [|rewrite -Heq].
Qed.

Reserved Notation "p1 ~pp[ p := q  ] p2" (at level 70).
Inductive path_path_repl (p q : path) : path → path → Prop :=
| path_path_repl_base : p ~pp[ p := q ] q
| path_path_repl_self p1 p2 l :
  p1 ~pp[ p := q ] p2 →
  pself p1 l ~pp[ p := q ] pself p2 l
where "p1 ~pp[ p := q  ] p2" := (path_path_repl p q p1 p2) .

Lemma psubst_path_id p1 p2 p : p1 ~pp[ p := p ] p2 → p1 = p2.
Proof. by elim; intros; simplify_eq/=. Qed.

Reserved Notation "T1 ~p[ p := q  ] T2" (at level 70).

Inductive ty_path_repl (p q : path) : ty → ty → Prop :=
| ty_path_repl_TAnd1 T1 T2 U :
  T1 ~p[ p := q ] T2 →
  TAnd T1 U ~p[ p := q ] TAnd T2 U
| ty_path_repl_TAnd2 T1 T2 U :
  T1 ~p[ p := q ] T2 →
  TAnd U T1 ~p[ p := q ] TAnd U T2
| ty_path_repl_TOr1 T1 T2 U :
  T1 ~p[ p := q ] T2 →
  TOr T1 U ~p[ p := q ] TOr T2 U
| ty_path_repl_TOr2 T1 T2 U :
  T1 ~p[ p := q ] T2 →
  TOr U T1 ~p[ p := q ] TOr U T2
| ty_path_repl_TLater T1 T2 :
  T1 ~p[ p := q ] T2 →
  TLater T1 ~p[ p := q ] TLater T2
| ty_path_repl_TAll1 T1 T2 U :
  T1 ~p[ p := q ] T2 →
  TAll T1 U ~p[ p := q ] TAll T2 U
| ty_path_repl_TAll2 T1 T2 U :
  T1 ~p[ p.|[ren (+1)] := q.|[ren (+1)] ] T2 →
  TAll U T1 ~p[ p := q ] TAll U T2
| ty_path_repl_TMu T1 T2 :
  T1 ~p[ p.|[ren (+1)] := q.|[ren (+1)] ] T2 →
  TMu T1 ~p[ p := q ] TMu T2
| ty_path_repl_TVMem T1 T2 l :
  T1 ~p[ p := q ] T2 →
  TVMem l T1 ~p[ p := q ] TVMem l T2
| ty_path_repl_TTMem1 T1 T2 U l :
  T1 ~p[ p := q ] T2 →
  TTMem l T1 U ~p[ p := q ] TTMem l T2 U
| ty_path_repl_TTMem2 T1 T2 U l :
  T1 ~p[ p := q ] T2 →
  TTMem l U T1 ~p[ p := q ] TTMem l U T2
| ty_path_repl_TSel p1 p2 l :
  p1 ~pp[ p := q ] p2 →
  TSel p1 l ~p[ p := q ] TSel p2 l
where "T1 ~p[ p := q  ] T2" := (ty_path_repl p q T1 T2) .

Lemma ty_path_repl_id p T1 T2 : T1 ~p[ p := p ] T2 → T1 = T2.
Proof.
  intros Hr; dependent induction Hr; rewrite // ?IHHr //.
  f_equiv; exact: psubst_path_id.
Qed.

(* XXX For Iris *)
Hint Extern 1 (environments.envs_entails _ (_ ∗-∗ _)) => iSplit : core.

Definition alias_pathsI {Σ} p q ρ : iProp Σ := ⌜alias_paths p q ρ⌝.

Section path_repl.
  Context `{dlangG Σ}.
  Implicit Types (φ: vl → iProp Σ).

  Notation path_wp p φ := (@path_wp Σ p φ).
  Notation alias_pathsI p q ρ := (@alias_pathsI Σ p q ρ).

  (* Not provable through pure props for impure [φ]. *)
  Lemma alias_paths_samepwp p q ρ:
    alias_paths p q ρ ↔
      (∃ u, path_wp_pure p.|[ρ] (λ vp, vp = u)) ∧
      ∀ φ, path_wp p.|[ρ] φ ≡ path_wp q.|[ρ] φ.
  Proof.
    rewrite alias_paths_sameres; split.
    - destruct 1 as (v & Hp & Hq).
      split; first by [eauto]; intros φ.
      rewrite !path_wp_eq. f_equiv => w.
      rewrite !path_wp_pureable; do 2 f_equiv.
      split => Hr; [ rewrite -(path_wp_pure_det Hp Hr)
        | rewrite -(path_wp_pure_det Hq Hr)]; auto.
    - destruct 1 as ((u & Hp) & Heq). exists u; split; first done.
      (* Yes, completely insane. *)
      apply (pure_soundness (M := iResUR Σ)).
      iRevert (Hp). by rewrite -!path_wp_pureable Heq.
  Qed.

  Lemma alias_paths_elim_eq φ p q ρ:
    alias_paths p q ρ →
    path_wp p.|[ρ] φ ≡ path_wp q.|[ρ] φ.
  Proof. intros ?%alias_paths_samepwp. intuition. Qed.

  (** Beware: we can do path replacement *before* substitution,
      even tho substitution and path replacement don't commute nicely.

      As a special case, we get the less surprising:
      [alias_paths p r ids → path_wp q φ ≡ path_wp (q .p[p := r]) φ].

      But we do need the general form. *)
  Lemma path_replacement_equiv {p r ρ} q q' (φ : vl → iProp Σ):
    q ~pp[ p := r ] q' →
    alias_paths p r ρ →
    path_wp q.|[ρ] φ ≡ path_wp q'.|[ρ] φ.
  Proof.
    move => Hrepl.
    elim: Hrepl φ => [| p1 p2 l Hrepl IHrepl] φ /=.
    exact: alias_paths_elim_eq.
    apply IHrepl.
  Qed.

  Lemma rewrite_ty_path_repl p q T1 T2 ρ v:
    T1 ~p[ p := q ] T2 →
    alias_paths p q ρ → (* p : q.type *)
    ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v.
  Proof.
    move => Hrew; move: v ρ.
    induction Hrew => v ρ He /=; properness;
      by [|exact: path_replacement_equiv|iApply IHHrew; rewrite ?alias_paths_weaken].
  Qed.

  (* Lemma TMu_E Γ T v: Γ ⊨ tv v : TMu T -∗ Γ ⊨ tv v : T.|[ids 0/] .p [.
  Proof. by rewrite TMu_equiv. Qed.

  Lemma TMu_I Γ T v: Γ ⊨ tv v : T.|[v/] -∗ Γ ⊨ tv v : TMu T.
  Proof. by rewrite TMu_equiv. Qed. *)

End path_repl.
