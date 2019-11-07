From iris.proofmode Require Import tactics.

From D.Dot.syn Require Import syn.
From D.Dot.lr Require Import unary_lr.

Implicit Types
         (T : ty) (v w : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (Γ : ctx) (vs : vls) (l : label).

Implicit Types (Pv : vl → Prop).
Set Nested Proofs Allowed.

(* XXX For Iris *)
Hint Extern 1 (environments.envs_entails _ (_ ∗-∗ _)) => iSplit : core.

Lemma ren_scons v ρ : ren (+1) >> v .: ρ = ρ.
Proof. done. Qed.

Fixpoint path_wp_pure p Pv : Prop :=
  match p with
  | pself p l => path_wp_pure p (λ v, ∃ w, v @ l ↘ dvl w ∧ Pv w)
  | pv vp => Pv vp
  end.

Global Instance Proper_pwp: Proper ((=) ==> pointwise_relation _ iff ==> iff) path_wp_pure.
Proof.
  (* The induction works best in this shape, but this instance is best kept local. *)
  have Proper_pwp_2: ∀ p, Proper (pointwise_relation _ iff ==> iff) (path_wp_pure p).
  elim; solve_proper.
  solve_proper.
Qed.

Lemma path_wp_pure_wand {Pv1 Pv2 p}:
  path_wp_pure p Pv1 →
  (∀ v, Pv1 v → Pv2 v) →
  path_wp_pure p Pv2.
Proof.
  elim: p Pv1 Pv2 => /= [v|p IHp l] Pv1 Pv2 Hp Hwand;
    first by apply Hwand.
  apply: (IHp _ _ Hp) => {IHp Hp} v [vq [??]].
  eauto.
Qed.

Lemma path_wp_pure_eq p Pv :
  path_wp_pure p Pv ↔ ∃ v, path_wp_pure p (λ w, w = v) ∧ Pv v.
Proof.
  elim: p Pv => [ v | p IHp l ] Pv /=; split.
  - eauto.
  - by destruct 1 as (w & <- & ?).
  - rewrite IHp.
    destruct 1 as (v & Hp & w & ?&?).
    eexists w; split; last by [].
    apply (path_wp_pure_wand Hp).
    intros; subst; exists w; eauto.
  - setoid_rewrite IHp; intros; ev; subst; eauto.
Qed.

Lemma path_wp_pure_det {p v1 v2}:
  path_wp_pure p (λ w, w = v1) →
  path_wp_pure p (λ w, w = v2) →
  v1 = v2.
Proof.
  elim: p v1 v2 => [v /=| p /= IHp l //] v1 v2;
    first by intros <- <-.
  rewrite !path_wp_pure_eq.
  destruct 1 as (w1 & Hp1 & ?); destruct 1 as (w2 & Hp2 & ?); ev; simplify_eq.
  pose proof (IHp _ _ Hp1 Hp2) as <-.
  by objLookupDet.
Qed.

Lemma path_wp_pure_swap p u :
  path_wp_pure p (λ w, u = w) ↔
  path_wp_pure p (λ w, w = u).
Proof. split => Hp; exact: path_wp_pure_wand. Qed.

Definition alias_paths_pure p q ρ :=
  path_wp_pure p.|[ρ] (λ vp, path_wp_pure q.|[ρ] (λ vq, vp = vq)).

Lemma alias_paths_pure_refl_vl v ρ :
  alias_paths_pure (pv v) (pv v) ρ.
Proof. done. Qed.

Lemma alias_paths_pure_eq p q ρ:
  alias_paths_pure p q ρ ↔
  ∃ v,
    path_wp_pure p.|[ρ] (λ vp, vp = v) ∧
    path_wp_pure q.|[ρ] (λ vq, vq = v).
Proof.
  rewrite /= /alias_paths_pure !path_wp_pure_eq. split => -[vp];
    [ rewrite (path_wp_pure_swap q.|[_]) |
      rewrite -(path_wp_pure_swap q.|[_]) ]; eauto.
Qed.

Lemma alias_paths_pure_symm p q ρ :
  alias_paths_pure p q ρ → alias_paths_pure q p ρ.
Proof. rewrite !alias_paths_pure_eq. intros; ev; eauto. Qed.

Lemma alias_paths_equiv_pure p q ρ:
  alias_paths_pure p q ρ ↔
    (∃ u, path_wp_pure p.|[ρ] (λ vp, vp = u)) ∧
    ∀ Pv, path_wp_pure p.|[ρ] Pv ↔ path_wp_pure q.|[ρ] Pv.
Proof.
  rewrite alias_paths_pure_eq; split.
  - destruct 1 as (v & Hp & Hq).
    split. by eauto. intros Pv.
    rewrite !path_wp_pure_eq.
    f_equiv => w; split => -[Hr];
      [ rewrite -(path_wp_pure_det Hp Hr)
      | rewrite -(path_wp_pure_det Hq Hr)]; auto.
  - intros [[u Hp] Heq]. exists u.
    split; by [|rewrite -Heq].
Qed.

Section equivI_utils.
  Context `{dlangG Σ}.

  Lemma exists_equivI {A} {PROP: sbi} (φ1 φ2 : A -d> PROP) :
    (∀ x, φ1 x ≡ φ2 x) ⊢@{PROP}
    (∃ x, φ1 x) ≡ ∃ x, φ2 x.
  Proof.
    rewrite -discrete_fun_equivI.
    apply (@f_equiv _ _ _ (λ φ : _ -d> _, ∃ x, φ x)%I). solve_proper.
  Qed.

  Lemma forall_equivI {A} {PROP: sbi} (φ1 φ2 : A -d> PROP) :
    (∀ x, φ1 x ≡ φ2 x) ⊢@{PROP}
    (∀ x, φ1 x) ≡ ∀ x, φ2 x.
  Proof.
    rewrite -discrete_fun_equivI.
    apply (@f_equiv _ _ _ (λ φ : _ -d> _, ∀ x, φ x)%I). solve_proper.
  Qed.

  Lemma wp_equivI (φ1 φ2 : vl -d> iPropO Σ) t :
    (∀ x, φ1 x ≡ φ2 x) ⊢@{iPropI Σ}
    WP t {{ φ1 }} ≡ WP t {{ φ2 }}.
  Proof.
    rewrite -discrete_fun_equivI.
    apply (@f_equiv _ _ _ (λ φ : _ -d> _, WP t {{ φ }})%I). solve_proper.
  Qed.

  Lemma or2_equivI {PROP : sbi} (P1 P2 Q : PROP) :
    P1 ≡ P2 ⊢@{PROP} (P1 ∨ Q) ≡ (P2 ∨ Q).
  Proof. apply (@f_equiv _ _ _ (λ P, P ∨ Q)%I). solve_proper. Qed.

  Lemma and2_equivI {PROP : sbi} (P1 P2 Q : PROP) :
    P1 ≡ P2 ⊢@{PROP} (P1 ∧ Q) ≡ (P2 ∧ Q).
  Proof. apply (@f_equiv _ _ _ (λ P, P ∧ Q)%I). solve_proper. Qed.

(*
  Lemma and_equivI {PROP : sbi} (P1 P2 Q1 Q2 : PROP) :
    P1 ≡ P2 ⊢@{PROP} Q1 ≡ Q2 -∗
    (P1 ∧ Q1) ≡ (P2 ∧ Q2).
  Proof.
  Admitted. *)

  Lemma wand2_equivI {PROP : sbi} (P1 P2 Q : PROP) :
    P1 ≡ P2 ⊢@{PROP} (P1 -∗ Q) ≡ (P2 -∗ Q).
  Proof. apply (@f_equiv _ _ _ (λ P, P -∗ Q)%I). solve_proper. Qed.

End equivI_utils.

Definition psubst_path p q : path → path := fix F r :=
  match (decide (r = p)) with
  | left _ => q
  | _ =>
    match r with
    | pv _ => r (* XXX no, values can contain paths! OTOH, pDOT path replacement doesn't do this. *)
    | pself r' l => pself (F r') l
    end
  end.
Notation "r .p[ p := q  ]" := (psubst_path p q r) (at level 65).

Lemma psubst_path_id p q : q .p[ p := p ] = q.
Proof. elim: q => /= *; case_decide; by f_equal. Qed.

Lemma psubst_path_self p q: p .p[ p := q ] = q.
Proof. case: p => /= *; by rewrite decide_True. Qed.

(* Useful ???*)
Lemma psubst_path_eq p q r: psubst_path p q r =
  match (decide (r = p)) with
  | left _ => q
  | _ =>
    match r with
    | pv _ => r
    | pself r' l => pself (psubst_path p q r') l
    end
  end.
Proof. by case: r. Qed.

(* Alternative *)
Reserved Notation "p1 ~pp[ p := q  ] p2" (at level 70).
Inductive path_path_repl (p q : path) : path → path → Prop :=
| path_path_repl_base : p ~pp[ p := q ] q
| path_path_repl_self p1 p2 l :
  p1 ~pp[ p := q ] p2 →
  pself p1 l ~pp[ p := q ] pself p2 l
where "p1 ~pp[ p := q  ] p2" := (path_path_repl p q p1 p2) .

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
| ty_path_repl_TSel r l :
  TSel r l ~p[ p := q ] TSel (r .p[ p := q ]) l
where "T1 ~p[ p := q  ] T2" := (ty_path_repl p q T1 T2) .

Lemma ty_path_repl_id p T1 T2 : T1 ~p[ p := p ] T2 → T1 = T2.
Proof. intros Hr; dependent induction Hr; by rewrite // ?IHHr // psubst_path_id. Qed.

Section path_repl.
  Context `{dlangG Σ}.
  Implicit Types (φ: vl → iProp Σ).

  Lemma path_wp_pureable p Pv:
    path_wp p (λ v, ⌜Pv v⌝) ⊣⊢@{iPropI Σ} ⌜path_wp_pure p Pv⌝.
  Proof.
    elim: p Pv => /= [//|p IHp l] Pv.
    by rewrite -{}IHp; f_equiv => v; iIntros "!% /=".
  Qed.

  Global Instance path_wp_pureableI p Pv :
   IntoPure (@path_wp Σ p (λ v, ⌜Pv v⌝))%I (path_wp_pure p Pv).
  Proof. by rewrite /IntoPure path_wp_pureable. Qed.
  Global Instance path_wp_pureableF p Pv :
   FromPure false  (@path_wp Σ p (λ v, ⌜Pv v⌝))%I (path_wp_pure p Pv).
  Proof. by rewrite /FromPure/= path_wp_pureable. Qed.

  Lemma path_wp_swap p u :
    path_wp p (λ w, ⌜u = w⌝) ⊣⊢@{iPropI Σ}
    path_wp p (λ w, ⌜w = u⌝).
  Proof. iIntros "!%". by rewrite /= path_wp_pure_swap. Qed.

  Definition alias_paths p q ρ : iProp Σ :=
    path_wp p.|[ρ] (λ vp, path_wp q.|[ρ] (λ vq, ⌜vp = vq⌝))%I.

  Lemma alias_paths_pureable p q ρ:
    alias_paths p q ρ ⊣⊢ ⌜alias_paths_pure p q ρ⌝.
  Proof.
    rewrite /alias_paths/= -path_wp_pureable.
    f_equiv => vp. apply path_wp_pureable.
  Qed.

  Global Instance alias_paths_pureableI p q ρ :
   IntoPure (alias_paths p q ρ) (alias_paths_pure p q ρ).
  Proof. by rewrite /IntoPure alias_paths_pureable. Qed.
  Global Instance alias_paths_pureableF p q ρ :
   FromPure false (alias_paths p q ρ) (alias_paths_pure p q ρ).
  Proof. by rewrite /FromPure/= alias_paths_pureable. Qed.

  Lemma alias_paths_refl_vl v ρ :
    alias_paths (pv v) (pv v) ρ.
  Proof. by iIntros "!%". Qed.

  Lemma alias_paths_eq p q ρ:
    alias_paths p q ρ ⊣⊢
    ∃ v,
      path_wp p.|[ρ] (λ vp : vl, ⌜vp = v⌝) ∧
      path_wp q.|[ρ] (λ vq : vl, ⌜vq = v⌝).
  Proof. iIntros "!%"; rewrite /= alias_paths_pure_eq. intuition. Qed.

  Lemma alias_paths_symm p q ρ :
    alias_paths p q ρ -∗ alias_paths q p ρ.
  Proof.
    rewrite !alias_paths_pureable; iIntros "!%".
    exact: alias_paths_pure_symm.
  Qed.

  Lemma simpl_alias_1 p vr ρ :
     alias_paths p (pv vr) ρ ⊣⊢ path_wp p.|[ρ] (λ w : vl, ⌜w = vr.[ρ]⌝) .
  Proof. done. Qed.

  Lemma simpl_alias_2 p vr ρ :
     alias_paths (pv vr) p ρ ⊣⊢ path_wp p.|[ρ] (λ w : vl, ⌜w = vr.[ρ]⌝) .
  Proof. exact: path_wp_swap. Qed.

  Ltac iProperness :=
    repeat first
    [ iEval (progress rewrite -(wp_equivI, exists_equivI, forall_equivI)); iIntros
    (* f_equiv must come before those others for performance. *)
    | iEval (progress rewrite -(f_equiv, and2_equivI, wand2_equivI, or2_equivI))
    ].

  (* Not provable through pure props for impure [φ]. *)
  Lemma alias_paths_equiv p q ρ:
    alias_paths_pure p q ρ ↔
      (∃ u, path_wp_pure p.|[ρ] (λ vp, vp = u)) ∧
      ∀ φ, path_wp p.|[ρ] φ ≡ path_wp q.|[ρ] φ.
  Proof.
    rewrite alias_paths_pure_eq; split.
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

  Lemma alias_paths_equiv' p q ρ:
    ⌜alias_paths_pure p q ρ⌝ ⊣⊢@{iPropI Σ}
      (∃ u, path_wp p.|[ρ] (λ vp, ⌜vp = u⌝)) ∧
      ∀ φ, ⌜path_wp p.|[ρ] φ ≡ path_wp q.|[ρ] φ⌝.
  Proof. iIntros "!%". apply alias_paths_equiv. Qed.

  Lemma alias_paths_elim_eq φ p q ρ:
    alias_paths_pure p q ρ →
    path_wp p.|[ρ] φ ≡ path_wp q.|[ρ] φ.
  Proof. intros ?%alias_paths_equiv. intuition. Qed.

  Lemma alias_paths_elim_eq' φ p q ρ:
    ⌜alias_paths_pure p q ρ⌝ ⊢@{iPropI Σ}
    ⌜path_wp p.|[ρ] φ ≡ path_wp q.|[ρ] φ⌝.
  Proof. iIntros "!%". apply alias_paths_elim_eq. Qed.

  Lemma alias_paths_elim_wand p q ρ φ:
    ⌜alias_paths_pure p q ρ⌝ ⊢@{iPropI Σ}
    path_wp p.|[ρ] φ -∗ path_wp q.|[ρ] φ.
  Proof. rewrite (alias_paths_elim_eq' φ). iIntros (->) "$". Qed.

  Lemma path_replacement_equiv_plain {p r ρ} q (φ : vl → iProp Σ):
    alias_paths_pure p r ρ →
    path_wp q.|[ρ] φ ≡ path_wp (q .p[p := r]).|[ρ] φ.
  Proof.
    elim: q φ => [w | q IHq l] φ /=; case_decide; simplify_eq/=.
    - apply (alias_paths_elim_eq φ (pv w) r).
    - done.
    - rewrite /= !path_wp_eq alias_paths_pure_eq /=.
      destruct 1 as (vr & (vq & Hq & w & Hl & ->)%path_wp_pure_eq & Hr).
      iSplit.
      + iDestruct 1 as (vq' Hq' vr' Hl') "Hφ".
        rewrite (path_wp_pure_det Hq' Hq) in Hl'.
        objLookupDet. eauto.
      + iDestruct 1 as (vr' Hr') "Hφ".
        rewrite (path_wp_pure_det Hr' Hr).
        eauto.
    - exact: IHq.
  Qed.

  Lemma path_replacement_equiv_plain' {p r ρ} q (φ : vl → iProp Σ):
    ⌜alias_paths_pure p r ρ⌝ ⊢@{iPropI Σ}
    path_wp q.|[ρ] φ ≡ path_wp (q .p[p := r]).|[ρ] φ.
  Proof. iIntros (?) "!%". exact: path_replacement_equiv_plain. Qed.

  (* Lemma path_replacement_equiv_pure {p r ρ} q (φ : vl → iProp Σ):
    alias_paths p r ρ ⊢@{iPropI Σ}
    (⌜ path_wp q.|[ρ] φ ≡ path_wp (q .p[p := r]).|[ρ] φ⌝)%I.
  Proof.
    elim: q φ => [w | q IHq l] φ /=;
     case_decide; simplify_eq/=.
    (* - apply (alias_paths_elim_eq φ (pv w) r).
    - by iIntros.
    - rewrite /= !path_wp_eq alias_paths_eq /=.
      iDestruct 1 as (vr) "[Hq' #Hr]".
      iDestruct (path_wp_eq with "Hq'") as (vq) "#[Hq A]";
        iDestruct "A" as %(? & Hl & ->).
      iApply prop_ext; iModIntro; iSplit.
      + iDestruct 1 as (vq') "[Hq' A]"; iDestruct "A" as (vr' Hl') "Hφ".
        iDestruct (path_wp_det with "Hq Hq'") as %<-; iClear "Hq Hq'".
        by objLookupDet; eauto.
      + iDestruct 1 as (vr') "[Hr' Hφ]".
        iDestruct (path_wp_det with "Hr Hr'") as %<-; iClear "Hr'".
        eauto.
    - iIntros. by iApply IHq.
  Qed. *)
  Admitted.

  Lemma path_replacement_equiv_plain2 {p r ρ} q (φ : vl → iProp Σ):
    alias_paths p r ρ ⊢@{iPropI Σ}
    path_wp q.|[ρ] φ ≡ path_wp (q .p[p := r]).|[ρ] φ.
  Proof. rewrite path_replacement_equiv_pure. by iIntros (<-). Qed. *)

  Lemma rewrite_tsel_psubst2 p q l ρ v r:
    ⌜alias_paths_pure p r ρ⌝ ⊢@{iPropI Σ}
    ⟦ TSel q l ⟧ ρ v ≡ ⟦ TSel (q .p[ p := r ]) l ⟧ ρ v.
  Proof. exact: path_replacement_equiv_plain'. Qed.

  (* That's false. *)
  (* Lemma path_replacement_equiv_0 {p r ρ} q:
    alias_paths p r ρ ⊢@{iPropI Σ}
    alias_paths q (q .p[p := r]) ρ.
  Proof.
    elim: q => [w | q IHq l] /=; case_decide; simplify_eq/=.
    - by iIntros.
    - rewrite -alias_paths_refl_vl. by iIntros.
    - by iIntros.
    - rewrite /= IHq !alias_paths_eq /=.
      iDestruct 1 as (vr) "#[Hq Hqr]".
      (* We don't know that [pself q l] terminates! *)
  Abort. *)

  Lemma path_replacement_equiv p q r ρ (φ : vl → iProp Σ):
    ⌜alias_paths_pure p r ρ⌝ ⊢@{iPropI Σ}
    □(path_wp q.|[ρ] φ ∗-∗ path_wp (q .p[p := r]).|[ρ] φ).
  Proof.
    iIntros "#H !>".
    iRewrite -(path_replacement_equiv_plain' q φ with "H").
    by rewrite -wand_iff_refl.
  Qed.

  Lemma alias_path_pure_weaken p q ρ v:
     alias_paths_pure p.|[ren (+1)] q.|[ren (+1)] (v .: ρ) ↔
     alias_paths_pure p q ρ.
  Proof.
    by rewrite /alias_paths_pure; f_equiv; rewrite hsubst_comp ren_scons.
  Qed.

  Lemma rewrite_ty_path_repl_plain p q T1 T2 ρ v:
    T1 ~p[ p := q ] T2 →
    alias_paths_pure p q ρ →
    ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v.
  Proof.
    move => Hrew; move: v ρ.
    induction Hrew => v ρ He /=; properness;
      by [|exact: path_replacement_equiv_plain|iApply IHHrew; rewrite ?alias_path_pure_weaken].
  Qed.

  Lemma rewrite_ty_path_repl_plain' p q T1 T2 ρ v:
    T1 ~p[ p := q ] T2 →
    alias_paths p q ρ ⊢@{iPropI Σ} (* p : q.type *)
    ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v.
  Proof. iIntros "!% /=". exact: rewrite_ty_path_repl_plain. Qed.

  (* Lemma rewrite_ty_path_repl_plain'_slow p q T1 T2 ρ v:
    T1 ~p[ p := q ] T2 →
    ⌜alias_paths_pure p q ρ⌝ ⊢@{iPropI Σ} (* p : q.type *)
    ⟦ T1 ⟧ ρ v ≡ ⟦ T2 ⟧ ρ v.
  Proof.
    move => Hrew; move: v ρ.
    induction Hrew => v ρ;
      iIntros "/= #H"; iProperness; last
      iApply path_replacement_equiv_plain';
      try by [|iApply IHHrew; rewrite ?alias_path_pure_weaken].
  Qed. *)

  (* Lemma TMu_E Γ T v: Γ ⊨ tv v : TMu T -∗ Γ ⊨ tv v : T.|[ids 0/] .p [.
  Proof. by rewrite TMu_equiv. Qed.

  Lemma TMu_I Γ T v: Γ ⊨ tv v : T.|[v/] -∗ Γ ⊨ tv v : TMu T.
  Proof. by rewrite TMu_equiv. Qed. *)


      (* rewrite -?exists_equivI; iIntros; rewrite -?f_equiv.
    1-2: rewrite -forall_equivI; iIntros (w).
    by iRewrite (IHHrew w with "H").
    rewrite -f_equiv -wp_equivI; iIntros.
    1-2: by iApply IHHrew; rewrite // hsubst_comp subst_comp ren_scons.
    all: rewrite -exists_equivI; iIntros (w); rewrite -!f_equiv.
    by iRewrite (IHHrew w with "H").
    rewrite -?and2_equivI.
    rewrite -f_equiv.
    all: rewrite -forall_equivI; iIntros (v0); by iRewrite (IHHrew v0 with "H").
  Qed. *)
      (* rewrite -f_equiv -wp_equivI; iIntros.

       iApply "H".
    (* iDestruct 1 as (t Heq) "#H1"; iExists t; iSplit; first done; iIntros "!>!>" (w) "#Ha"; *)
      by iRewrite (IHHrew w with "H").
      iApply internal_eq_proper. exist_proper.
    f_equiv.
    properness.
    iDestruct 1 as "H1".
    iDestruct 1 as (t Heq) "H1". iExists t; iSplit; first done; iIntros "!>!>" (w) "#Ha"; iApply "H1"; by iApply IHHrew. *)

    (* move HE: (pv vr) => q Hrew.
    iInduction Hrew as [] "IHHrew" forall (v ρ vr HE); subst q;
      last iApply rewrite_tsel_psubst2; iIntros "/= #H";
      try by iRewrite ("IHHrew" $! v with "[//] H").
      try by iRewrite ("IHHrew" with "[//] H").
       iApply prop_ext; iModIntro; iSplit. *)

(* Axiom skip: forall a, a. *)
  (* Special cases, any use? *)
  (* Lemma path_replacement_equiv_plain_special {p vr ρ} q (φ : vl → iProp Σ):
    path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) ⊢@{iPropI Σ}
    path_wp q.|[ρ] φ ≡ path_wp (q .p[p := pv vr]).|[ρ] φ.
  Proof. rewrite -path_replacement_equiv_plain' -simpl_alias_1.
  by iIntros "!%". Qed.

  Lemma rewrite_tsel_psubst2_special p q l ρ v vr:
    path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) ⊢@{iPropI Σ}
    ⟦ TSel q l ⟧ ρ v ≡ ⟦ TSel (q .p[ p := pv vr ]) l ⟧ ρ v.
  Proof. exact: path_replacement_equiv_plain_special. Qed. *)

  (* Lemma rewrite_ty_path_repl p T1 T2 ρ v vr:
    T1 ~p[ p := pv vr ] T2 →
    path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) ⊢@{iPropI Σ}
    □(⟦ T1 ⟧ ρ v ∗-∗ ⟦ T2 ⟧ ρ v).
  Proof.
    (* V1: gets type error at Qed, due to [dependent induction]. *)
    intros Hrew; move: v ρ; dependent induction Hrew => v ρ;
    (* V2 *)
    (* move HE: (pv vr) => q; move => Hrew; move: v ρ vr HE. induction Hrew => v ρ vr HE; subst q; *)
      last apply skip; iIntros "/= #H !>"; iSplit.
    1-4: iIntros "[??]"; iFrame; by iApply IHHrew.
    1-4: iIntros "[?|?]"; iFrame; by (iLeft + iRight); iApply IHHrew.
    1-2: iIntros "? !>"; by iApply IHHrew.
    1-2: iDestruct 1 as (t Heq) "#H1"; iExists t; iSplit; first done; iIntros "!>!>" (w) "#Ha"; iApply "H1"; by iApply IHHrew.
    1-2: iDestruct 1 as (t Heq) "#H1"; iExists t; iSplit; first done; iIntros "!>!>" (w) "#Ha";
      iApply (wp_wand with "(H1 Ha)").
    1-4: iIntros; iApply IHHrew; rewrite // hsubst_comp subst_comp ren_scons; iApply "H".
    1-2: iDestruct 1 as (d Hl vm Heq) "H1"; iExists d; iSplit; first done; iExists vm; iSplit; first done; by iApply IHHrew.
    1-4: iDestruct 1 as (d Hl ψ) "[Hl #[HL HU]]"; iExists d; iSplit; first done; iExists ψ; iSplit; first done; iModIntro; iSplit; iIntros.
      1-8: try ((iApply "HL" || iApply "HU"); by [iApply IHHrew|]).
      1-2: iApply IHHrew; by [iApply "HL"|iApply "HU"|].
  Qed. *)

  (* Looks very false. *)
  (* Lemma swap_substs p q r ρ: (q .p[ p := r ]).|[ren ρ] = q.|[ren ρ] .p[ p.|[ren ρ] := r.|[ren ρ]].
  Proof.
    induction q eqn:Heq; cbn; case_decide; try by simplify_eq/=; rewrite 1?decide_True.
    case_decide => //=.
    rewrite H1. f_equal.
    simplify_eq/=.
  elim: q => /= [v | q IHq l]; case_decide; simplify_eq/=; try by rewrite 1?decide_True.

  rewrite decide_False; simplify_eq/=. done. naive_solver. congruence. *)

  (* Lemma path_replacement p q vr ρ φ:
    □path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) ⊢@{iPropI Σ}
    □(path_wp q.|[ρ] φ -∗ path_wp (q .p[p := pv vr]).|[ρ] φ).
  Proof.
    iIntros "#Heq !> HA".
    (* rewrite (path_replacement_equiv_plain q φ); by iApply (internal_eq_iff with "Heq"). *)
    iApply (path_replacement_equiv with "Heq HA").
  Qed.

  Lemma path_replacement_2 p q vr ρ φ:
    □path_wp p.|[ρ] (λ w, ⌜ w = vr.[ρ] ⌝) ⊢@{iPropI Σ}
    □(path_wp (q .p[p := pv vr]).|[ρ] φ -∗ path_wp q.|[ρ] φ).
  Proof.
    iIntros "#Heq !> HA".
    iApply (path_replacement_equiv with "Heq HA").
  Qed. *)

End path_repl.
