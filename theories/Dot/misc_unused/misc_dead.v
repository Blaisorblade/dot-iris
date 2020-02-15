From iris.proofmode Require Import tactics.
From D.pure_program_logic Require Import lifting.

From D Require Import proofmode_extra.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Section wp_extra.
  Context `{irisG Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Lemma wp_strong_mono_wf s1 s2 E1 E2 e Φ {Ψ} (wf: expr Λ → Prop):
    s1 ⊑ s2 →
    wf e →
    (∀ t1 t2 σ σ' ts κ, prim_step t1 σ κ t2 σ' ts → wf t1 → wf t2 ∧ Forall wf ts) →
    WP e @ s1; E1 {{ Φ }} -∗
    (∀ v, ⌜wf (of_val v)⌝ -∗ Φ v -∗ Ψ v) -∗
    WP e @ s2; E2 {{ Ψ }}.
  Proof.
    iIntros (? HwfE Hpres) "H HΦ". iLöb as "IH" forall (e HwfE E1 E2 Φ Ψ).
    rewrite !wp_unfold /wp_pre.
    destruct (to_val e) as [v|] eqn:?.
    { iApply ("HΦ" with "[%] [-//]"). apply of_to_val in Heqo. by subst. }
    iIntros (σ1 κ κs n) "Hσ".
    iDestruct ("H" with "[$]") as "[% H]".
    iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep).
    iDestruct ("H" with "[//]") as "H". iIntros "!>".
    have HPefs: Forall wf efs. by eapply Hpres.
    iDestruct "H" as "(Hσ & H & Hefs)".
    iFrame "Hσ". iSplitR "Hefs".
    - iApply ("IH" with "[%] H HΦ"). by eapply Hpres.
    - iApply (big_sepL_impl with "Hefs"); iIntros "!#" (k ef Heq).
      iIntros "H". iApply ("IH" with "[%] H"); auto.
      edestruct (Hpres e e2) => //. by eapply Forall_lookup_1.
  Qed.

  Lemma wp_wand_wf s E e Φ {Ψ} (wf: expr Λ → Prop):
    wf e →
    (∀ t1 t2 σ σ' ts κ, prim_step t1 σ κ t2 σ' ts → wf t1 → wf t2 ∧ Forall wf ts) →
    WP e @ s; E {{ v, Φ v }} -∗
    (∀ v, ⌜wf (of_val v)⌝ -∗ Φ v -∗ Ψ v) -∗
    WP e @ s; E {{ v, Ψ v }}.
  Proof.
    iIntros (HwfE Hpres) "Hwp HΦ". iApply (wp_strong_mono_wf with "Hwp"); eauto.
  Qed.
End wp_extra.

From iris.program_logic Require Import ectxi_language.
From D.Dot Require Import syn dlang_inst path_wp rules synLemmas step_fv
  lr_syn_aux.
Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx) (ρ : env).

Fixpoint plength p : nat :=
  match p with
  | pv _ => 0
  | pself p _ => S (plength p)
  end.

Lemma plength_subst_inv p s :
  plength p.|[s] = plength p.
Proof. by elim: p => [v| p /= ->]. Qed.

Instance: HSubst vl ectx_item := λ ρ K,
  match K with
  | AppLCtx e2 => AppLCtx e2.|[ρ]
  | AppRCtx v1 => AppRCtx v1.[ρ]
  | ProjCtx l => K
  | SkipCtx => K
  | UnCtx u => K
  | BinLCtx b e2 => BinLCtx b e2.|[ρ]
  | BinRCtx b v1 => BinRCtx b v1.[ρ]
  | IfCtx e1 e2 => IfCtx e1.|[ρ] e2.|[ρ]
  end.

Lemma fill_item_subst K e ρ :
  (fill_item K e).|[ρ] = fill_item K.|[ρ] e.|[ρ].
Proof. by case: K. Qed.

Lemma subst_app (Ks1 Ks2 : list ectx_item) ρ:
  (Ks1 ++ Ks2).|[ρ] =
  Ks1.|[ρ] ++ Ks2.|[ρ].
Proof. elim: Ks1 => [//|K Ks1 IH]; cbn; by rewrite IH. Qed.

Lemma fill_subst K e ρ :
  (fill K e).|[ρ] = fill K.|[ρ] e.|[ρ].
Proof.
  induction K using rev_ind => //.
  rewrite subst_app !fill_app fill_item_subst !IHK //.
Qed.
(*
Instance: LanguageCtx (λ e, (fill Ks e).|[ρ]).
Proof.
  Import rules syn asubst_base.
  intros.
  rewrite -Proper_LanguageCtx; first last.
  intro.
  by rewrite fill_subst.
  apply _.
Abort. *)

Lemma dms_lookup_subst l ds p ρ :
  dms_lookup l (selfSubst ds) = Some (dpt p) →
  dms_lookup l (selfSubst ds.|[up ρ]) = Some (dpt p.|[ρ]).
Proof.
  rewrite /selfSubst (subst_swap _ _ (vobj ds)).
  move: (vobj ds) => v0.
  elim: ds ρ => [|[l' d'] ds IHds] ρ //; cbn => Hl.
  case_decide; simplify_eq/=; rewrite ?IHds // Hl //.
Qed.

Lemma head_step_subst e1 σ1 κ e2 σ2 efs ρ:
  head_step e1 σ1 κ e2 σ2 efs → head_step e1.|[ρ] σ1 κ e2.|[ρ] σ2 efs.
Proof.
  elim => //; intros *; eauto using head_step.
  - have <-: t1.|[up ρ].|[v2.[ρ]/] = t1.|[v2/].|[ρ].
    by rewrite subst_swap.
    by constructor.
  - intros [ds [-> Hl]]; rewrite path2tm_subst.
    constructor.
    eexists ds.|[up ρ]; split => //.
    exact: dms_lookup_subst.
  - intros Hev; constructor; move: Hev.
    rewrite /un_op_eval => Hev.
    by repeat (case_match => //; simplify_eq/=).
  - intros Hev; constructor; move: Hev.
    rewrite /bin_op_eval /bin_op_eval_nat /bin_op_eval_bool => Hev.
    by repeat (case_match => //; simplify_eq/=).
Qed.

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  (* Was also proved for DSub. *)
  Lemma wp_wand_cl e Φ Ψ:
    WP e {{ v, Φ v }} -∗ ⌜ nclosed e 0 ⌝ -∗ (∀ v, Φ v -∗ ⌜ nclosed_vl v 0 ⌝ -∗ Ψ v) -∗ WP e {{ v, Ψ v }}.
  Proof.
    iIntros "/= He" (Hcle) "Himpl". iApply (wp_wand_wf _ _ e Φ (flip nclosed 0) Hcle with "He [Himpl]").
    intros. by eapply nclosed_prim_step.
    iIntros (v Hclv) "/= H". iApply ("Himpl" with "H [%]"). exact: fv_of_val_inv.
  Qed.
End Sec.

Section path_wp.
  Context `{HdlangG: dlangG Σ}.
  Implicit Types (φ : vl -d> iPropO Σ).

  (* Lemma path_wp_cl n p v:
    path_wp_pure p (eq v) →
    nclosed p n → nclosed_vl v n.
  Proof.
    elim: p v => /= [w|p IHp l] v.
    - intros ->. exact: fv_pv_inv.
    - rewrite path_wp_pure_eq.
      intros (w & Hpwp & _ & Hl & <-) Hclps.
      enough (nclosed (dpt v) n). by eauto with fv.
      eapply nclosed_lookup', IHp; eauto with fv.
  Qed. *)
End path_wp.

From D.Dot.lr Require Import unary_lr path_wp path_repl.
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

  Lemma wand2_equivI {PROP : sbi} (P1 P2 Q : PROP) :
    P1 ≡ P2 ⊢@{PROP} (P1 -∗ Q) ≡ (P2 -∗ Q).
  Proof. apply (@f_equiv _ _ _ (λ P, P -∗ Q)%I). solve_proper. Qed.
End equivI_utils.

Ltac iProperness :=
  repeat first
  [ iEval (progress rewrite -(wp_equivI, exists_equivI, forall_equivI)); iIntros
  (* f_equiv must come before those others for performance. *)
  | iEval (progress rewrite -(f_equiv, and2_equivI, wand2_equivI, or2_equivI))
  ].
