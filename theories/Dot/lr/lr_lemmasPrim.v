From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D.Dot Require Import rules unary_lr.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

Definition un_op_semtype u B1 Br := ∀ v, pure_interp_prim B1 v →
  ∃ w, un_op_eval u v = Some w ∧ pure_interp_prim Br w.

Definition bin_op_semtype b B1 B2 Br (P : prim_sem B1 → prim_sem B2 → Prop) :=
  ∀ v1 v2 l1 l2,
  prim_evals_to B1 v1 l1 →
  prim_evals_to B2 v2 l2 →
  P l1 l2 →
  ∃ w, bin_op_eval b v1 v2 = Some w ∧ pure_interp_prim Br w.

Inductive un_op_syntype : un_op → base_ty → base_ty → Set :=
| ty_unot : un_op_syntype unot tbool tbool.

Inductive bin_op_syntype : bin_op → ∀ (B1 B2 Br : base_ty),
  (prim_sem B1 → prim_sem B2 → Prop) → Set :=
| ty_beq_bool : bin_op_syntype beq    tbool tbool tbool (const (const True))
| ty_beq_nat  : bin_op_syntype beq    tnat  tnat  tbool (const (const True))
| ty_blt      : bin_op_syntype blt    tnat  tnat  tbool (const (const True))
| ty_ble      : bin_op_syntype ble    tnat  tnat  tbool (const (const True))
| ty_bplus    : bin_op_syntype bplus  tnat  tnat  tnat  (const (const True))
| ty_bminus   : bin_op_syntype bminus tnat  tnat  tnat  (λ n1 n2, n2 ≤ n1)
| ty_btimes   : bin_op_syntype btimes tnat  tnat  tnat  (const (const True))
| ty_bdiv     : bin_op_syntype bdiv   tnat  tnat  tnat  (λ _ n, n > 0).

Lemma un_op_syntype_sound {u B1 Br} : un_op_syntype u B1 Br → un_op_semtype u B1 Br.
Proof. rewrite /un_op_semtype /pure_interp_prim => Ht; inverse Ht; naive_solver. Qed.

Lemma bin_op_syntype_sound {b B1 B2 Br P} :
  bin_op_syntype b B1 B2 Br P → bin_op_semtype b B1 B2 Br P.
Proof.
  rewrite /bin_op_semtype /pure_interp_prim => Ht;
    dependent destruction Ht => *; simplify_eq/=;
    try (case_decide || case_match);
    naive_solver eauto with lia.
Qed.

Section Sec.
  Context `{HdlangG: dlangG Σ} Γ.

  Lemma T_Nat_I n: Γ ⊨ tv (vnat n): TNat.
  Proof. iIntros "!> * _ /="; rewrite -wp_value /pure_interp_prim /prim_evals_to; eauto. Qed.

  Lemma T_Bool_I b: Γ ⊨ tv (vlit $ lbool b): TPrim tbool.
  Proof. iIntros "!> * _ /="; rewrite -wp_value /pure_interp_prim /prim_evals_to; eauto. Qed.

  Lemma wp_un B1 Br u v
    (Hev1 : pure_interp_prim B1 v) (Hu : un_op_semtype u B1 Br) :
    WP tun u (tv v) {{ w, ⌜un_op_eval u v = Some w ∧ pure_interp_prim Br w⌝ }}%I.
  Proof.
    destruct (Hu v) => //; ev.
    by rewrite -wp_pure_step_later // -wp_value'; auto.
  Qed.

  Lemma T_Un u e1 B1 Br (Hu : un_op_semtype u B1 Br) :
    Γ ⊨ e1 : TPrim B1 -∗
    Γ ⊨ tun u e1 : TPrim Br.
  Proof.
    iIntros "#He1 !>" (ρ) "#Hg !>".
    smart_wp_bind (UnCtx _) v1 "#Ha1" ("He1" with "Hg"); iClear "He1 Hg".
    iDestruct "Ha1" as %Ha1.
    by iApply wp_wand; [iApply wp_un|iIntros (? [??])].
  Qed.

  Lemma wp_bin {b v1 v2 B1 B2 Br P} (Hu : bin_op_semtype b B1 B2 Br P) l1 l2
    (Hev1 : prim_evals_to B1 v1 l1) (Hev2 : prim_evals_to B2 v2 l2)
    (HP : P l1 l2) :
    WP tbin b (tv v1) (tv v2) {{ w, ⌜bin_op_eval b v1 v2 = Some w ∧ pure_interp_prim Br w⌝ }}%I.
  Proof.
    edestruct (Hu v1 v2) => //; ev.
    by rewrite -wp_pure_step_later // -wp_value'; auto.
  Qed.

  Lemma T_Bin b e1 e2 B1 B2 Br (Hu : bin_op_semtype b B1 B2 Br (const (const True))) :
    Γ ⊨ e1 : TPrim B1 -∗
    Γ ⊨ e2 : TPrim B2 -∗
    Γ ⊨ tbin b e1 e2 : TPrim Br.
  Proof.
    iIntros "#He1 #He2 !> /=" (ρ) "#Hg !>"; rewrite /pure_interp_prim.
    smart_wp_bind (BinLCtx _ _) v1 "#Ha1" ("He1" with "Hg"); iClear "He1".
    iDestruct "Ha1" as %Ha1.
    smart_wp_bind (BinRCtx _ _) v2 "#Ha2" ("He2" with "Hg"); iClear "He2".
    iDestruct "Ha2" as %Ha2; ev.
    by iApply wp_wand; [iApply wp_bin|iIntros (? [??])].
  Qed.

  Lemma T_Un' u e1 B1 Br (Hu : un_op_syntype u B1 Br) :
    Γ ⊨ e1 : TPrim B1 -∗
    Γ ⊨ tun u e1 : TPrim Br.
  Proof. apply T_Un, un_op_syntype_sound, Hu. Qed.

  Lemma T_Bin' b e1 e2 B1 B2 Br (Hu : bin_op_syntype b B1 B2 Br (const (const True))) :
    Γ ⊨ e1 : TPrim B1 -∗
    Γ ⊨ e2 : TPrim B2 -∗
    Γ ⊨ tbin b e1 e2 : TPrim Br.
  Proof. apply T_Bin, bin_op_syntype_sound, Hu. Qed.

  Lemma T_If e e1 e2 T :
    Γ ⊨ e : TBool -∗
    Γ ⊨ e1 : T -∗
    Γ ⊨ e2 : T -∗
    Γ ⊨ tif e e1 e2 : T.
  Proof.
    iIntros "#He #He1 #He2 !> /=" (ρ) "#Hg !>".
    smart_wp_bind (IfCtx _ _) v "#Ha" ("He" with "[]").
    iDestruct "Ha" as %([] & ->); rewrite -wp_pure_step_later //;
      [ iApply ("He1" with "Hg") | iApply ("He2" with "Hg")].
  Qed.
End Sec.
