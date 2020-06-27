(** * Semantic lemmas for typing of primitive expressions. *)
From iris.proofmode Require Import tactics.
From D.Dot Require Import syn.
From D.Dot Require Import typing_aux_defs.
From D.pure_program_logic Require Import lifting.
From iris.program_logic Require Import language.

From D.Dot Require Import rules unary_lr.

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms) (n : Z).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Inductive cond_bin_op_syntype : bin_op → ∀ (B1 B2 Br : base_ty),
  (prim_sem B1 → prim_sem B2 → Prop) → Set :=
| ty_syn b B1 B2 Br : bin_op_syntype b B1 B2 Br →
                      cond_bin_op_syntype b B1 B2 Br (const (const True))
| ty_bminus         : cond_bin_op_syntype bminus tint  tint  tint  (λ n1 n2, n2 ≤ n1)%Z
| ty_bdiv           : cond_bin_op_syntype bdiv   tint  tint  tint  (λ _ n, n ≠ 0).

Definition un_op_semtype u B1 Br := ∀ v, pure_interp_prim B1 v →
  ∃ w, un_op_eval u v = Some w ∧ pure_interp_prim Br w.

Lemma un_op_syntype_sound {u B1 Br} : un_op_syntype u B1 Br → un_op_semtype u B1 Br.
Proof. rewrite /un_op_semtype /pure_interp_prim => Ht; inverse Ht; naive_solver. Qed.

Definition bin_op_semtype b B1 B2 Br (P : prim_sem B1 → prim_sem B2 → Prop) :=
  ∀ v1 v2 l1 l2,
  prim_evals_to B1 v1 l1 →
  prim_evals_to B2 v2 l2 →
  P l1 l2 →
  ∃ w, bin_op_eval b v1 v2 = Some w ∧ pure_interp_prim Br w.

Lemma bin_op_syntype_sound {b B1 B2 Br} :
  bin_op_syntype b B1 B2 Br → bin_op_semtype b B1 B2 Br (const (const True)).
Proof. rewrite /bin_op_semtype /pure_interp_prim. destruct 1; naive_solver. Qed.

Lemma cond_bin_op_syntype_sound {b B1 B2 Br P} :
  cond_bin_op_syntype b B1 B2 Br P → bin_op_semtype b B1 B2 Br P.
Proof.
  destruct 1; first exact: bin_op_syntype_sound;
    rewrite /bin_op_semtype /pure_interp_prim => *; simplify_eq/=;
    try (case_decide || case_match); naive_solver eauto with lia.
Qed.

Section Sec.
  Context `{HdlangG: !dlangG Σ}.

  Import path_wp.
  Lemma sP_Nat_I Γ n: ⊢ Γ s⊨p pv (vint n): oInt, 0.
  Proof.
    iIntros "!> %ρ * _ /=";
      rewrite path_wp_pv_eq /= /pure_interp_prim /prim_evals_to; naive_solver.
  Qed.

  Lemma sP_Bool_I Γ b: ⊢ Γ s⊨p pv (vbool b): oBool, 0.
  Proof.
    iIntros "!> %ρ _ /=";
      rewrite path_wp_pv_eq /= /pure_interp_prim /prim_evals_to; naive_solver.
  Qed.

  (** ** Unary operations *)
  Lemma wp_un B1 Br u v
    (Hev1 : pure_interp_prim B1 v) (Hu : un_op_semtype u B1 Br) :
    ⊢ WP tun u (tv v) {{ w, ⌜un_op_eval u v = Some w ∧ pure_interp_prim Br w⌝ }}.
  Proof.
    destruct (Hu v) => //; ev.
    by wp_pure; auto.
  Qed.

  Lemma sT_Un Γ u e1 B1 Br (Hu : un_op_semtype u B1 Br) :
    Γ s⊨ e1 : oPrim B1 -∗
    Γ s⊨ tun u e1 : oPrim Br.
  Proof.
    iIntros ">He1 !> %ρ Hg /=".
    wp_bind (UnCtx _); wp_wapply "(He1 Hg)"; iIntros "%v1 %Ha1 /=".
    by iApply wp_wand; [iApply wp_un|iIntros (? [??])].
  Qed.

  Lemma T_Un Γ u e1 B1 Br (Hu : un_op_syntype u B1 Br) :
    Γ ⊨ e1 : TPrim B1 -∗
    Γ ⊨ tun u e1 : TPrim Br.
  Proof. apply sT_Un, un_op_syntype_sound, Hu. Qed.

  (** ** Binary operations *)
  Lemma wp_bin {b v1 v2 B1 B2 Br P} (Hu : bin_op_semtype b B1 B2 Br P) l1 l2
    (Hev1 : prim_evals_to B1 v1 l1) (Hev2 : prim_evals_to B2 v2 l2)
    (HP : P l1 l2) :
    ⊢ WP tbin b (tv v1) (tv v2) {{ w, ⌜bin_op_eval b v1 v2 = Some w ∧ pure_interp_prim Br w⌝ }}.
  Proof.
    edestruct (Hu v1 v2) => //; ev.
    by wp_pure; auto.
  Qed.

  Lemma sT_Bin Γ b e1 e2 B1 B2 Br (Hu : bin_op_semtype b B1 B2 Br (const (const True))) :
    Γ s⊨ e1 : oPrim B1 -∗
    Γ s⊨ e2 : oPrim B2 -∗
    Γ s⊨ tbin b e1 e2 : oPrim Br.
  Proof.
    iIntros ">He1 >He2 !> /= %ρ #Hg".
    wp_bind (BinLCtx _ _); wp_wapply "(He1 Hg)"; iIntros "%v1 %Ha1 /=".
    wp_bind (BinRCtx _ _); wp_wapply "(He2 Hg)"; iIntros "{Hg} %v2 %Ha2 /=".
    unfold pure_interp_prim in *; ev.
    by iApply wp_wand; [iApply wp_bin|iIntros (? [??])].
  Qed.

  Lemma sT_Bin_cond Γ b e1 e2 B1 B2 Br (Hu : cond_bin_op_syntype b B1 B2 Br (const (const True))) :
    Γ s⊨ e1 : oPrim B1 -∗
    Γ s⊨ e2 : oPrim B2 -∗
    Γ s⊨ tbin b e1 e2 : oPrim Br.
  Proof. apply sT_Bin, cond_bin_op_syntype_sound, Hu. Qed.

  Lemma T_Bin Γ b e1 e2 B1 B2 Br (Hu : bin_op_syntype b B1 B2 Br) :
    Γ ⊨ e1 : TPrim B1 -∗
    Γ ⊨ e2 : TPrim B2 -∗
    Γ ⊨ tbin b e1 e2 : TPrim Br.
  Proof. apply sT_Bin_cond, ty_syn, Hu. Qed.

  Lemma sT_If Γ e e1 e2 T :
    Γ s⊨ e : oBool -∗ Γ s⊨ e1 : T -∗ Γ s⊨ e2 : T -∗
    Γ s⊨ tif e e1 e2 : T.
  Proof.
    iIntros ">He >He1 >He2 !> /= %ρ #Hg".
    wp_bind (IfCtx _ _); wp_wapply "(He Hg)".
    rewrite /=/pure_interp_prim/=; iIntros (v (b & ->)).
    case: b; wp_pure; [iApply ("He1" with "Hg") | iApply ("He2" with "Hg")].
  Qed.
End Sec.
