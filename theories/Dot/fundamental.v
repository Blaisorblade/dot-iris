From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot Require Import unary_lr typing typeExtractionSem typing_unstamped
  lr_lemma lr_lemmasDefs lr_lemma_nobinding lr_lemmasTSel
  astStamping typingStamping skeleton.
Import stamp_transfer.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

(** Single-definition typing *)
Notation "Γ ⊨[ gφ  ] { l := d  } : T" := (wellMappedφ gφ -∗ idtp Γ T l d)%I (at level 74, d, l, T at next level).
(** Multi-definition typing *)
Notation "Γ ⊨[ gφ  ]ds ds : T" := (wellMappedφ gφ -∗ idstp Γ T ds)%I (at level 74, ds, T at next level).
(** Expression typing *)
Notation "Γ ⊨[ gφ  ] e : T" := (wellMappedφ gφ -∗ ietp Γ T e)%I (at level 74, e, T at next level).
Notation "Γ ⊨[ gφ  ]p p : T , i" := (wellMappedφ gφ -∗ iptp Γ T p i)%I (at level 74, p, T, i at next level).
Notation "Γ ⊨[ gφ  ] T1 , i <: T2 , j" := (wellMappedφ gφ -∗ step_indexed_ivstp Γ T1 T2 i j)%I (at level 74, T1, T2, i, j at next level).

Section fundamental.
  Context `{!dlangG Σ} `{!SwapPropI Σ}.
  Context `{hasStampTable: stampTable}.

  Lemma fundamental_dm_typed Γ V l d T (HT: Γ |d V ⊢{ l := d } : T):
    Γ |L V ⊨[ ⟦ getStampTable ⟧g ] { l := d } : T with
  fundamental_dms_typed Γ V ds T (HT: Γ |ds V ⊢ ds : T):
    Γ |L V ⊨[ ⟦ getStampTable ⟧g ]ds ds : T with
  fundamental_subtype Γ T1 i1 T2 i2 (HT: Γ ⊢ₜ T1, i1 <: T2, i2):
    Γ ⊨[ ⟦ getStampTable ⟧g ] T1, i1 <: T2, i2 with
  fundamental_typed Γ e T (HT: Γ ⊢ₜ e : T):
    Γ ⊨[ ⟦ getStampTable ⟧g ] e : T with
  fundamental_path_typed Γ p T i (HT : Γ ⊢ₚ p : T, i):
    Γ ⊨[ ⟦ getStampTable ⟧g ]p p : T, i.
  Proof.
    - iIntros "#Hm"; induction HT.
      + iApply D_Typ_Abs; by [> iApply fundamental_subtype .. |
          iApply extraction_to_leadsto_envD_equiv].
      + iApply TVMem_All_I. by iApply fundamental_typed.
      + iApply TVMem_I. by iApply fundamental_typed.
      + iApply TVMem_Sub; by [> iApply fundamental_subtype|].
    - iIntros "#Hm"; induction HT.
      + by iApply DNil_I.
      + iApply DCons_I; by [|iApply fundamental_dm_typed].
    - iIntros "#Hm"; induction HT.
      + by iApply Sub_Refl.
      + by iApply Sub_Trans; [apply IHHT1|apply IHHT2].
      + by iApply Later_Sub.
      + by iApply Sub_Later.
      + by iApply Sub_Add_Later.
      + by iApply Sub_Index_Incr.
      + by iApply Sub_Top.
      + by iApply Bot_Sub.
      + by iApply And1_Sub.
      + by iApply And2_Sub.
      + by iApply Sub_And.
      + by iApply Sub_Or1.
      + by iApply Sub_Or2.
      + by iApply Or_Sub.
      + iApply Sel_Sub_Path. by iApply fundamental_path_typed.
      + iApply Sub_Sel_Path. by iApply fundamental_path_typed.
      + by iApply Sub_Mu_X.
      + iApply Sub_Mu_A.
      + iApply Sub_Mu_B.
      + by iApply Sub_Later_Sub.
      + by iApply Sub_TAllConCov.
      + by iApply Sub_TVMem_Variant.
      + by iApply Sub_TTMem_Variant.
      + iApply Sub_TAll_Cov_Distr.
      + iApply Sub_TVMem_Cov_Distr.
      + iApply Sub_TTMem_Cov_Distr.
    - iIntros "#Hm"; induction HT.
      + by iApply T_Forall_Ex; [apply IHHT1|apply IHHT2].
      + by iApply T_Forall_E; [apply IHHT1|apply IHHT2].
      + by iApply T_Mem_E.
      + by iApply TMu_E.
      + by iApply T_Forall_I.
      + iApply T_New_I. by iApply fundamental_dms_typed.
      + by iApply TMu_I.
      + by iApply T_Nat_I.
      + by iApply T_Var.
      + iApply T_Sub; by [apply IHHT|iApply (fundamental_subtype with "Hm")].
      + by iApply TAnd_I.
    - iIntros "#Hm"; induction HT.
      + iApply P_Val. by iApply fundamental_typed.
      + by iApply P_DLater.
      + by iApply P_Mem_E.
      + iApply P_Sub; by [|iApply fundamental_subtype].
  Qed.
End fundamental.

(** Adequacy of our logical relation: semantically well-typed terms are safe. *)

Import dlang_adequacy.

Theorem adequacy_mapped_semtyping Σ `{HdlangG: dlangPreG Σ} `{SwapPropI Σ} e g T:
  (∀ `{dlangG Σ} `(!SwapPropI Σ), [] ⊨[ ⟦ g ⟧g ] e : T) →
  safe e.
Proof.
  intros Hlog ?*; eapply (adequacy_dot_sem _).
  iIntros (??) "Hs"; iApply Hlog. by iApply transfer_empty.
Qed.

Corollary type_soundness_stamped e T `{!stampTable}:
  [] ⊢ₜ e : T → safe e.
Proof.
  intros; apply: (adequacy_mapped_semtyping dlangΣ) => *. exact: fundamental_typed.
Qed.

Lemma safe_same_skel {e e_s}:
  same_skel_tm e e_s → safe e_s → safe e.
Proof.
  rewrite /safe; intros Hst Hsafe * Hred Hin.
  destruct (simulation_skeleton_erased_steps Hst Hred Hin)
    as (e_s' & Hst_s & Hskel').
  edestruct Hsafe; [apply Hst_s|apply elem_of_list_here|left|right].
  - destruct e_s', e'; naive_solver.
  - exact: same_skel_reducible.
Qed.

Lemma safe_stamp {n e g e_s}:
  stamps_tm n e g e_s → safe e_s → safe e.
Proof. move => [/unstamp_same_skel_tm Hs _] Hsafe. exact: safe_same_skel. Qed.

Theorem type_soundness e T :
  [] u⊢ₜ e : T → safe e.
Proof.
  intros (e_s & g & HsT & Hs)%stamp_typed.
  eapply (safe_stamp Hs), type_soundness_stamped, HsT.
Qed.
