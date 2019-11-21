From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot Require Import unary_lr typing typeExtractionSem typing_unstamped
  lr_lemma lr_lemmasDefs lr_lemma_nobinding lr_lemmasTSel
  astStamping typingStamping skeleton.
From D.Dot.lr Require Import path_repl.
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

  Lemma fundamental_typing_mut Γ:
    (∀ e T, Γ ⊢ₜ e : T → Γ ⊨[ ⟦ getStampTable ⟧g ] e : T) ∧
    (∀ V ds T, Γ |ds V ⊢ ds : T →
    Γ |L V ⊨[ ⟦ getStampTable ⟧g ]ds ds : T) ∧
    (∀ V l d T, Γ |d V ⊢{ l := d } : T →
      Γ |L V ⊨[ ⟦ getStampTable ⟧g ] { l := d } : T) ∧
    (∀ p T i, Γ ⊢ₚ p : T , i → Γ ⊨[ ⟦ getStampTable ⟧g ]p p : T, i) ∧
    (∀ T1 i1 T2 i2, Γ ⊢ₜ T1, i1 <: T2, i2 → Γ ⊨[ ⟦ getStampTable ⟧g ] T1, i1 <: T2, i2).
  Proof.
    apply stamped_typing_mut_ind with
        (P := λ Γ e T _, Γ ⊨[ ⟦ getStampTable ⟧g ] e : T)
        (P0 := λ Γ V ds T _, Γ |L V ⊨[ ⟦ getStampTable ⟧g ]ds ds : T)
        (P1 := λ Γ V l d T _, Γ |L V ⊨[ ⟦ getStampTable ⟧g ] { l := d } : T)
        (P2 := λ Γ p T i _, Γ ⊨[ ⟦ getStampTable ⟧g ]p p : T, i)
        (P3 := λ Γ T1 i1 T2 i2 _, Γ ⊨[ ⟦ getStampTable ⟧g ] T1, i1 <: T2, i2);
        clear Γ; intros; iIntros "#Hm".

    - iApply T_Forall_Ex; by [> iApply H|iApply H0].
    - iApply T_Forall_Ex_p; by [>|iApply H | iApply H0].
    - iApply T_Forall_E; by [>iApply H|iApply H0].
    - iApply T_Mem_E. by iApply H.
    - iApply TMu_E. by iApply H.
    - iApply T_Forall_I. by iApply H.
    - iApply T_New_I. by iApply H.
    - iApply TMu_I. by iApply H.
    - iApply T_Nat_I.
    - by iApply T_Var.
    - iApply T_Sub; by [> iApply H0|iApply H].
    - iApply P_To_E. by iApply H.
    - iApply TAnd_I; by [> iApply H|iApply H0].

    - by iApply DNil_I.
    - iApply DCons_I; by [> | iApply H | iApply H0].

    - iApply D_Typ_Abs; by [> iApply H0 | iApply H |
        iApply extraction_to_leadsto_envD_equiv].
    - iApply TVMem_All_I. by iApply H.
    - iApply TVMem_I. by iApply H.
    - iApply TVMem_Sub; by [> iApply H|iApply H0].

    - iApply P_Val. by iApply H.
    - iApply P_DLater. by iApply H.
    - iApply P_Mem_E. by iApply H.
    - iApply P_Sub; by [> iApply H0|iApply H].
    - iApply TMu_I_p; by [>|iApply H].
    - iApply TMu_E_p; by [>|iApply H].
    - iApply PT_Mem_I. by iApply H.
    - iApply PTAnd_I; by [> iApply H|iApply H0].
    - iApply singleton_self. by iApply H.
    - iApply singleton_sym. by iApply H.
    - iApply singleton_trans; by [>iApply H|iApply H0].
    - iApply singleton_elim; by [>iApply H|iApply H0].

    - by iApply Sub_Refl.
    - by iApply Sub_Trans; [iApply H|iApply H0].
    - by iApply Later_Sub.
    - by iApply Sub_Later.
    - by iApply Sub_Add_Later.
    - iApply Sub_Index_Incr. by iApply H.
    - by iApply Sub_Top.
    - by iApply Bot_Sub.
    - by iApply And1_Sub.
    - by iApply And2_Sub.
    - iApply Sub_And; by [> iApply H|iApply H0].
    - by iApply Sub_Or1.
    - by iApply Sub_Or2.
    - iApply Or_Sub; by [> iApply H|iApply H0].
    - iApply Sel_Sub_Path. by iApply H.
    - iApply Sub_Sel_Path. by iApply H.
    - iApply Sub_singleton; by [> |iApply H].
    - iApply Sub_Mu_X. by iApply H.
    - iApply Sub_Mu_A.
    - iApply Sub_Mu_B.
    - iApply Sub_Later_Sub. by iApply H.
    - iApply Sub_TAllConCov; by [> iApply H|iApply H0].
    - iApply Sub_TVMem_Variant. by iApply H.
    - iApply Sub_TTMem_Variant; by [> iApply H|iApply H0].
    - iApply Sub_TAll_Cov_Distr.
    - iApply Sub_TVMem_Cov_Distr.
    - iApply Sub_TTMem_Cov_Distr.
  Qed.

  Lemma fundamental_typed Γ e T (HT: Γ ⊢ₜ e : T) :
    Γ ⊨[ ⟦ getStampTable ⟧g ] e : T.
  Proof. destruct (fundamental_typing_mut Γ) as [H _]; apply H, HT. Qed.
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

Corollary type_soundness_storeless e T `{!stampTable}:
  [] ⊢ₜ e : T → safe e.
Proof.
  intros; apply: (adequacy_mapped_semtyping dlangΣ) => *. exact: fundamental_typed.
Qed.

Theorem type_soundness e T :
  [] u⊢ₜ e : T → safe e.
Proof.
  intros (e_s & g & HsT & Hs)%stamp_typed.
  eapply Hs, type_soundness_storeless, HsT.
Qed.
