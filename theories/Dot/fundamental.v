From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot Require Import unary_lr typing_storeless typeExtractionSem typing_unstamped
  lr_lemma lr_lemmasDefs lr_lemma_nobinding lr_lemmasTSel
  astStamping typingStamping skeleton.
From D.Dot.lr Require Import path_repl.
Import stamp_transfer.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

Section fundamental.
  Context `{!dlangG Σ} `{!SwapPropI Σ}.

  Local Ltac by_reflect :=
    match goal with
    | H : context [wellMappedφ] |- _ => by iApply H
    end.

  Fixpoint fundamental_dm_typed Γ g V l d T (HT: Γ |d V v⊢[ g ]{ l := d } : T) { struct HT }:
    Γ |L V ⊨[ ⟦ g ⟧g ] { l := d } : T with
  fundamental_dms_typed Γ g V ds T (HT: Γ |ds V v⊢[ g ] ds : T) { struct HT }:
    Γ |L V ⊨ds[ ⟦ g ⟧g ] ds : T with
  fundamental_subtype Γ g T1 i1 T2 i2 (HT: Γ v⊢ₜ[ g ] T1, i1 <: T2, i2) { struct HT }:
    Γ ⊨[ ⟦ g ⟧g ] T1, i1 <: T2, i2 with
  fundamental_typed Γ g e T (HT: Γ v⊢ₜ[ g ] e : T) { struct HT }:
    Γ ⊨[ ⟦ g ⟧g ] e : T with
  fundamental_path_typed Γ g p T i (HT : Γ v⊢ₚ[ g ] p : T, i) { struct HT }:
    Γ ⊨p[ ⟦ g ⟧g ] p : T, i.
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
      + by iApply Sub_singleton; [|iApply fundamental_path_typed].
      + by iApply singleton_sym_sub; [iApply fundamental_path_typed|apply IHHT].
      + iApply singleton_self_sub. by iApply fundamental_path_typed.
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
      + by_reflect.
    - iIntros "#Hm"; induction HT.
      + by iApply T_Forall_Ex; [apply IHHT1|apply IHHT2].
      + by iApply T_Forall_Ex_p; [|apply IHHT|iApply fundamental_path_typed].
      + by iApply T_Forall_E; [apply IHHT1|apply IHHT2].
      + by iApply T_Mem_E.
      + by iApply TMu_E.
      + by iApply T_Forall_I.
      + iApply T_New_I. by iApply fundamental_dms_typed.
      + by iApply TMu_I.
      + by iApply T_Nat_I.
      + by iApply T_Var.
      + by iApply T_Sub; [apply IHHT|iApply fundamental_subtype].
      + iApply P_To_E. by iApply fundamental_path_typed.
      + by_reflect.
    - iIntros "#Hm"; induction HT.
      + iApply P_Val. by iApply fundamental_typed.
      + by iApply P_DLater.
      + by iApply P_Mem_E.
      + by iApply P_Sub; [|iApply fundamental_subtype].
      + by iApply TMu_I_p; [|apply IHHT].
      + by iApply TMu_E_p; [|apply IHHT].
      + by iApply PT_Mem_I.
      + by iApply singleton_self.
      + by iApply singleton_self_inv.
      + by iApply singleton_trans; [apply IHHT1|apply IHHT2].
      + by iApply singleton_elim; [apply IHHT1|apply IHHT2].
      + by_reflect.
  Qed.
End fundamental.

(** Adequacy of our logical relation: semantically well-typed terms are safe. *)

Import dlang_adequacy adequacy.

(** Adequacy of semantic typing: not only are semantically well-typed expressions safe,
but any result value they produce also satisfies any properties that follow from their
semantic type. *)
Theorem adequacy_mapped_semtyping Σ `{!dlangPreG Σ} `{!SwapPropI Σ} e g Ψ T
  (Himpl : ∀ `(!dlangG Σ) v, ⟦ T ⟧ ids v -∗ ⌜Ψ v⌝)
  (Hlog : ∀ `(!dlangG Σ) `(!SwapPropI Σ), [] ⊨[ ⟦ g ⟧g ] e : T):
  ∀ σ, adequate NotStuck e σ (λ v _, Ψ v).
Proof.
  eapply (adequacy_dot_sem Σ e _ T Himpl).
  iIntros (??) "Hs"; iApply Hlog. iApply (transfer_empty with "Hs").
Qed.

(** Theorem 5.5: safety of semantic typing. Corollary of [adequacy_mapped_semtyping]. *)
Corollary safety_mapped_semtyping Σ `{!dlangPreG Σ} `{!SwapPropI Σ} e g T
  (Hlog : ∀ `(!dlangG Σ) `(!SwapPropI Σ), [] ⊨[ ⟦ g ⟧g ] e : T):
  safe e.
Proof.
  eapply adequate_safe, (adequacy_mapped_semtyping _ e g _ T), Hlog;
    naive_solver.
Qed.

(** The overall proof of type soundness, as outlined in Sec. 5 of the paper. *)
(** Combination of Thm 5.4 and 5.5, to give soundness of stamped typing.
In fact, we use the even more general storeless typing. *)
Corollary type_soundness_storeless {e T g}
  (HsT: [] v⊢ₜ[ g ] e : T): safe e.
Proof.
  apply: (safety_mapped_semtyping dlangΣ e g T); intros.
  apply fundamental_typed, HsT.
Qed.

(** Theorem 5.2: Type soundness for gDOT. *)
Corollary type_soundness e T :
  [] u⊢ₜ e : T → safe e.
Proof.
  (* Apply 5.3: Translation of typing derivations. *)
  intros (e_s & g & HsT & Hs)%stamp_typed.
  apply Hs.
  apply (type_soundness_storeless HsT).
Qed.
