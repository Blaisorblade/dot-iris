From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot Require Import unary_lr typing_storeless typeExtractionSem typing_unstamped
  lr_lemmas lr_lemmasDefs lr_lemmasNoBinding lr_lemmasTSel lr_lemmasPrim
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

Section restate.
  Context (Γ : ctx).

  Lemma sSub_Sel_Path L U p l i:
    Γ ⊨p p : TTMem l L U, i -∗
    Γ ⊨ TLater L, i <: TSel p l, i.
  Proof. apply Sub_Sel_Path. Qed.

  Lemma sSel_Sub_Path L U p l i:
    Γ ⊨p p : TTMem l L U, i -∗
    Γ ⊨ TSel p l, i <: TLater U, i.
  Proof. apply Sel_Sub_Path. Qed.


  Lemma sD_Typ_Abs T L U s σ l:
    Γ ⊨ TLater T, 0 <: TLater U, 0 -∗
    Γ ⊨ TLater L, 0 <: TLater T, 0 -∗
    s ↝[ σ ] V⟦ T ⟧ -∗
    Γ ⊨ { l := dtysem σ s } : TTMem l L U.
  Proof. apply D_Typ_Abs. Qed.

  Lemma sD_Typ T s σ l:
    s ↝[ σ ] V⟦ T ⟧ -∗
    Γ ⊨ { l := dtysem σ s } : TTMem l T T.
  Proof. apply D_Typ. Qed.
End restate.

  Fixpoint fundamental_dm_typed Γ g l d T (HT: Γ v⊢[ g ]{ l := d } : T) { struct HT }:
    Γ ⊨[ Vs⟦ g ⟧ ] { l := d } : T with
  fundamental_dms_typed Γ g ds T (HT: Γ v⊢ds[ g ] ds : T) { struct HT }:
    Γ ⊨ds[ Vs⟦ g ⟧ ] ds : T with
  fundamental_subtype Γ g T1 i1 T2 i2 (HT: Γ v⊢ₜ[ g ] T1, i1 <: T2, i2) { struct HT }:
    Γ ⊨[ Vs⟦ g ⟧ ] T1, i1 <: T2, i2 with
  fundamental_typed Γ g e T (HT: Γ v⊢ₜ[ g ] e : T) { struct HT }:
    Γ ⊨[ Vs⟦ g ⟧ ] e : T with
  fundamental_path_typed Γ g p T i (HT : Γ v⊢ₚ[ g ] p : T, i) { struct HT }:
    Γ ⊨p[ Vs⟦ g ⟧ ] p : T, i.
  Proof.
    - iIntros "#Hm"; induction HT.
      + iApply sD_Typ_Abs; by [> iApply fundamental_subtype .. |
          iApply extraction_to_leadsto_envD_equiv].
      + subst; iApply D_TVMem_All_I. by iApply fundamental_typed.
      + iApply D_TVMem_I. by iApply fundamental_typed.
      + iApply D_Path_TVMem_I. by iApply fundamental_path_typed.
      + iApply D_New_Mem_I. by iApply fundamental_dms_typed.
      + iApply D_TVMem_Sub; by [> iApply fundamental_subtype|].
    - iIntros "#Hm"; induction HT.
      + by iApply D_Nil.
      + iApply D_Cons; by [|iApply fundamental_dm_typed].
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
      + iApply sSel_Sub_Path. by iApply fundamental_path_typed.
      + iApply sSub_Sel_Path. by iApply fundamental_path_typed.
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
      (* + by_reflect. *)
    - iIntros "#Hm"; induction HT.
      + by iApply T_All_Ex; [apply IHHT1|apply IHHT2].
      + by iApply T_All_Ex_p; [|apply IHHT|iApply fundamental_path_typed].
      + by iApply T_All_E; [apply IHHT1|apply IHHT2].
      + by iApply T_Mem_E.
      + by iApply TMu_E.
      + by iApply T_All_I.
      + iApply T_New_I. by iApply fundamental_dms_typed.
      + by iApply TMu_I.
      + by iApply T_Nat_I.
      + by iApply T_Var.
      + by iApply T_Sub; [apply IHHT|iApply fundamental_subtype].
      + iApply P_To_E. by iApply fundamental_path_typed.
      (* + by_reflect. *)
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
      (* + by_reflect. *)
  Qed.

  Lemma ipwp_terminates {p T i}:
    [] ⊨p p : T , i ⊢ ▷^i ⌜ terminates (path2tm p) ⌝.
  Proof.
    iIntros "#H".
    iSpecialize ("H" $! ids with "[//]"); rewrite hsubst_id.
    iApply (path_wp_terminates with "H").
  Qed.
End fundamental.

(** Adequacy of our logical relation: semantically well-typed terms are safe. *)

Import dlang_adequacy adequacy.

(** Adequacy of semantic typing: not only are semantically well-typed expressions safe,
but any result value they produce also satisfies any properties that follow from their
semantic type. *)
Theorem adequacy_mapped_semtyping Σ `{!dlangPreG Σ} `{!SwapPropI Σ} e g Ψ T
  (Himpl : ∀ `(!dlangG Σ) v, ⟦ T ⟧ ids v -∗ ⌜Ψ v⌝)
  (Hlog : ∀ `(!dlangG Σ) `(!SwapPropI Σ), [] ⊨[ Vs⟦ g ⟧ ] e : T):
  ∀ σ, adequate NotStuck e σ (λ v _, Ψ v).
Proof.
  eapply (adequacy_dot_sem Σ e _ T Himpl).
  iIntros (??) "Hs"; iApply Hlog. iApply (transfer_empty with "Hs").
Qed.

(** Theorem 5.5: safety of semantic typing. Corollary of [adequacy_mapped_semtyping]. *)
Corollary safety_mapped_semtyping Σ `{!dlangPreG Σ} `{!SwapPropI Σ} e g T
  (Hlog : ∀ `(!dlangG Σ) `(!SwapPropI Σ), [] ⊨[ Vs⟦ g ⟧ ] e : T):
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

(** Normalization for gDOT paths. *)
Lemma ipwp_gs_adequacy Σ `{dlangPreG Σ} `{SwapPropI Σ} g p T i
  (Hwp : ∀ (Hdlang : dlangG Σ) `(!SwapPropI Σ), [] ⊨p[ Vs⟦ g ⟧ ] p : T , i):
  terminates (path2tm p).
Proof.
  eapply (@soundness (iResUR Σ) _ i).
  apply (bupd_plain_soundness _).
  iMod (gen_iheap_init (L := stamp) ∅) as (hG) "Hgs".
  set (DLangΣ := DLangG Σ _ hG).
  iMod (@transfer_empty _ DLangΣ Vs⟦ g ⟧ with "Hgs") as "Hgs".
  iApply ipwp_terminates.
  iApply (Hwp DLangΣ with "Hgs").
Qed.

Lemma path_normalization_storeless {g p T i}
  (Ht : [] v⊢ₚ[ g ] p : T, i) :
  terminates (path2tm p).
Proof.
  eapply (ipwp_gs_adequacy dlangΣ); intros.
  apply fundamental_path_typed, Ht.
Qed.

Corollary path_normalization p T i :
  [] u⊢ₚ p : T, i → terminates (path2tm p).
Proof.
  (* Apply 5.3: Translation of typing derivations. *)
  intros (e_s & g & HsT & Hs)%stamp_path_typed.
  apply Hs.
  apply (path_normalization_storeless HsT).
Qed.
