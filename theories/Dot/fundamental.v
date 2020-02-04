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
      + iApply D_Typ_Abs; by [> iApply fundamental_subtype .. |
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
      + by iApply sSub_Refl.
      + by iApply sSub_Trans; [apply IHHT1|apply IHHT2].
      + by iApply sLater_Sub.
      + by iApply sSub_Later.
      + by iApply sSub_Add_Later.
      + by iApply sSub_Index_Incr.
      + by iApply sSub_Top.
      + by iApply sBot_Sub.
      + by iApply sAnd1_Sub.
      + by iApply sAnd2_Sub.
      + by iApply sSub_And.
      + by iApply sSub_Or1.
      + by iApply sSub_Or2.
      + by iApply sOr_Sub.
      + iApply Sel_Sub_Path. by iApply fundamental_path_typed.
      + iApply Sub_Sel_Path. by iApply fundamental_path_typed.
      + by iApply Sngl_pq_Sub; [|iApply fundamental_path_typed].
      + by iApply Sngl_Sym_Sub; [iApply fundamental_path_typed|apply IHHT].
      + iApply Sngl_Self_Sub. by iApply fundamental_path_typed.
      + by iApply Sub_Mu_X.
      + iApply Sub_Mu_A.
      + iApply Sub_Mu_B.
      + by iApply sSub_Later_Sub.
      + by iApply All_Sub_All.
      + by iApply Fld_Sub_Fld.
      + by iApply Typ_Sub_Typ.
      + iApply sSub_TAll_Cov_Distr.
      + iApply sSub_TVMem_Cov_Distr.
      + iApply sSub_TTMem_Cov_Distr.
      (* + by_reflect. *)
    - iIntros "#Hm"; induction HT.
      + by iApply T_All_Ex; [apply IHHT1|apply IHHT2].
      + by iApply T_All_Ex_p; [|apply IHHT|iApply fundamental_path_typed].
      + by iApply T_All_E; [apply IHHT1|apply IHHT2].
      + by iApply T_Obj_E.
      + by iApply T_Mu_E.
      + by iApply T_All_I.
      + iApply T_Obj_I. by iApply fundamental_dms_typed.
      + by iApply T_Mu_I.
      + by iApply T_Nat_I.
      + by iApply T_Var.
      + by iApply T_Sub; [apply IHHT|iApply fundamental_subtype].
      + iApply T_Path. by iApply fundamental_path_typed.
      (* + by_reflect. *)
    - iIntros "#Hm"; induction HT.
      + iApply P_Val. by iApply fundamental_typed.
      + by iApply sP_Later.
      + by iApply sP_Fld_E.
      + by iApply sP_Sub; [|iApply fundamental_subtype].
      + by iApply P_Mu_I; [|apply IHHT].
      + by iApply P_Mu_E; [|apply IHHT].
      + by iApply P_Fld_I.
      + by iApply P_Sngl_Refl.
      + by iApply P_Sngl_Inv.
      + by iApply P_Sngl_Trans; [apply IHHT1|apply IHHT2].
      + by iApply P_Sngl_E; [apply IHHT1|apply IHHT2].
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
Theorem adequacy_mapped_semtyping Σ `{!dlangPreG Σ} `{!SwapPropI Σ} {e g Ψ T}
  (Himpl : ∀ `(!dlangG Σ) v, ⟦ T ⟧ ids v -∗ ⌜Ψ v⌝)
  (Hlog : ∀ `(!dlangG Σ) `(!SwapPropI Σ), [] ⊨[ Vs⟦ g ⟧ ] e : T):
  ∀ σ, adequate NotStuck e σ (λ v _, Ψ v).
Proof.
  eapply (adequacy_dot_sem Σ Himpl).
  iIntros (??) "Hs"; iApply Hlog. iApply (transfer_empty with "Hs").
Qed.

(** Theorem 5.5: safety of semantic typing. Corollary of [adequacy_mapped_semtyping]. *)
Corollary safety_mapped_semtyping Σ `{!dlangPreG Σ} `{!SwapPropI Σ} {e g T}
  (Hlog : ∀ `(!dlangG Σ) `(!SwapPropI Σ), [] ⊨[ Vs⟦ g ⟧ ] e : T):
  safe e.
Proof.
  eapply adequate_safe, adequacy_mapped_semtyping, Hlog;
    naive_solver.
Qed.

(** The overall proof of type soundness, as outlined in Sec. 5 of the paper. *)
(** Combination of Thm 5.4 and 5.5, to give soundness of stamped typing.
In fact, we use the even more general storeless typing. *)
Corollary type_soundness_storeless {e T g}
  (HsT: [] v⊢ₜ[ g ] e : T): safe e.
Proof.
  apply: (safety_mapped_semtyping dlangΣ); intros.
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
Lemma ipwp_gs_adequacy Σ `{dlangPreG Σ} `{SwapPropI Σ} {g p T i}
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
