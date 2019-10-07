From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot Require Import unary_lr typing typeExtractionSem typing_unstamped
  lr_lemma lr_lemmasDefs lr_lemma_nobinding lr_lemmasTSel
  astStamping typingStamping skeleton.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

Set Implicit Arguments.

Section fundamental.
  Context `{!dlangG Σ} `{!SwapProp (iPropSI Σ)}.
  Context `{hasStampTable: stampTable}.

  Lemma fundamental_dm_typed Γ V l d T (HT: Γ |d V ⊢{ l := d } : T):
    wellMapped getStampTable -∗ Γ |L V ⊨d{ l := d } : T with
  fundamental_dms_typed Γ V ds T (HT: Γ |ds V ⊢ ds : T):
    wellMapped getStampTable -∗ Γ |L V ⊨ds ds : T with
  fundamental_subtype Γ T1 i1 T2 i2 (HT: Γ ⊢ₜ T1, i1 <: T2, i2):
    wellMapped getStampTable -∗ Γ ⊨ [T1, i1] <: [T2, i2] with
  fundamental_typed Γ e T (HT: Γ ⊢ₜ e : T):
    wellMapped getStampTable -∗ Γ ⊨ e : T with
  fundamental_path_typed Γ p T i (HT : Γ ⊢ₚ p : T, i):
    wellMapped getStampTable -∗ Γ ⊨p p : T, i.
  Proof.
    - iIntros "#Hm"; iInduction HT as [] "IHT".
      + iApply D_Typ; by [> iApply fundamental_subtype .. |
          iApply extraction_to_leadsto_envD_equiv].
      + iApply TVMem_I. by iApply fundamental_typed.
    - iIntros "#Hm"; iInduction HT as [] "IHT".
      + by iApply DNil_I.
      + iApply DCons_I; by [|iApply fundamental_dm_typed].
    - iIntros "#Hm"; iInduction HT as [] "IHT".
      + by iApply Sub_Refl.
      + by iApply Sub_Trans.
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
    - iIntros "#Hm"; iInduction HT as [] "IHT".
      + by iApply T_Forall_Ex.
      + by iApply T_Forall_E.
      + by iApply T_Mem_E.
      + by iApply TMu_E.
      + by iApply T_Forall_I.
      + iApply T_New_I. by iApply fundamental_dms_typed.
      + by iApply TMu_I.
      + by iApply T_Nat_I.
      + by iApply T_Var.
      + iApply T_Sub; by [|iApply fundamental_subtype].
      + by iApply TAnd_I.
    - iIntros "#Hm"; iInduction HT as [] "IHT".
      + iApply P_Val. by iApply fundamental_typed.
      + by iApply P_DLater.
      + by iApply P_Mem_E.
      + iApply P_Sub; by [|iApply fundamental_subtype].
  Qed.

  Lemma fundamental_typed_upd Γ e T :
    Γ ⊢ₜ e : T → allGs ∅ ==∗ Γ ⊨ e : T.
  Proof.
    iIntros (HuT) "?". iApply (fundamental_typed HuT). by iApply transfer_empty.
  Qed.
End fundamental.

(** Adequacy of our logical relation: semantically well-typed terms are safe. *)

Import dlang_adequacy.

Definition safe e :=
  ∀ e' thp σ σ', rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
    is_Some (to_val e') ∨ reducible e' σ'.

Theorem adequacy Σ `{HdlangG: dlangPreG Σ} `{SwapProp (iPropSI Σ)} e T:
  (∀ `{!dlangG Σ} `{!SwapProp (iPropSI Σ)}, allGs ∅ ⊢ |==> [] ⊨ e : T) →
  safe e.
Proof.
  intros Hlog ?*; eapply (adequacy _).
  iIntros (??) "Hs". iDestruct (Hlog with "Hs") as ">#Ht".
  by iSpecialize ("Ht" $! ids with "[#// ]"); rewrite hsubst_id.
Qed.

(** Instead of still assuming semantic typing, here we should assume syntactic
    typing and use the fundamental lemma. But otherwise this follows the general
    instantiation pattern, from e.g.
    https://gitlab.mpi-sws.org/iris/examples/blob/a89dc12821b63eeb9b831d21629ac55ebd601f38/theories/logrel/F_mu_ref/soundness.v#L29-39. *)
Corollary type_soundness_stamped e T `{!stampTable}:
  [] ⊢ₜ e : T → safe e.
Proof.
  intros; apply: (@adequacy dlangΣ _ _)=>*. exact: fundamental_typed_upd.
Qed.

Lemma safe_same_skel e e_s:
  same_skel_tm e e_s → safe e_s → safe e.
Proof.
  rewrite /safe; intros Hst Hsafe * Hred Hin.
  destruct (simulation_skeleton_erased_steps Hst Hred Hin)
    as (e_s' & Hst_s & Hskel').
  edestruct Hsafe; [apply Hst_s|apply elem_of_list_here|left|right].
  - destruct e_s', e'; naive_solver.
  - exact: same_skel_reducible.
Qed.

Lemma safe_stamp n e g e_s:
  stamps_tm n e g e_s → safe e_s → safe e.
Proof. move => [/unstamp_same_skel_tm Hs _] Hsafe. exact: safe_same_skel. Qed.

Theorem type_soundness e T :
  [] u⊢ₜ e : T → safe e.
Proof.
  intros (e_s & g & HsT & Hs)%stamp_typed.
  eapply (safe_stamp Hs), type_soundness_stamped, HsT.
Qed.
