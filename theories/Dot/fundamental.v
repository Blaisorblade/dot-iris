From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot Require Import unary_lr typing typeExtractionSem.
From D.Dot Require Import lr_lemma lr_lemmasDefs lr_lemma_nobinding lr_lemmasTSel.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

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
    Γ ⊢ₜ e : T → allGs ∅ -∗ |==> Γ ⊨ e : T.
  Proof.
    iIntros. iApply fundamental_typed => //. by iApply transfer_empty.
  Qed.

End fundamental.

(** Adequacy of our logical relation: semantically well-typed terms are safe. *)

Import dlang_adequacy.

Theorem adequacy Σ `{HdlangG: dlangPreG Σ} `{SwapProp (iPropSI Σ)} e e' thp σ σ' T:
  (forall `{!dlangG Σ} `{!SwapProp (iPropSI Σ)}, allGs ∅ ⊢ |==> [] ⊨ e : T) →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros Hlog; eapply (adequacy _).
  iIntros (??) "Hs"; iDestruct (Hlog with "Hs") as ">#H".
  by iSpecialize ("H" $! ids with "[#//]"); rewrite hsubst_id.
Qed.

(** Instead of still assuming semantic typing, here we should assume syntactic
    typing and use the fundamental lemma. But otherwise this follows the general
    instantiation pattern, from e.g.
    https://gitlab.mpi-sws.org/iris/examples/blob/a89dc12821b63eeb9b831d21629ac55ebd601f38/theories/logrel/F_mu_ref/soundness.v#L29-39. *)
Corollary type_soundness e e' thp σ σ' T `{!stampTable}:
  [] ⊢ₜ e : T →
  rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
  is_Some (to_val e') ∨ reducible e' σ'.
Proof.
  intros; eapply (adequacy dlangΣ) => // *.
  by iApply fundamental_typed_upd.
Qed.
