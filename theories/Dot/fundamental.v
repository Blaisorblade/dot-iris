(** * Fundamental theorem and type safety for gDOT. *)
From D Require Import swap_later_impl.
From D.Dot Require Export unary_lr later_sub_syn
  binding_lr defs_lr prims_lr path_repl_lr dsub_lr.
From D.Dot Require Export path_repl_lr_syn.
From D.Dot Require Export sem_unstamped_typing.

From D.Dot Require Import typing path_repl_lemmas.
Set Suggest Proof Using.
Set Default Proof Using "Type*".
Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

Section fundamental.
  Context `{!dlangG Σ} `{!SwapPropI Σ}.

  (* Make proofs below more robust by opaquifying judgments. *)
  Opaque setp sdstp sdtp sptp suetp sudstp.

  Definition fundamental_typed_def Γ e T (HT: Γ t⊢ₜ e : T) :=
    ⊢ Γ u⊨ e : T.
  Definition fundamental_dms_typed_def Γ ds T (HT: Γ t⊢ds ds : T) :=
    ⊢ Γ u⊨ds ds : T.
  Definition fundamental_dm_typed_def Γ l d T (HT : Γ t⊢{ l := d } : T) :=
    ⊢ Γ u⊨ { l := d } : T.
  Definition fundamental_path_typed_def Γ p T i (HT : Γ t⊢ₚ p : T, i) :=
    ⊢ Γ ⊨p p : T, i.
  Definition fundamental_subtype_def Γ i T1 T2 (HT: Γ t⊢ₜ T1 <:[i] T2) :=
    ⊢ Γ ⊨ T1 <:[ i ] T2.

  (* Reduce away the above definitions. *)
  #[local] Ltac simpl_context := red; markUsed Σ; red_hyps_once.

  Theorem subtype_fundamental_mut Γ :
    (∀ p T i (HT : Γ t⊢ₚ p : T, i), fundamental_path_typed_def HT) ∧
    (∀ i T1 T2 (HT: Γ t⊢ₜ T1 <:[i] T2), fundamental_subtype_def HT).
  Proof.
    apply pure_typing_mut_ind; clear Γ; intros; simpl_context.
    + by iApply P_Var.
    + by iApply sP_Nat_I.
    + by iApply sP_Bool_I.
    + iApply sP_Fld_E. by iApply H.
    + iApply sP_Sub; [iApply H0|iApply H].
    + by iApply sP_Later; [iApply H].
    + by iApply P_Mu_I; [|iApply H]; first exact: psubst_one_implies.
    + by iApply P_Mu_E; [|iApply H]; first exact: psubst_one_implies.
    + iApply sP_Fld_I. by iApply H.
    + iApply sP_Sngl_Refl. by iApply H.
    + iApply sP_Sngl_Inv. by iApply H.
    + by iApply sP_Sngl_Trans; [iApply H|iApply H0].
    + by iApply sP_Sngl_E; [iApply H|iApply H0].

    + by iApply sStp_Refl.
    + by iApply sStp_Trans; [iApply H|iApply H0].
    + by iApply sLater_Stp_Eq; [iApply H].
    + by iApply sLater_Stp_Eq; [iApply H].
    + by iApply sStp_Add_Later.
    + by iApply sStp_Top.
    + by iApply sBot_Stp.
    + by iApply sAnd1_Stp.
    + by iApply sAnd2_Stp.
    + by iApply sStp_And; [iApply H|iApply H0].
    + by iApply sStp_Or1.
    + by iApply sStp_Or2.
    + by iApply sOr_Stp; [iApply H|iApply H0].
    + iApply sSel_Stp; by iApply H.
    + iApply sStp_Sel; by iApply H.
    + by iApply Sngl_pq_Stp; [|iApply H].
    + by iApply sSngl_Stp_Sym; [iApply H|iApply H0].
    + iApply sSngl_Stp_Self. by iApply H.
    + iApply Mu_Stp_Mu. by iApply H.
    + iApply Mu_Stp.
    + iApply Stp_Mu.
    + by iApply All_Stp_All; [iApply H|iApply H0].
    + iApply sFld_Stp_Fld. by iApply H.
    + by iApply sTyp_Stp_Typ; [iApply H|iApply H0].
    + iApply sAnd_All_1_Stp_Distr.
    + iApply sAnd_All_2_Stp_Distr.
    + iApply sAnd_Fld_Stp_Distr.
    + iApply sAnd_Typ_Stp_Distr.
    + iApply sOr_Fld_Stp_Distr.
    + iApply sDistr_And_Or_Stp.
    + by iApply Stp_Eq.
    + by iApply Stp_Skolem_P; iApply H.
  Qed.
  Lemma fundamental_path_typed Γ p T i :
    Γ t⊢ₚ p : T, i → ⊢ Γ ⊨p p : T, i.
  Proof. apply (subtype_fundamental_mut Γ). Qed.
  Lemma fundamental_subtype Γ i T1 T2 :
    Γ t⊢ₜ T1 <:[i] T2 → ⊢ Γ ⊨ T1 <:[i] T2.
  Proof. apply (subtype_fundamental_mut Γ). Qed.

  Theorem fundamental_mut Γ :
    (∀ e T (HT: Γ t⊢ₜ e : T), fundamental_typed_def HT) ∧
    (∀ ds T (HT: Γ t⊢ds ds : T), fundamental_dms_typed_def HT) ∧
    (∀ l d T (HT : Γ t⊢{ l := d } : T), fundamental_dm_typed_def HT).
  Proof.
    apply typing_mut_ind; clear Γ; intros; simpl_context.
    + by iApply uT_All_E_p; [|iApply H|iApply fundamental_path_typed];
        first exact: psubst_one_implies.
    + by iApply uT_All_E; [iApply H|iApply H0].
    + by iApply suT_Obj_E; iApply H.
    + iApply uT_All_I_Strong; [|by iApply H].
      by apply fundamental_ctx_sub, ctx_strip_to_sub.
    + iApply suT_Obj_I. by iApply H.
    + by iApply suT_Sub; [iApply H|iApply fundamental_subtype].
    + by iApply suT_Skip; iApply H.
    + iApply suT_Path. by iApply fundamental_path_typed.
    + by iApply uT_Un; [|iApply H].
    + by iApply uT_Bin; [| iApply H| iApply H0].
    + by iApply suT_If; [iApply H|iApply H0|iApply H1].

    + by iApply suD_Nil.
    + by iApply suD_Cons; [|iApply H|iApply H0].

    + by iApply uD_Typ_Abs; [> |iApply fundamental_subtype ..].
    + iApply suD_Val. by iApply H.
    + iApply suD_Path. by iApply fundamental_path_typed.
    + iApply suD_Val_New. by iApply H.
    + iApply suD_Path_Stp; by [> iApply fundamental_subtype|iApply H].
  Qed.

  (** * Fundamental theorem 5.3. *)
  Lemma fundamental_typed Γ e T :
    Γ t⊢ₜ e : T → ⊢ Γ u⊨ e : T.
  Proof. apply (fundamental_mut Γ). Qed.
  Lemma fundamental_dms_typed Γ ds T :
    Γ t⊢ds ds : T → ⊢ Γ u⊨ds ds : T.
  Proof. apply (fundamental_mut Γ). Qed.
  Lemma fundamental_dm_typed Γ l d T :
    Γ t⊢{ l := d } : T → ⊢ Γ u⊨ { l := d } : T.
  Proof. apply (fundamental_mut Γ). Qed.
End fundamental.

(** Adequacy of our logical relation: semantically well-typed terms are safe. *)

Import dlang_adequacy.

(** The overall proof of type soundness, as outlined in Sec. 5 of the paper. *)
(** Theorem 5.2: Type soundness for gDOT. *)
Theorem type_soundness {e T}
  (Ht: [] t⊢ₜ e : T): safe e.
Proof.
  (* Apply adequacy of unstamped semantic typing (Theorem 5.4). *)
  apply: (unstamped_safety_dot_sem dlangΣ); intros.
  (* Apply fundamental theorem (Theorem 5.3). *)
  apply fundamental_typed, Ht.
Qed.

(** Normalization for gDOT paths. *)
Theorem path_normalization {p T i}
  (Ht : [] t⊢ₚ p : T, i) :
  terminates (path2tm p).
Proof.
  (* Apply adequacy of semantic path typing. *)
  apply: (ipwp_gs_adequacy dlangΣ); intros.
  apply fundamental_path_typed, Ht.
Qed.
