(** * Fundamental theorem and type safety for gDOT. *)
From D Require Import swap_later_impl.
(* For fundamental theorem. *)
From D.Dot Require Export unary_lr later_sub_sem
  binding_lr defs_lr prims_lr path_repl_lr sub_lr dsub_lr.
From D.Dot Require Import storeless_typing.
(* For unstamped safety. *)
From D.Dot Require Import old_unstamped_typing type_extraction_syn ast_stamping
  old_typing_stamping skeleton path_repl_lemmas.
From D.Dot Require Import sem_unstamped_typing.

Set Suggest Proof Using.
Set Default Proof Using "Type*".
Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx) (g : stys).

Section old_fundamental.
  Context `{!dlangG Σ} `{!SwapPropI Σ}.

  (* Make proofs below more robust by opaquifying judgments. *)
  Opaque setp sdstp sdtp sptp sstpi suetp sudtp sudstp.

  Definition fundamental_typed_def Γ g e T (HT: Γ v⊢ₜ[ g ] e : T) :=
    ⊢ Γ u⊨ e : T.
  Definition fundamental_dms_typed_def Γ g ds T (HT: Γ v⊢ds[ g ] ds : T) :=
    ⊢ Γ u⊨ds ds : T.
  Definition fundamental_dm_typed_def Γ g l d T (HT : Γ v⊢[ g ]{ l := d } : T) :=
    ⊢ Γ u⊨ { l := d } : T.

  Definition fundamental_path_typed_def Γ p T i (HT : Γ u⊢ₚ p : T, i) :=
    ⊢ Γ ⊨p p : T, i.
  Definition fundamental_subtype_def Γ T1 i1 T2 i2 (HT: Γ u⊢ₜ T1, i1 <: T2, i2) :=
    ⊢ Γ ⊨ T1, i1 <: T2, i2.

  Theorem subtype_fundamental_mut Γ :
    (∀ p T i HT, @fundamental_path_typed_def Γ p T i HT) ∧
    (∀ T1 i1 T2 i2 HT, @fundamental_subtype_def Γ T1 i1 T2 i2 HT).
  Proof.
    apply old_pure_typing_mut_ind; clear Γ; intros; red.
      + by iApply P_Var.
      + by iApply sP_Nat_I.
      + by iApply sP_Bool_I.
      + iApply P_Fld_E. by iApply H.
      + by iApply sP_Sub; [iApply H0|iApply H].
      + by iApply P_Mu_I; [|iApply H]; first exact: psubst_one_implies.
      + by iApply P_Mu_E; [|iApply H]; first exact: psubst_one_implies.
      + iApply P_Fld_I. by iApply H.
      + iApply P_Sngl_Refl. by iApply H.
      + iApply P_Sngl_Inv. by iApply H.
      + by iApply P_Sngl_Trans; [iApply H|iApply H0].
      + by iApply P_Sngl_E; [iApply H|iApply H0].

      + by iApply sSub_Refl.
      + by iApply sSub_Trans; [iApply H|iApply H0].
      + by iApply sLater_Sub.
      + by iApply sSub_Later.
      + by iApply sSub_Add_Later.
      + by iApply sSub_Top.
      + by iApply sBot_Sub.
      + by iApply sAnd1_Sub.
      + by iApply sAnd2_Sub.
      + by iApply sSub_And; [iApply H|iApply H0].
      + by iApply sSub_Or1.
      + by iApply sSub_Or2.
      + by iApply sOr_Sub; [iApply H|iApply H0].
      + iApply sSel_Sub; by iApply H.
      + iApply sSub_Sel; by iApply H.
      + by iApply Sngl_pq_Sub; [|iApply H].
      + by iApply Sngl_Sub_Sym; [iApply H|iApply H0].
      + iApply Sngl_Sub_Self. by iApply H.
      + iApply Mu_Sub_Mu. by iApply H.
      + iApply Mu_Sub.
      + iApply Sub_Mu.
      + by iApply All_Sub_All; [iApply H|iApply H0].
      + iApply Fld_Sub_Fld. by iApply H.
      + by iApply Typ_Sub_Typ; [iApply H|iApply H0].
      + iApply sAnd_All_Sub_Distr.
      + iApply sAnd_Fld_Sub_Distr.
      + iApply sAnd_Typ_Sub_Distr.
      + iApply sDistr_And_Or_Sub.
      + iApply Sub_Skolem_P. by iApply H.
  Qed.

  Lemma fundamental_path_typed Γ p T i :
    Γ u⊢ₚ p : T, i → ⊢ Γ ⊨p p : T, i.
  Proof. apply (subtype_fundamental_mut Γ). Qed.
  Lemma fundamental_subtype Γ T1 i1 T2 i2 :
    Γ u⊢ₜ T1, i1 <: T2, i2 → ⊢ Γ ⊨ T1, i1 <: T2, i2.
  Proof. apply (subtype_fundamental_mut Γ). Qed.

  Theorem fundamental_mut Γ g :
    (∀ e T HT, @fundamental_typed_def Γ g e T HT) ∧
    (∀ ds T HT, @fundamental_dms_typed_def Γ g ds T HT) ∧
    (∀ l d T HT, @fundamental_dm_typed_def Γ g l d T HT).
  Proof.
    apply storeless_typing_mut_ind; clear Γ g; intros.
    + by iApply uT_All_Ex; [iApply H|iApply H0].
    + by iApply uT_All_Ex_p; [|iApply H|iApply fundamental_path_typed].
    + by iApply uT_All_E; [iApply H|iApply H0].
    + by iApply suT_Obj_E; iApply H.
    + iApply uT_All_I_Strong; [|by iApply H].
      by apply fundamental_ctx_sub, ctx_strip_to_sub.
    + iApply suT_Obj_I. by iApply H.
    + by iApply uT_Sub; [iApply H |iApply fundamental_subtype].
    + iApply suT_Path. by iApply fundamental_path_typed.
    + by iApply uT_Un; [|iApply H].
    + by iApply uT_Bin; [| iApply H| iApply H0].
    + by iApply suT_If; [iApply H|iApply H0|iApply H1].

    + by iApply suD_Nil.
    + by iApply suD_Cons; [|iApply H|iApply H0].

        Import dsub_lr.
      + have /nclosed_syn_coveringσ HclT := extraction_closed e.
        iApply suD_Typ_Abs_dtysem; first done.
        iApply (sstpd0_to_sstpi0 _ _ V⟦ TLater T⟧);
        by iApply fundamental_subtype.
        iApply (sstpd0_to_sstpi0 _ V⟦ TLater T⟧ _);
        by iApply fundamental_subtype.
      + iApply suD_Val. by iApply H.
      + iApply suD_Path. by iApply fundamental_path_typed.
      + iApply suD_Val_New. by iApply H.
      + iApply suD_Path_Stp; [> |iApply H].
        rewrite sstpd0_to_sstpi0.
        by iApply fundamental_subtype.
      Qed.

  (** * Fundamental theorem 5.4. *)
  Lemma fundamental_typed Γ g e T :
    Γ v⊢ₜ[ g ] e : T → ⊢ Γ u⊨ e : T.
  Proof. apply fundamental_mut. Qed.
  Lemma fundamental_dms_typed Γ g ds T :
    Γ v⊢ds[ g ] ds : T → ⊢ Γ u⊨ds ds : T.
  Proof. apply fundamental_mut. Qed.
  Lemma fundamental_dm_typed Γ g l d T :
    Γ v⊢[ g ]{ l := d } : T → ⊢ Γ u⊨ { l := d } : T.
  Proof. apply fundamental_mut. Qed.
End old_fundamental.

(** Adequacy of our logical relation: semantically well-typed terms are safe. *)

Import dlang_adequacy.

(** The overall proof of type soundness, as outlined in Sec. 5 of the paper. *)
(** Combination of Thm 5.4 and 5.5, to give soundness of stamped typing.
In fact, we use the even more general storeless typing. *)
Corollary type_soundness_storeless {e T g}
  (HsT: [] v⊢ₜ[ g ] e : T): safe e.
Proof.
  (* Apply 5.5: Adequacy of semantic typing. *)
  apply: (unstamped_safety_dot_sem dlangΣ); intros.
  eapply fundamental_typed, HsT.
Qed.

(** Theorem 5.2: Type soundness for gDOT. *)
Corollary type_soundness e T :
  [] u⊢ₜ e : T → safe e.
Proof.
  (* Apply 5.3: Translation of typing derivations. *)
  intros (e_s & g & HsT & ? & Hs)%(stamp_typed ∅) ?.
  apply (same_skel_safe_equiv Hs).
  apply (type_soundness_storeless HsT).
Qed.

(** Normalization for gDOT paths. *)
Lemma path_normalization_storeless {p T i}
  (Ht : [] v⊢ₚ[ g ] p : T, i) :
  terminates (path2tm p).
Proof.
  eapply (ipwp_gs_adequacy dlangΣ); intros.
  eapply fundamental_path_typed, Ht.
Qed.

Corollary path_normalization p T i :
  [] u⊢ₚ p : T, i → terminates (path2tm p).
Proof.
  (* Apply 5.3: Translation of typing derivations. *)
  intros (g & HsT & _)%(stamp_path_typed ∅).
  apply (path_normalization_storeless HsT).
Qed.
