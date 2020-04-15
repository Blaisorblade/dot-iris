(** * Fundamental theorem and type safety for gDOT. *)
From D Require Import swap_later_impl.
(* For fundamental theorem. *)
From D.Dot Require Export unary_lr later_sub_sem
  binding_lr defs_lr prims_lr path_repl_lr sub_lr.
From D.Dot Require Import storeless_typing.
(* For unstamped safety. *)
From D.Dot Require Import unstamped_typing type_extraction_syn ast_stamping typing_stamping skeleton.
Import stamp_transfer.

Set Suggest Proof Using.
Set Default Proof Using "Type*".
Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx) (g : stys).

Section fundamental.
  Context `{!dlangG Σ} `{!SwapPropI Σ}.

  Lemma extraction_to_leadsto_envD_equiv T g s σ n : T ~[ n ] (g, (s, σ)) →
    wellMappedφ Vs⟦ g ⟧ -∗ s ↝[ σ ] V⟦ T ⟧.
  Proof.
    move => [T'] [Hl] [<- [_ /is_stamped_nclosed_ty HclT]].
    iIntros "Hm". iExists V⟦ T' ⟧. iSplitR.
    - iIntros "!%" (args ρ v). exact: interp_finsubst_commute_cl.
    - iApply (wellMappedφ_apply with "Hm"). by rewrite lookup_fmap Hl.
  Qed.

  (* Make proofs below more robust. *)
  Opaque setp sdstp sdtp sptp sstpi.
  Lemma sSub_Eq' {Γ T U i j} :
    V⟦ Γ ⟧* s⊨ V⟦ T ⟧, i <: V⟦ U ⟧, j ⊣⊢
    V⟦ Γ ⟧* s⊨ V⟦ iterate TLater i T ⟧, 0 <: V⟦ iterate TLater j U ⟧, 0.
  Proof. by rewrite sSub_Eq !iterate_TLater_oLater. Qed.

  Definition fundamental_typed_def Γ g e T (HT: Γ v⊢ₜ[ g ] e : T) := ⊢ Γ ⊨[ Vs⟦ g ⟧ ] e : T.
  Definition fundamental_dms_typed_def Γ g ds T (HT: Γ v⊢ds[ g ] ds : T) := ⊢ Γ ⊨ds[ Vs⟦ g ⟧ ] ds : T.
  Definition fundamental_dm_typed_def Γ g l d T (HT : Γ v⊢[ g ]{ l := d } : T) := ⊢ Γ ⊨[ Vs⟦ g ⟧ ] { l := d } : T.
  Definition fundamental_path_typed_def Γ g p T i (HT : Γ v⊢ₚ[ g ] p : T, i) := ⊢ Γ ⊨p[ Vs⟦ g ⟧ ] p : T, i.
  Definition fundamental_subtype_def Γ g T1 T2 (HT: Γ v⊢ₜ[ g ] T1 <: T2) :=
    ⊢ Γ ⊨[ Vs⟦ g ⟧ ] T1, 0 <: T2, 0.
  Arguments fundamental_subtype_def /.

  Theorem fundamental_mut Γ g :
    (∀ e T HT, @fundamental_typed_def Γ g e T HT) ∧
    (∀ ds T HT, @fundamental_dms_typed_def Γ g ds T HT) ∧
    (∀ l d T HT, @fundamental_dm_typed_def Γ g l d T HT) ∧
    (∀ p T i HT, @fundamental_path_typed_def Γ g p T i HT) ∧
    (∀ T1 T2 HT, @fundamental_subtype_def Γ g T1 T2 HT).
  Proof.
    apply storeless_typing_mut_ind; clear Γ g; intros; iIntros "#Hm"; rewrite -1?Sub_Eq.
      + by iApply T_All_Ex; [iApply H|iApply H0].
      + by iApply T_All_Ex_p; [|iApply H|iApply H0].
      + by iApply T_All_E; [iApply H|iApply H0].
      + by iApply T_Obj_E; iApply H.
      + by iApply T_Mu_E; iApply H.
      + iApply T_All_I_Strong; [|by iApply H].
        by apply fundamental_ctx_sub, ctx_strip_to_sub.
      + iApply T_Obj_I. by iApply H.
      + iApply T_Mu_I. by iApply H.
      + by iApply T_Var.
      + by iApply T_Sub; [iApply H0| rewrite Sub_Eq; iApply H].
      + iApply T_Path. by iApply H.
      + by iApply sT_Nat_I.
      + by iApply sT_Bool_I.
      + by iApply T_Un; [|iApply H].
      + by iApply T_Bin; [| iApply H| iApply H0].
      + by iApply sT_If; [iApply H|iApply H0|iApply H1].

      + by iApply D_Nil.
      + by iApply D_Cons; [|iApply H|iApply H0].

      + by iApply D_Typ_Abs; [> iApply H | iApply H0|
          iApply extraction_to_leadsto_envD_equiv].
      + iApply D_Val. by iApply H.
      + iApply D_Path. by iApply H.
      + iApply D_Val_New. by iApply H.
      + iApply D_Path_Sub; by [> iApply H|iApply H0].

      + iApply P_Val. by iApply H.
      + iApply P_Fld_E. by iApply H.
      + by iApply sP_Sub; [iApply H0|rewrite sSub_Eq'; iApply H].
      + by iApply P_Mu_I; [|iApply H].
      + by iApply P_Mu_E; [|iApply H].
      + iApply P_Fld_I. by iApply H.
      + iApply P_Sngl_Refl. by iApply H.
      + iApply P_Sngl_Inv. by iApply H.
      + by iApply P_Sngl_Trans; [iApply H|iApply H0].
      + by iApply P_Sngl_E; [iApply H|iApply H0].

      + by iApply sSub_Refl.
      + rewrite Sub_Eq. by iApply sSub_Trans; [iApply H|iApply H0].
      + by iApply sLater_Sub.
      + by iApply sSub_Later.
      + by iApply sSub_Add_Later.
      + by iApply sSub_Top.
      + by iApply sBot_Sub.
      + by iApply sAnd1_Sub.
      + by iApply sAnd2_Sub.
      + by iApply sSub_And; rewrite sSub_Eq'; [iApply H|iApply H0].
      + by iApply sSub_Or1.
      + by iApply sSub_Or2.
      + by iApply sOr_Sub; rewrite sSub_Eq'; [iApply H|iApply H0].
      + iApply sSel_Sub; by iApply H.
      + iApply sSub_Sel; by iApply H.
      + by iApply Sngl_pq_Sub; [|iApply H].
      + by iApply Sngl_Sub_Sym; rewrite 1?Sub_Eq; [iApply H| iApply H0].
      + iApply Sngl_Sub_Self. by iApply H.
      + iApply Mu_Sub_Mu. rewrite Sub_Eq. by iApply H.
      + iApply Mu_Sub.
      + iApply Sub_Mu.
      + by iApply All_Sub_All; rewrite 1?Sub_Eq; [iApply H|iApply H0].
      + iApply Fld_Sub_Fld. rewrite Sub_Eq. by iApply H.
      + by iApply Typ_Sub_Typ; rewrite 1?Sub_Eq; [iApply H|iApply H0].
      + iApply sAnd_All_Sub_Distr.
      + iApply sAnd_Fld_Sub_Distr.
      + iApply sAnd_Typ_Sub_Distr.
      + iApply sDistr_And_Or_Sub.
      + iApply Sub_Skolem_P. by iApply H.
  Qed.

  (** * Fundamental theorem 5.4. *)
  Lemma fundamental_typed Γ g e T :
    Γ v⊢ₜ[ g ] e : T → ⊢ Γ ⊨[ Vs⟦ g ⟧ ] e : T.
  Proof. apply (fundamental_mut Γ g). Qed.
  Lemma fundamental_dms_typed Γ g ds T :
    Γ v⊢ds[ g ] ds : T → ⊢ Γ ⊨ds[ Vs⟦ g ⟧ ] ds : T.
  Proof. apply (fundamental_mut Γ g). Qed.
  Lemma fundamental_dm_typed Γ g l d T :
    Γ v⊢[ g ]{ l := d } : T → ⊢ Γ ⊨[ Vs⟦ g ⟧ ] { l := d } : T.
  Proof. apply (fundamental_mut Γ g). Qed.
  Lemma fundamental_path_typed Γ g p T i :
    Γ v⊢ₚ[ g ] p : T, i → ⊢ Γ ⊨p[ Vs⟦ g ⟧ ] p : T, i.
  Proof. apply (fundamental_mut Γ g). Qed.
  Lemma fundamental_subtype' Γ g T1 T2 :
    Γ v⊢ₜ[ g ] T1 <: T2 → ⊢ Γ ⊨[ Vs⟦ g ⟧ ] T1, 0 <: T2, 0.
  Proof. apply (fundamental_mut Γ g). Qed.

  Lemma fundamental_subtype Γ g T1 i1 T2 i2 :
    Γ v⊢ₜ[ g ] T1, i1 <: T2, i2 → ⊢ Γ ⊨[ Vs⟦ g ⟧ ] T1, i1 <: T2, i2.
  Proof. rewrite Sub_Eq. apply fundamental_subtype'. Qed.
End fundamental.

(** Adequacy of our logical relation: semantically well-typed terms are safe. *)

Import dlang_adequacy.

(** The overall proof of type soundness, as outlined in Sec. 5 of the paper. *)
(** Combination of Thm 5.4 and 5.5, to give soundness of stamped typing.
In fact, we use the even more general storeless typing. *)
Corollary type_soundness_storeless {e T g}
  (HsT: [] v⊢ₜ[ g ] e : T): safe e.
Proof.
  (* Apply 5.5: Adequacy of semantic typing. *)
  apply: (safety_mapped_semtyping dlangΣ); intros.
  apply fundamental_typed, HsT.
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
  intros (g & HsT & _)%(stamp_path_typed ∅).
  apply (path_normalization_storeless HsT).
Qed.
