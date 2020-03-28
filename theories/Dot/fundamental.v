From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
(* For fundamental theorem. *)
From D.Dot Require Import unary_lr typing_storeless typeExtractionSem
  lr_lemmas lr_lemmasDefs lr_lemmasNoBinding lr_lemmasTSel lr_lemmasPrim
  later_sub_sem.
(* For unstamped safety. *)
From D.Dot Require Import typing_unstamped astStamping typingStamping skeleton.
From D.Dot.lr Require Import path_repl.
Import stamp_transfer.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : ctx).

Section fundamental.
  Context `{!dlangG Σ} `{!SwapPropI Σ}.

  Local Ltac by_reflect :=
    match goal with
    | H : context [wellMappedφ] |- _ => by iApply H
    end.

  Lemma fundamental_mut Γ g :
    (∀ e T (HT: Γ v⊢ₜ[ g ] e : T), ⊢ Γ ⊨[ Vs⟦ g ⟧ ] e : T) ∧
    (∀ ds T (HT: Γ v⊢ds[ g ] ds : T), ⊢ Γ ⊨ds[ Vs⟦ g ⟧ ] ds : T) ∧
    (∀ l d T, Γ v⊢[ g ]{ l := d } : T → ⊢ Γ ⊨[ Vs⟦ g ⟧ ] { l := d } : T) ∧
    (∀ p T i (HT : Γ v⊢ₚ[ g ] p : T, i), ⊢ Γ ⊨p[ Vs⟦ g ⟧ ] p : T, i) ∧
    (∀ T1 i1 T2 i2 (HT: Γ v⊢ₜ[ g ] T1, i1 <: T2, i2),
      ⊢ Γ ⊨[ Vs⟦ g ⟧ ] T1, i1 <: T2, i2).
  Proof.
    eapply storeless_typing_mut_ind with
        (P := λ Γ g e T _,  ⊢ Γ ⊨[ Vs⟦ g ⟧ ] e : T)
        (P0 := λ Γ g ds T _,  ⊢ Γ ⊨ds[ Vs⟦ g ⟧ ] ds : T)
        (P1 := λ Γ g l d T _, ⊢ Γ ⊨[ Vs⟦ g ⟧ ] { l := d } : T)
        (P2 := λ Γ g p T i _, ⊢ Γ ⊨p[ Vs⟦ g ⟧ ] p : T, i)
        (P3 := λ Γ g T1 i1 T2 i2 _, ⊢ Γ ⊨[ Vs⟦ g ⟧ ] T1, i1 <: T2, i2);
    clear Γ g; intros; iIntros "#Hm".
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
      + by iApply T_Sub; [iApply H0|iApply H].
      + iApply T_Path. by iApply H.
      + by iApply sT_Nat_I.
      + by iApply sT_Bool_I.
      + by iApply T_Un; [|iApply H].
      + by iApply T_Bin; [| iApply H| iApply H0].
      + by iApply sT_If; [iApply H|iApply H0|iApply H1].

      (* + by_reflect. *)
      + by iApply D_Nil.
      + by iApply D_Cons; [|iApply H|iApply H0].

      + by iApply D_Typ_Abs; [> iApply H0 | iApply H|
          iApply extraction_to_leadsto_envD_equiv].
      + iApply D_Val. by iApply H.
      + iApply D_Path. by iApply H.
      + iApply D_Val_New. by iApply H.
      + iApply D_Path_Sub; by [> iApply H|iApply H0].

      + iApply P_Val. by iApply H.
      + iApply sP_Fld_E. by iApply H.
      + by iApply sP_Sub; [iApply H0|iApply H].
      + by iApply P_Mu_I; [|iApply H].
      + by iApply P_Mu_E; [|iApply H].
      + iApply P_Fld_I. by iApply H.
      + iApply P_Sngl_Refl. by iApply H.
      + iApply P_Sngl_Inv. by iApply H.
      + by iApply P_Sngl_Trans; [iApply H|iApply H0].
      + by iApply P_Sngl_E; [iApply H|iApply H0].
      (* + by_reflect. *)

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
      + iApply Sel_Sub. by iApply H.
      + iApply Sub_Sel. by iApply H.
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
      + iApply sAnd_Or_Sub_Distr.
      + iApply Sub_Skolem_P. by iApply H.
      (* + by iApply istpi_weaken_ctx_syn.
      + subst. by iApply Delay_Sub. *)
      (* + by_reflect. *)
  Qed.

  Lemma fundamental_dm_typed Γ g l d T (HT: Γ v⊢[ g ]{ l := d } : T) :
    ⊢ Γ ⊨[ Vs⟦ g ⟧ ] { l := d } : T.
  Proof. unmut_lemma (fundamental_mut Γ g). Qed.
  Lemma fundamental_dms_typed Γ g ds T (HT: Γ v⊢ds[ g ] ds : T) :
    ⊢ Γ ⊨ds[ Vs⟦ g ⟧ ] ds : T.
  Proof. unmut_lemma (fundamental_mut Γ g). Qed.
  Lemma fundamental_subtype Γ g T1 i1 T2 i2 (HT: Γ v⊢ₜ[ g ] T1, i1 <: T2, i2) :
    ⊢ Γ ⊨[ Vs⟦ g ⟧ ] T1, i1 <: T2, i2.
  Proof. unmut_lemma (fundamental_mut Γ g). Qed.
  Lemma fundamental_typed Γ g e T (HT: Γ v⊢ₜ[ g ] e : T) :
    ⊢ Γ ⊨[ Vs⟦ g ⟧ ] e : T.
  Proof. unmut_lemma (fundamental_mut Γ g). Qed.
  Lemma fundamental_path_typed Γ g p T i (HT : Γ v⊢ₚ[ g ] p : T, i) :
    ⊢ Γ ⊨p[ Vs⟦ g ⟧ ] p : T, i.
  Proof. unmut_lemma (fundamental_mut Γ g). Qed.
End fundamental.

(** Adequacy of our logical relation: semantically well-typed terms are safe. *)

Import dlang_adequacy.

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
  intros (e_s & g & HsT & ? & Hs)%(stamp_typed ∅) ?.
  apply Hs.
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
