(** * Old fundamental theorem and type safety for storeless gDOT and old unstamped gDOT. *)
From D Require Import swap_later_impl.

From D.Dot Require Export fundamental.
From D.Dot Require Export sub_lr.

From D.Dot Require Import storeless_typing path_repl_lemmas skeleton.
From D.Dot Require Import old_unstamped_typing old_unstamped_typing_to_typing.

Set Suggest Proof Using.
Set Default Proof Using "Type*".
Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms).

(* For storeless typing. *)
Section storeless_unstamped_lemmas.
  Context `{!dlangG Σ}.

  Lemma uT_ISub {Γ e T1 T2 i}:
    Γ u⊨ e : T1 -∗ Γ ⊨ T1, 0 <: T2, i -∗ Γ u⊨ iterate tskip i e : T2.
  Proof.
    iIntros "#H1 #Hsub !>"; iMod "H1" as (e1s Hsk1) "H1"; iModIntro.
    iExists (iterate tskip i e1s); iSplit; last iApply (sT_ISub with "H1 Hsub").
    eauto using same_skel_tm_tskips.
  Qed.

  Lemma suetp_var Γ x T :
    Γ su⊨ tv (ids x) : T ==∗ Γ s⊨ tv (ids x) : T.
  Proof.
    iIntros "#H1"; iMod "H1" as (e1s Hsk1) "H1".
    by rewrite (same_skel_tv_var_tv_var Hsk1).
  Qed.

  Lemma suetp_vlit Γ b T :
    Γ su⊨ tv (vlit b) : T ==∗ Γ s⊨ tv (vlit b) : T.
  Proof.
    iIntros "#H1"; iMod "H1" as (e1s Hsk1) "H1".
    by rewrite (same_skel_tv_vlit_tv_vlit Hsk1).
  Qed.

  Lemma uT_All_Ex {Γ e1 x2 T1 T2}:
    Γ u⊨ e1: TAll T1 T2 -∗ Γ u⊨ tv (ids x2) : T1 -∗ Γ u⊨ tapp e1 (tv (ids x2)) : T2.|[ids x2/].
  Proof.
    iIntros "#H1 #H2 !>"; iMod "H1" as (e1s Hsk1) "H1".
    iMod (suetp_var with "H2") as "{H2} H2"; iModIntro.
    by iExists (tapp e1s (tv (ids x2))); iSplit; last iApply (T_All_Ex with "H1 H2").
  Qed.

  Lemma suD_Typ_Sub {Γ} L1 L2 U1 U2 d l:
    Γ s⊨ L2, 0 <: L1, 0 -∗
    Γ s⊨ U1, 0 <: U2, 0 -∗
    Γ su⊨ { l := d } : cTMem l L1 U1 -∗
    Γ su⊨ { l := d } : cTMem l L2 U2.
  Proof. rewrite -!sstpd0_to_sstpi0; iApply suD_Typ_Stp. Qed.

  Lemma suD_Path_Sub {Γ T1 T2 p1 l}:
    Γ s⊨ T1, 0 <: T2, 0 -∗
    Γ su⊨ { l := dpt p1 } : cVMem l T1 -∗
    Γ su⊨ { l := dpt p1 } : cVMem l T2.
  Proof. rewrite -!sstpd0_to_sstpi0; iApply suD_Path_Stp. Qed.

  Lemma suD_Typ_Abs_I {l σ Γ L T U} (HclT : coveringσ σ V⟦ T ⟧):
    Γ s⊨ L, 0 <: oLater V⟦ T ⟧, 0 -∗
    Γ s⊨ oLater V⟦ T ⟧, 0 <: U, 0 -∗
    Γ su⊨ { l := dtysyn T } : cTMem l L U.
  Proof.
    by iIntros "H1 H2"; iApply (suD_Typ_Sub with "H1 H2"); iApply suD_Typ.
  Qed.

  Lemma uD_Typ_Abs_I {Γ T L U l n} (HclT : nclosed T n):
    Γ ⊨        L, 0 <: TLater T, 0 -∗
    Γ ⊨ TLater T, 0 <: U       , 0 -∗
    Γ u⊨ { l := dtysyn T } : TTMem l L U.
  Proof. have := !!(nclosed_syn_coveringσ HclT); apply suD_Typ_Abs_I. Qed.

  Lemma suD_Typ_dtysem {Γ l σ s fakeσ} {T : olty Σ 0} (HclT : coveringσ σ T):
    ⊢ Γ su⊨ { l := dtysem fakeσ s } : cTMem l (oLater T) (oLater T).
  Proof.
    by iApply sudtp_respects_skel_sym; last iApply (suD_Typ (fakeT := TTop)).
  Qed.

  Lemma suD_Typ_Abs_I_dtysem {Γ T L U l s σ fakeσ} (HclT : coveringσ σ T):
    Γ s⊨        L, 0 <: oLater T, 0 -∗
    Γ s⊨ oLater T, 0 <: U       , 0 -∗
    Γ su⊨ { l := dtysem fakeσ s } : cTMem l L U.
  Proof.
    by iIntros "H1 H2"; iApply (suD_Typ_Sub with "H1 H2");
      iApply suD_Typ_dtysem.
  Qed.

  Lemma uD_Typ_Abs_I_dtysem {l n Γ L T U s fakeσ} (HclT : nclosed T n):
    Γ ⊨        L, 0 <: TLater T, 0 -∗
    Γ ⊨ TLater T, 0 <:        U, 0 -∗
    Γ u⊨ { l := dtysem fakeσ s } : TTMem l L U.
  Proof. have := !!(nclosed_syn_coveringσ HclT); apply suD_Typ_Abs_I_dtysem. Qed.
End storeless_unstamped_lemmas.

Section old_fundamental.
  Context `{!dlangG Σ} `{!SwapPropI Σ}.

  (* Make proofs below more robust by opaquifying judgments. *)
  Opaque setp sdstp sdtp sptp sstpi suetp sudtp sudstp.

  Local Definition fundamental_path_typed_def Γ p T i
    (HT : Γ u⊢ₚ p : T, i) := ⊢ Γ ⊨p p : T, i.
  Local Definition fundamental_subtype_def Γ T1 i1 T2 i2
    (HT: Γ u⊢ₜ T1, i1 <: T2, i2) := ⊢ Γ ⊨ T1, i1 <: T2, i2.

  (* Reduce away the above definitions; copied from [fundamental.v] *)
  Local Ltac simpl_context := red; markUsed Σ; red_hyps_once.

  (** TODO: replace. *)
  Theorem subtype_fundamental_mut Γ :
    (∀ p T i (HT : Γ u⊢ₚ p : T, i), fundamental_path_typed_def HT) ∧
    (∀ T1 i1 T2 i2 (HT: Γ u⊢ₜ T1, i1 <: T2, i2), fundamental_subtype_def HT).
  Proof.
    apply old_pure_typing_mut_ind; clear Γ; intros; simpl_context.
      + by iApply P_Var.
      + by iApply sP_Nat_I.
      + by iApply sP_Bool_I.
      + iApply sP_Fld_E. by iApply H.
      + by iApply sP_ISub; [iApply H0|iApply H].
      + by iApply P_Mu_I; [|iApply H]; first exact: psubst_one_implies.
      + by iApply P_Mu_E; [|iApply H]; first exact: psubst_one_implies.
      + iApply sP_Fld_I. by iApply H.
      + iApply sP_Sngl_Refl. by iApply H.
      + iApply sP_Sngl_Inv. by iApply H.
      + by iApply sP_Sngl_Trans; [iApply H|iApply H0].
      + by iApply sP_Sngl_E; [iApply H|iApply H0].

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
      + by iApply sSngl_Sub_Sym; [iApply H|iApply H0].
      + iApply sSngl_Sub_Self. by iApply H.
      + iApply Mu_Sub_Mu. by iApply H.
      + iApply Mu_Sub.
      + iApply Sub_Mu.
      + by iApply All_Sub_All; [iApply H|iApply H0].
      + iApply sFld_Sub_Fld. by iApply H.
      + by iApply sTyp_Sub_Typ; [iApply H|iApply H0].
      + iApply sAnd_All_Sub_Distr.
      + iApply sAnd_Fld_Sub_Distr.
      + iApply sAnd_Typ_Sub_Distr.
      + iApply sDistr_And_Or_Sub.
      + iApply Sub_Skolem_P. by iApply H.
  Qed.

  Local Definition fundamental_typed_def Γ e T
    (HT: Γ v⊢ₜ e : T) := ⊢ Γ u⊨ e : T.
  Local Definition fundamental_dms_typed_def Γ ds T
    (HT: Γ v⊢ds ds : T) := ⊢ Γ u⊨ds ds : T.
  Local Definition fundamental_dm_typed_def Γ l d T
    (HT : Γ v⊢{ l := d } : T) := ⊢ Γ u⊨ { l := d } : T.

  Lemma fundamental_path_typed Γ p T i :
    Γ u⊢ₚ p : T, i → ⊢ Γ ⊨p p : T, i.
  Proof. apply (subtype_fundamental_mut Γ). Qed.
  Lemma fundamental_subtype Γ T1 i1 T2 i2 :
    Γ u⊢ₜ T1, i1 <: T2, i2 → ⊢ Γ ⊨ T1, i1 <: T2, i2.
  Proof. apply (subtype_fundamental_mut Γ). Qed.

  Theorem fundamental_mut Γ :
    (∀ e T (HT: Γ v⊢ₜ e : T), fundamental_typed_def HT) ∧
    (∀ ds T (HT: Γ v⊢ds ds : T), fundamental_dms_typed_def HT) ∧
    (∀ l d T (HT : Γ v⊢{ l := d } : T), fundamental_dm_typed_def HT).
  Proof.
    apply storeless_typing_mut_ind; clear Γ; intros; simpl_context.
    + by iApply uT_All_Ex; [iApply H|iApply H0].
    + by iApply uT_All_E_p; [|iApply H|iApply fundamental_path_typed].
    + by iApply uT_All_E; [iApply H|iApply H0].
    + by iApply suT_Obj_E; iApply H.
    + iApply uT_All_I_Strong; [|by iApply H].
      by apply fundamental_ctx_sub, ctx_strip_to_sub.
    + iApply suT_Obj_I. by iApply H.
    + by iApply uT_ISub; [iApply H |iApply fundamental_subtype].
    + iApply suT_Path. by iApply fundamental_path_typed.
    + by iApply uT_Un; [|iApply H].
    + by iApply uT_Bin; [| iApply H| iApply H0].
    + by iApply suT_If; [iApply H|iApply H0|iApply H1].

    + by iApply suD_Nil.
    + by iApply suD_Cons; [|iApply H|iApply H0].

    + iApply uD_Typ_Abs_I; [done|by iApply fundamental_subtype..].
    + iApply uD_Typ_Abs_I_dtysem; [done|by iApply fundamental_subtype..].
    + iApply suD_Val. by iApply H.
    + iApply suD_Path. by iApply fundamental_path_typed.
    + iApply suD_Val_New. by iApply H.
    + iApply suD_Path_Sub; [> |iApply H].
      by iApply fundamental_subtype.
  Qed.

  (** ** Old fundamental theorem for storeless gDOT.
    Only used for semantically typed examples. *)
  Lemma fundamental_typed Γ e T :
    Γ v⊢ₜ e : T → ⊢ Γ u⊨ e : T.
  Proof. apply fundamental_mut. Qed.
  Lemma fundamental_dms_typed Γ ds T :
    Γ v⊢ds ds : T → ⊢ Γ u⊨ds ds : T.
  Proof. apply fundamental_mut. Qed.
  Lemma fundamental_dm_typed Γ l d T :
    Γ v⊢{ l := d } : T → ⊢ Γ u⊨ { l := d } : T.
  Proof. apply fundamental_mut. Qed.
End old_fundamental.

Import dlang_adequacy.

(** This proves that "storeless typing" also enjoys type safety. *)
Corollary type_soundness_storeless {e T}
  (HsT: [] v⊢ₜ e : T): safe e.
Proof.
  apply: (unstamped_safety_dot_sem dlangΣ); intros.
  eapply fundamental_typed, HsT.
Qed.

(** Normalization for gDOT paths. *)
Lemma path_normalization_storeless {p T i}
  (Ht : [] u⊢ₚ p : T, i) :
  terminates (path2tm p).
Proof.
  eapply (ipwp_gs_adequacy dlangΣ); intros.
  eapply fundamental_path_typed, Ht.
Qed.

(** We also prove that the old_unstamped_typing is safe, using
fundamental theorem 5.2. *)
Corollary type_soundness_old {e T}
  (Ht : [] u⊢ₜ e : T) : safe e.
Proof. eapply type_soundness, renew_typed, Ht. Qed.

Corollary path_normalization_old p T i
  (Hp : [] u⊢ₚ p : T, i) : terminates (path2tm p).
Proof. eapply path_normalization, renew_path_typed, Hp. Qed.
