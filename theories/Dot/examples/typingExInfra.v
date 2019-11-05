(**
Infrastructure for examples of DOT programs using stamped and storeless typing.
*)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn.
From D.Dot Require Export typing exampleInfra.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

(***************)
(** WEAKENING **)
(***************)
From D.Dot Require Import traversals stampingDefsCore typeExtractionSyn.

Lemma extr_dtysem_stamped {g s} σ T n :
  T ~[ n ] (g, (s, σ)) →
  is_stamped_σ n g σ →
  is_stamped_dm n g (dtysem σ s).
Proof.
  rewrite /= /extraction => -[T' [Hg [Hs [Hclσ HstT']]]].
  by apply @Trav1.trav_dtysem with (T' := T') (ts' := (length σ, g)).
Qed.

Lemma extraction_weaken m n T gsσ :
  T ~[ n ] gsσ → n <= m → T ~[ m ] gsσ.
Proof.
  move: gsσ => [g [s σ]] /= [T' ?] Hle; ev.
  exists T'; split_and!; eauto using is_stamped_weaken_σ.
Qed.

(* While other lemmas allow to produce a suitable stamp table, for examples it makes more sense to have a generic one. *)
Lemma pack_extraction g s T n σ :
  g !! s = Some T →
  is_stamped_ty n g T →
  σ = idsσ n →
  T ~[ n ] (g, (s, σ)).
Proof.
  move => Hcl Hl ->; exists T; move: (is_stamped_nclosed_ty Hl) => Hst.
  rewrite length_idsσ closed_subst_idsρ; auto.
Qed.

(****************)
(** AUTOMATION **)
(****************)
(* Prevent simplification from unfolding it, basically unconditionally. *)
Arguments extraction : simpl never.

(* For performance, keep these hints local to examples *)
Hint Extern 5 => try_once extraction_weaken : core.
Hint Extern 5 (is_stamped_ty _ _ _) => try_once is_stamped_weaken_ty : core.
Hint Extern 5 (is_stamped_dm _ _ _) => try_once is_stamped_weaken_dm : core.
Hint Extern 5 (is_stamped_ty _ _ _) => cbn : core.

Ltac typconstructor := match goal with
  | |- typed _ _ _ => constructor
  | |- dms_typed _ _ _ _ => constructor
  | |- dm_typed _ _ _ _ _ => constructor
  | |- path_typed _ _ _ _ => constructor
  | |- subtype _ _ _ _ _ => constructor
  end.
(** [tcrush] is the safest automation around. *)
Ltac tcrush := repeat typconstructor; stcrush; try solve [ done |
  first [
    try_once extraction_weaken |
    try_once is_stamped_weaken_dm |
    try_once is_stamped_weaken_ty ]; eauto ].

Hint Extern 5 (nclosed _ _) => by solve_fv_congruence : fvc.
Hint Resolve pack_extraction : fvc.
Hint Extern 5 (is_stamped_ty _ _ _) => tcrush : fvc.
Ltac by_extcrush := by auto with fvc.

Hint Constructors typed subtype dms_typed dm_typed path_typed : core.
Remove Hints Trans_stp : core.
Hint Extern 10 => try_once Trans_stp : core.

Hint Extern 5 => try_once is_stamped_mono_ty : core.

Hint Resolve is_stamped_idsσ_ren : core.

(*******************)
(** DERIVED RULES **)
(*******************)

Section examples_lemmas.
(* From D Require Import typeExtraction *)
Context `{hasStampTable: stampTable}.

Lemma Appv_typed' T2 {Γ e1 v2 T1 T3} :
  Γ ⊢ₜ e1: TAll T1 T2 →                        Γ ⊢ₜ tv v2 : T1 →
  T3 = T2.|[v2/] →
  (*────────────────────────────────────────────────────────────*)
  Γ ⊢ₜ tapp e1 (tv v2) : T3.
Proof. intros; subst; by econstructor. Qed.

Lemma Var_typed' Γ x T1 T2 :
  Γ !! x = Some T1 →
  T2 = T1.|[ren (+x)] →
  (*──────────────────────*)
  Γ ⊢ₜ tv (var_vl x) : T2.
Proof. intros; subst; tcrush. Qed.

Lemma TMuE_typed' Γ v T1 T2:
  Γ ⊢ₜ tv v: TMu T1 →
  T2 = T1.|[v/] →
  (*──────────────────────*)
  Γ ⊢ₜ tv v: T2.
Proof. intros; subst; auto. Qed.

Lemma Subs_typed_nocoerce T1 T2 {Γ e} :
  Γ ⊢ₜ e : T1 →
  Γ ⊢ₜ T1, 0 <: T2, 0 →
  Γ ⊢ₜ e : T2.
Proof. rewrite -(iterate_0 tskip e). eauto. Qed.
Hint Resolve Subs_typed_nocoerce : core.

Lemma Sub_later_shift {Γ T1 T2 i j}
  (Hs1: is_stamped_ty (length Γ) getStampTable T1)
  (Hs2: is_stamped_ty (length Γ) getStampTable T2)
  (Hsub: Γ ⊢ₜ T1, S i <: T2, S j):
  Γ ⊢ₜ TLater T1, i <: TLater T2, j.
Proof.
  eapply Trans_stp; first exact: TLaterL_stp.
  by eapply Trans_stp, TLaterR_stp.
Qed.

Lemma Sub_later_shift_inv {Γ T1 T2 i j}
  (Hs1: is_stamped_ty (length Γ) getStampTable T1)
  (Hs2: is_stamped_ty (length Γ) getStampTable T2)
  (Hsub: Γ ⊢ₜ TLater T1, i <: TLater T2, j):
  Γ ⊢ₜ T1, S i <: T2, S j.
Proof.
  eapply Trans_stp; first exact: TLaterR_stp.
  by eapply Trans_stp, TLaterL_stp.
Qed.

Lemma Var_typed_sub Γ x T1 T2 :
  Γ !! x = Some T1 →
  Γ ⊢ₜ T1.|[ren (+x)], 0 <: T2, 0 →
  (*──────────────────────*)
  Γ ⊢ₜ tv (var_vl x) : T2.
Proof. intros; eapply Subs_typed_nocoerce; by [exact: Var_typed|]. Qed.

Lemma LSel_stp' Γ U {p l L i}:
  is_stamped_ty (length Γ) getStampTable L →
  Γ ⊢ₚ p : TTMem l L U, i →
  Γ ⊢ₜ L, i <: TSel p l, i.
Proof. intros; eapply Trans_stp; last exact: (LSel_stp _ p); tcrush. Qed.

Lemma AddI_stp Γ T i (Hst: is_stamped_ty (length Γ) getStampTable T) :
  Γ ⊢ₜ T, 0 <: T, i.
Proof.
  elim: i => [|n IHn]; first tcrush.
  eapply Trans_stp; first apply IHn.
  eapply Trans_stp; [exact: TAddLater_stp | tcrush].
Qed.

Lemma AddIB_stp Γ T U i:
  Γ ⊢ₜ T, 0 <: U, 0 →
  Γ ⊢ₜ T, i <: U, i.
Proof.
  move => Hstp; elim: i => [|n IHn]; first tcrush.
  exact: TMono_stp.
Qed.

Lemma is_stamped_pvar i n : i < n → is_stamped_path n getStampTable (pv (var_vl i)).
Proof. eauto. Qed.
Lemma is_stamped_pvars i n l : i < n → is_stamped_ty n getStampTable (pv (var_vl i) @; l).
Proof. eauto using is_stamped_pvar. Qed.

Lemma Let_typed Γ t u T U :
  Γ ⊢ₜ t : T →
  T.|[ren (+1)] :: Γ ⊢ₜ u : U.|[ren (+1)] →
  is_stamped_ty (length Γ) getStampTable T →
  Γ ⊢ₜ lett t u : U.
Proof. move=> Ht Hu HsT. apply /App_typed /Ht /Lam_typed /Hu /HsT. Qed.

(* Note how we must weaken the type (or its environment) to account for the
   self-variable of the created object. *)
Definition packTV n s := (ν {@ type "A" = ((idsσ n).|[ren (+1)]; s)}).

Lemma packTV_typed' s T n Γ :
  getStampTable !! s = Some T →
  is_stamped_ty n getStampTable T →
  n <= length Γ →
  Γ ⊢ₜ tv (packTV n s) : typeEq "A" T.
Proof.
  move => Hlp HsT1 Hle; move: (Hle) (HsT1) => /le_n_S Hles /is_stamped_ren1_ty HsT2.
  move: (is_stamped_nclosed_ty HsT1) => Hcl.
  apply (Subs_typed_nocoerce (μ {@ typeEq "A" T.|[ren (+1)] }));
    last (eapply Trans_stp; first apply (Mu_stp _ ({@ typeEq "A" T })); tcrush).
  apply VObj_typed; tcrush.
  apply (dty_typed T.|[ren (+1)]); auto 2; tcrush.
  apply /(@extraction_inf_subst _ (length _)); auto 3;
    by apply /extraction_weaken /Hle /pack_extraction.
Qed.

Lemma packTV_typed s T Γ :
  getStampTable !! s = Some T →
  is_stamped_ty (length Γ) getStampTable T →
  Γ ⊢ₜ tv (packTV (length Γ) s) : typeEq "A" T.
Proof. intros; exact: packTV_typed'. Qed.

Lemma val_LB T U Γ i v :
  Γ ⊢ₜ tv v : type "A" >: T <: U →
  Γ ⊢ₜ ▶ T, i <: (pv v @; "A"), i.
Proof. intros; apply /AddIB_stp /(LSel_stp _ (pv _)); tcrush. Qed.

Lemma packTV_LB s T n Γ i :
  getStampTable !! s = Some T →
  is_stamped_ty n getStampTable T →
  n <= length Γ →
  Γ ⊢ₜ ▶ T, i <: (pv (packTV n s) @; "A"), i.
Proof. intros; by apply /val_LB /packTV_typed'. Qed.

Lemma val_UB T L Γ i v :
  Γ ⊢ₜ tv v : type "A" >: L <: T →
  Γ ⊢ₜ (pv v @; "A"), i <: ▶ T, i.
Proof. intros; eapply AddIB_stp, SelU_stp; tcrush. Qed.

Lemma packTV_UB s T n Γ i :
  is_stamped_ty n getStampTable T →
  getStampTable !! s = Some T →
  n <= length Γ →
  Γ ⊢ₜ (pv (packTV n s) @; "A"), i <: ▶ T, i.
Proof. intros; by apply /val_UB /packTV_typed'. Qed.

Definition tApp Γ t s :=
  lett t (lett (tv (packTV (S (length Γ)) s)) (tapp (tv x1) (tv x0))).

Lemma typeApp_typed s Γ T U V t :
  Γ ⊢ₜ t : TAll (type "A" >: ⊥ <: ⊤) U →
  (** This subtyping premise is needed to perform "avoidance", as in compilers
    for ML and Scala: that is, producing a type [V] that does not refer to
    variables bound by let in the expression. *)
  (∀ L, typeEq "A" T.|[ren (+2)] :: L :: Γ ⊢ₜ U.|[up (ren (+1))], 0 <: V.|[ren (+2)], 0) →
  is_stamped_ty (length Γ) getStampTable T →
  is_stamped_ty (S (length Γ)) getStampTable U →
  getStampTable !! s = Some T.|[ren (+1)] →
  Γ ⊢ₜ tApp Γ t s : V.
Proof.
  move => Ht Hsub HsT1 HsU1 Hl; move: (HsT1) => /is_stamped_ren1_ty HsT2.
  move: (HsT2) => /is_stamped_ren1_ty HsT3.
  rewrite -hrenS in HsT3.
  eapply Let_typed; [exact: Ht| |tcrush].
  eapply Let_typed; [by apply packTV_typed| |tcrush].
  rewrite /= -!hrenS -/(typeEq _ _).

  apply /Subs_typed_nocoerce /Hsub.

  eapply Appv_typed'; first exact: Var_typed'.
  apply: Var_typed_sub; repeat tcrush; rewrite /= hsubst_id //.
  rewrite !hsubst_comp; f_equal. autosubst.
Qed.

End examples_lemmas.

Hint Resolve is_stamped_pvar is_stamped_pvars Subs_typed_nocoerce : core.
