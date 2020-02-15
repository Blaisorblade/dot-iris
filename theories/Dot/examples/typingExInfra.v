(**
Infrastructure for examples of DOT programs using stamped and storeless typing.
*)
From stdpp Require Import strings gmap.

From D Require Import tactics.
From D.Dot Require Import syn.
From D.Dot Require Export typing_storeless exampleInfra hoas.
Export DBNotation.

Set Default Proof Using "Type".
Set Suggest Proof Using.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).
Implicit Types (g : stys).

(**********************)
(** STAMPED NOTATION **)
(**********************)
Bind Scope positive_scope with stamp.

Notation σ1 := ([] : vls).
Notation s1 := (1 %positive).

Notation σ2 := ([] : vls).
Notation s2 := (2 %positive).

Notation "'type' l = ( σ ; s )" := (l, dtysem σ s) (at level 60, l at level 50).

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

Lemma pack_extraction' g s T T' n σ :
  g !! s = Some T →
  is_stamped_ty (length σ) g T →
  is_stamped_σ n g σ →
  T' = T.|[∞ σ] →
  T' ~[ n ] (g, (s, σ)).
Proof. move => Hcl HsT Hsσ ->. exists T; split_and!; auto. Qed.

Notation styConforms' g p := (g !! pStamp p = Some (pTy p)).
Definition styConforms {nvl} g (p : preTyMem nvl) : Prop := styConforms' g p.
Arguments styConforms {_} _ !_ /.

Record TyMemStamp g p := {
  pStampTy : is_stamped_ty (length (pSubst p)) g (pTy p); pStampσ: is_stamped_σ (pNoVars p) g (pSubst p);
}.

Notation extractPreTyMem' g p := ((pTy p).|[∞ pSubst p] ~[ pNoVars p ] (g, (pStamp p, pSubst p))).
Definition extractPreTyMem g (p : stampTy): Prop := extractPreTyMem' g p.

Lemma stampTyAgree g : ∀ p, styConforms' g p → TyMemStamp g p → extractPreTyMem' g p.
Proof. move=> [s σ T n]/= Hl [/= HsT Hsσ]. exact: pack_extraction'. Qed.

(** wrappers for [hstampTy], which is more convenient for HOAS terms. *)
Definition stClose : hstampTy → stampTy := λ '(MkTy s hσ T n), (MkTy s (map hclose hσ) T n).

Definition hTyMemStamp g p := TyMemStamp g (stClose p).
Arguments hTyMemStamp _ !_ /.

Notation hextractPreTyMem' g p := (extractPreTyMem' g (stClose p)).
Definition hextractPreTyMem g (p : hstampTy) := hextractPreTyMem' g p.

Lemma hstampTyAgree g p: styConforms' g p → hTyMemStamp g p → hextractPreTyMem' g p.
Proof. intros; apply stampTyAgree => //. by destruct p. Qed.

Definition pToStys {nvl} : preTyMem nvl → stys := λ '(MkTy s σ T n), {[s:=T]}.
Definition pAddStys {nvl} : preTyMem nvl → stys → stys := λ p g, pToStys p ∪ g.
Global Arguments pAddStys {_} !_ /.

Lemma pAddStysSpec {nvl} g s σ T n :
  pAddStys (nvl := nvl) (MkTy s σ T n) g = <[s:=T]> g.
Proof. by rewrite insert_union_singleton_l. Qed.
Lemma pAddStysConforms {nvl} g p : styConforms (nvl := nvl) (pAddStys p g) p.
Proof.
  destruct p; simpl. apply /lookup_union_Some_raw /ltac:(left) /lookup_insert.
Qed.

Definition psAddStys {nvl} : stys → list (preTyMem nvl) → stys := foldr pAddStys.
(* XXX prove its correctness, or just test it via vm_compute? *)

(****************)
(** AUTOMATION **)
(****************)
(* Prevent simplification from unfolding it, basically unconditionally. *)
Arguments extraction : simpl never.

(* For performance, keep these hints local to examples *)
Hint Extern 5 => try_once extraction_weaken : core.
Hint Extern 5 (is_stamped_ty _ _ _) => try_once is_stamped_weaken_ty : core.
Hint Extern 5 (is_stamped_dm _ _ _) => try_once is_stamped_weaken_dm : core.
Hint Extern 5 (is_stamped_ty _ _ _) => progress cbn : core.
Hint Extern 5 (is_stamped_ren _ _ _ _) => progress cbn : core.

(** [tcrush] is the safest automation around. *)
Ltac tcrush := repeat first [ eassumption | reflexivity | typconstructor | stcrush ].
Ltac wtcrush := repeat first [fast_done | typconstructor | stcrush]; try solve [ done |
  first [
    (* by eauto 3 using is_stamped_TLater_n, is_stamped_ren1_ty, is_stamped_ren1_path *)
    by eauto 3 using is_stamped_ren1_ty |
    try_once extraction_weaken |
    try_once is_stamped_weaken_dm |
    try_once is_stamped_weaken_ty ]; eauto ].

Hint Extern 5 (nclosed _ _) => by solve_fv_congruence : fvc.
Hint Resolve pack_extraction : fvc.
Hint Extern 5 (is_stamped_ty _ _ _) => tcrush : fvc.
Hint Resolve pack_extraction' : fvc.
Ltac by_extcrush := by try eapply pack_extraction'; rewrite /= ?hsubst_id; eauto with fvc.

Hint Constructors typed subtype dms_typed dm_typed path_typed : core.
Remove Hints Trans_stp : core.
Hint Extern 10 => try_once Trans_stp : core.

Hint Resolve is_stamped_idsσ_ren : core.

Ltac asideLaters :=
  repeat first
    [ettrans; last (apply TLaterR_stp; tcrush)|
    ettrans; first (apply TLaterL_stp; tcrush)].

Ltac lNext := ettrans; first apply TAnd2_stp; tcrush.
Ltac lThis := ettrans; first apply TAnd1_stp; tcrush.

Ltac lookup :=
  lazymatch goal with
  | |- _ v⊢ₜ[ _ ] ?T1, _ <: ?T2, _ =>
    let T1' := eval hnf in T1 in
    match T1' with
    | (TAnd ?T11 ?T12) =>
      (* first [unify (label_of_ty T11) (label_of_ty T2); lThis | lNext] *)
      let ls := eval cbv in (label_of_ty T11, label_of_ty T2) in
      match ls with
      | (Some ?l1, Some ?l1) => lThis
      | (Some ?l1, Some ?l2) => lNext
      end
    end
  end.
Ltac ltcrush := tcrush; repeat lookup.

(*******************)
(** DERIVED RULES **)
(*******************)

Section examples_lemmas.
Context {g}.

Lemma Appv_typed' T2 {Γ e1 v2 T1 T3} :
  Γ v⊢ₜ[ g ] e1: TAll T1 T2 →                        Γ v⊢ₜ[ g ] tv v2 : T1 →
  T3 = T2.|[v2/] →
  (*────────────────────────────────────────────────────────────*)
  Γ v⊢ₜ[ g ] tapp e1 (tv v2) : T3.
Proof. intros; subst; by econstructor. Qed.

Lemma Var_typed' Γ x T1 T2 :
  Γ !! x = Some T1 →
  T2 = shiftN x T1 →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv (var_vl x) : T2.
Proof. intros; subst; tcrush. Qed.

Lemma Var0_typed Γ T :
  Γ !! 0 = Some T →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv (var_vl 0) : T.
Proof. intros; eapply Var_typed'; by rewrite ?hsubst_id. Qed.

Lemma TMuE_typed' Γ v T1 T2:
  Γ v⊢ₜ[ g ] tv v: TMu T1 →
  T2 = T1.|[v/] →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv v: T2.
Proof. intros; subst; auto. Qed.

Lemma Bind1 Γ T1 T2 i:
  is_stamped_ty (S (length Γ)) g T1 → is_stamped_ty (length Γ) g T2 →
  iterate TLater i T1 :: Γ v⊢ₜ[g] T1, i <: shift T2, i →
  Γ v⊢ₜ[g] μ T1, i <: T2, i.
Proof.
  intros Hus1 Hus2 Hsub.
  ettrans. exact: (Mu_stp_mu Hsub).
  exact: Mu_stp.
Qed.

Lemma Bind2 Γ T1 T2 i:
  is_stamped_ty (length Γ) g T1 → is_stamped_ty (S (length Γ)) g T2 →
  iterate TLater i (shift T1) :: Γ v⊢ₜ[g] shift T1, i <: T2, i →
  Γ v⊢ₜ[g] T1, i <: μ T2, i.
Proof.
  intros Hus1 Hus2 Hsub.
  ettrans; last apply (Mu_stp_mu Hsub); [exact: Stp_mu | wtcrush].
Qed.

Lemma Bind1' Γ T1 T2:
  is_stamped_ty (S (length Γ)) g T1 → is_stamped_ty (length Γ) g T2 →
  T1 :: Γ v⊢ₜ[g] T1, 0 <: shift T2, 0 →
  Γ v⊢ₜ[g] μ T1, 0 <: T2, 0.
Proof. intros; exact: Bind1. Qed.

Lemma Subs_typed_nocoerce T1 T2 {Γ e} :
  Γ v⊢ₜ[ g ] e : T1 →
  Γ v⊢ₜ[ g ] T1, 0 <: T2, 0 →
  Γ v⊢ₜ[ g ] e : T2.
Proof. rewrite -(iterate_0 tskip e). eauto. Qed.
Hint Resolve Subs_typed_nocoerce : core.

Lemma Var_typed_sub Γ x T1 T2 :
  Γ !! x = Some T1 →
  Γ v⊢ₜ[ g ] shiftN x T1, 0 <: T2, 0 →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv (var_vl x) : T2.
Proof. intros; eapply Subs_typed_nocoerce; by [exact: Var_typed|]. Qed.

Lemma Var0_typed_sub Γ T1 T2 :
  Γ !! 0 = Some T1 →
  Γ v⊢ₜ[ g ] T1, 0 <: T2, 0 →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv (var_vl 0) : T2.
Proof. intros. by eapply Var_typed_sub; [| rewrite ?hsubst_id]. Qed.

Lemma LSel_stp' Γ U {p l L i}:
  is_stamped_ty (length Γ) g L →
  Γ v⊢ₚ[ g ] p : TTMem l L U, i →
  Γ v⊢ₜ[ g ] L, i <: TSel p l, i.
Proof. intros; ettrans; last exact: (LSel_stp (p := p)); tcrush. Qed.

(** Specialization of [LSel_stp'] for convenience. *)
Lemma LSel_stp'' Γ {p l L i}:
  is_stamped_ty (length Γ) g L →
  Γ v⊢ₚ[ g ] p : TTMem l L L, i → Γ v⊢ₜ[ g ] L, i <: TSel p l, i.
Proof. apply LSel_stp'. Qed.

Lemma AddI_stp Γ T i (Hst: is_stamped_ty (length Γ) g T) :
  Γ v⊢ₜ[ g ] T, 0 <: T, i.
Proof.
  elim: i => [|n IHn]; first tcrush.
  ettrans; first apply IHn.
  ettrans; [exact: TAddLater_stp | tcrush].
Qed.

Lemma AddIB_stp Γ T U i:
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (length Γ) g U →
  Γ v⊢ₜ[ g ] T, 0 <: U, 0 →
  Γ v⊢ₜ[ g ] T, i <: U, i.
Proof.
  move => Hst Hsu Hstp; elim: i => [|n IHn]; first tcrush.
  exact: TMono_stp.
Qed.

Lemma is_stamped_pvar i n : i < n → is_stamped_path n g (pv (var_vl i)).
Proof. eauto. Qed.
Lemma is_stamped_pvars i n l : i < n → is_stamped_ty n g (pv (var_vl i) @; l).
Proof. eauto using is_stamped_pvar. Qed.

Lemma Let_typed Γ t u T U :
  Γ v⊢ₜ[ g ] t : T →
  shift T :: Γ v⊢ₜ[ g ] u : shift U →
  is_stamped_ty (length Γ) g T →
  Γ v⊢ₜ[ g ] lett t u : U.
Proof. move=> Ht Hu HsT. apply /App_typed /Ht /Lam_typed /Hu /HsT. Qed.

(* Note how we must weaken the type (or its environment) to account for the
   self-variable of the created object. *)
Definition packTV n s := (ν {@ type "A" = (shift (idsσ n); s)}).

Lemma Dty_typed T {Γ l s σ}:
  T ~[ length Γ ] (g, (s, σ)) →
  is_stamped_σ (length Γ) g σ →
  is_stamped_ty (length Γ) g T →
  Γ v⊢[ g ]{ l := dtysem σ s } : TTMem l T T.
Proof. intros. apply (dty_typed T); auto 3. Qed.

Lemma packTV_typed' s T n Γ :
  g !! s = Some T →
  is_stamped_ty n g T →
  n <= length Γ →
  Γ v⊢ₜ[ g ] tv (packTV n s) : typeEq "A" T.
Proof.
  move => Hlp HsT1 Hle; move: (Hle) (HsT1) => /le_n_S Hles /is_stamped_ren1_ty HsT2.
  move: (is_stamped_nclosed_ty HsT1) => Hcl.
  apply (Subs_typed_nocoerce (μ {@ typeEq "A" (shift T) }));
    last (ettrans; first apply: (Mu_stp _ (T := {@ typeEq "A" T })); tcrush).
  apply VObj_typed; tcrush.
  apply (Dty_typed (shift T)); simpl; eauto 2.
  eapply extraction_inf_subst, is_stamped_ren1.
  by apply /extraction_weaken /Hle /pack_extraction.
Qed.

Lemma packTV_typed s T Γ :
  g !! s = Some T →
  is_stamped_ty (length Γ) g T →
  Γ v⊢ₜ[ g ] tv (packTV (length Γ) s) : typeEq "A" T.
Proof. intros; exact: packTV_typed'. Qed.

Lemma val_LB T U Γ i v :
  is_stamped_ty (length Γ) g T →
  is_stamped_vl (length Γ) g v →
  Γ v⊢ₜ[ g ] tv v : type "A" >: T <: U →
  Γ v⊢ₜ[ g ] ▶: T, i <: (pv v @; "A"), i.
Proof. intros; apply /AddIB_stp /(LSel_stp (p := pv _)); tcrush. Qed.

Lemma is_stamped_sub_dm d s m n:
  is_stamped_sub n m g s →
  is_stamped_dm n g d →
  is_stamped_dm m g d.|[s].
Proof. apply is_stamped_sub_mut. Qed.

Lemma is_stamped_dtysem m n s T:
  g !! s = Some T →
  is_stamped_ty m g T →
  m ≤ n →
  is_stamped_dm n g (dtysem (idsσ m) s).
Proof.
  intros.
  by apply Trav1.trav_dtysem with (T' := T) (ts' := (m, g)), is_stamped_idsσ.
Qed.

Lemma packTV_LB s T n Γ i :
  g !! s = Some T →
  is_stamped_ty n g T →
  n <= length Γ →
  Γ v⊢ₜ[ g ] ▶: T, i <: (pv (packTV n s) @; "A"), i.
Proof.
  intros; apply /val_LB /packTV_typed'; wtcrush; cbn.
  eapply (is_stamped_sub_dm (dtysem _ _) (ren (+1))); trivial.
  exact: is_stamped_dtysem.
Qed.

Lemma val_UB T L Γ i v :
  is_stamped_ty (length Γ) g T →
  is_stamped_vl (length Γ) g v →
  Γ v⊢ₜ[ g ] tv v : type "A" >: L <: T →
  Γ v⊢ₜ[ g ] (pv v @; "A"), i <: ▶: T, i.
Proof. intros; eapply AddIB_stp, SelU_stp; tcrush. Qed.

Lemma packTV_UB s T n Γ i :
  is_stamped_ty n g T →
  g !! s = Some T →
  n <= length Γ →
  Γ v⊢ₜ[ g ] (pv (packTV n s) @; "A"), i <: ▶: T, i.
Proof.
  intros; apply /val_UB /packTV_typed'; wtcrush.
  eapply (is_stamped_sub_dm (dtysem _ _) (ren (+1))); trivial.
  exact: is_stamped_dtysem.
Qed.

Definition tApp Γ t s :=
  lett t (lett (tv (packTV (S (length Γ)) s)) (tapp (tv x1) (tv x0))).

Lemma typeApp_typed s Γ T U V t :
  Γ v⊢ₜ[ g ] t : TAll (type "A" >: ⊥ <: ⊤) U →
  (** This subtyping premise is needed to perform "avoidance", as in compilers
    for ML and Scala: that is, producing a type [V] that does not refer to
    variables bound by let in the expression. *)
  (∀ L, typeEq "A" (shiftN 2 T) :: L :: Γ v⊢ₜ[ g ] U.|[up (ren (+1))], 0 <: shiftN 2 V, 0) →
  is_stamped_ty (length Γ) g T →
  is_stamped_ty (S (length Γ)) g U →
  g !! s = Some (shift T) →
  Γ v⊢ₜ[ g ] tApp Γ t s : V.
Proof.
  move => Ht Hsub HsT1 HsU1 Hl; move: (HsT1) => /is_stamped_ren1_ty HsT2.
  move: (HsT2) => /is_stamped_ren1_ty HsT3.
  rewrite -hrenS in HsT3.
  eapply Let_typed; [exact: Ht| |tcrush].
  eapply Let_typed; [by apply packTV_typed| |tcrush].
  rewrite /= -!hrenS -/(typeEq _ _).

  apply /Subs_typed_nocoerce /Hsub.

  eapply Appv_typed'; first exact: Var_typed'.
  apply: Var_typed_sub; tcrush; rewrite /= hsubst_id //.
  rewrite !hsubst_comp; f_equal. autosubst.
Qed.

End examples_lemmas.

Hint Resolve is_stamped_pvar is_stamped_pvars Subs_typed_nocoerce : core.

Ltac var := exact: Var0_typed || exact: Var_typed'.
Ltac varsub := (eapply Var0_typed_sub || eapply Var_typed_sub); first done.
Ltac mltcrush := tcrush; try ((apply Bind1' || apply Bind1); tcrush); repeat lookup.
