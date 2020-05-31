(**
Infrastructure for examples of DOT programs using stamped and storeless typing.
*)
From stdpp Require Import strings gmap.

From D Require Import tactics.
From D.Dot Require Import syn.
From D.Dot Require Export storeless_typing ex_utils hoas old_subtyping_derived_rules ast_stamping.
Export DBNotation old_subtyping_derived_rules.

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
From D.Dot Require Import traversals core_stamping_defs type_extraction_syn.

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

(****************)
(** AUTOMATION **)
(****************)
(* Prevent simplification from unfolding it, basically unconditionally. *)
Arguments extraction : simpl never.

From D.Dot Require Import unstampedness_binding stampedness_binding.
(* For performance, keep these hints local to examples *)
Hint Extern 5 => try_once extraction_weaken : core.
Hint Extern 5 (is_stamped_ty _ _ _) => try_once is_stamped_weaken_ty : core.
Hint Extern 5 (is_unstamped_ty _ _ _) => try_once is_unstamped_weaken_ty : core.
Hint Extern 5 (is_stamped_dm _ _ _) => try_once is_stamped_weaken_dm : core.
Hint Extern 5 (is_stamped_ren _ _ _ _) => progress cbn : core.

(** [tcrush] is the safest automation around. *)
Ltac tcrush := repeat first [ eassumption | reflexivity | typconstructor | stcrush ].
Ltac wtcrush := repeat first [fast_done | typconstructor | stcrush]; try solve [ done |
  first [
    (* by eauto 3 using is_stamped_TLater_n, is_stamped_ren1_ty, is_stamped_ren1_path *)
    by eauto 3 using is_stamped_ren1_ty, is_unstamped_ren1_ty |
    try_once extraction_weaken |
    try_once is_unstamped_weaken_ty |
    try_once is_stamped_weaken_dm |
    try_once is_stamped_weaken_ty ]; eauto ].

Hint Extern 5 (nclosed _ _) => by solve_fv_congruence : fvc.
Hint Resolve pack_extraction : fvc.
Hint Extern 5 (is_stamped_ty _ _ _) => tcrush : fvc.
Hint Extern 5 (is_stamped_σ _ _ _) => tcrush : fvc.
Hint Resolve pack_extraction' : fvc.
Ltac by_extcrush := by try eapply pack_extraction'; rewrite /= ?hsubst_id; eauto with fvc.

Ltac hideCtx :=
  let hideCtx' Γ := (let x := fresh "Γ" in set x := Γ) in
  match goal with
  | |- ?Γ v⊢ₜ[ _ ] _ : _ => hideCtx' Γ
  | |- ?Γ v⊢ₜ[ _ ] _, _ <: _, _ => hideCtx' Γ
  | |- ?Γ v⊢ₚ[ _ ] _ : _, _  => hideCtx' Γ
  | |- ?Γ v⊢[ _ ]{ _ := _  } : _ => hideCtx' Γ
  | |- ?Γ v⊢ds[ _ ] _ : _ => hideCtx' Γ
  end.

(** Not used here, but useful for extending storeless typing and making it compositional. *)
Lemma storeless_typing_mono_mut Γ g :
  (∀ e T, Γ v⊢ₜ[ g ] e : T → ∀ g' (Hle : g ⊆ g'), Γ v⊢ₜ[ g' ] e : T) ∧
  (∀ ds T, Γ v⊢ds[ g ] ds : T → ∀ g' (Hle : g ⊆ g'), Γ v⊢ds[ g' ] ds : T) ∧
  (∀ l d T, Γ v⊢[ g ]{ l := d } : T → ∀ g' (Hle : g ⊆ g'), Γ v⊢[ g' ]{ l := d } : T).
Proof.
  eapply storeless_typing_mut_ind with
      (P := λ Γ g e T _, ∀ g' (Hle : g ⊆ g'), Γ v⊢ₜ[ g' ] e : T)
      (P0 := λ Γ g ds T _, ∀ g' (Hle : g ⊆ g'), Γ v⊢ds[ g' ] ds : T)
      (P1 := λ Γ g l d T _, ∀ g' (Hle : g ⊆ g'), Γ v⊢[ g' ]{ l := d } : T);
  clear Γ g; intros;
    repeat match goal with
    | H : forall g : stys, _ |- _ => specialize (H g' Hle)
    end; eauto 3; eauto.
Qed.

Hint Resolve is_stamped_idsσ_ren : core.

(* XXX drop *)
Ltac asideLaters' :=
  repeat first
    [ettrans; last (apply iSub_Later; tcrush)|
    ettrans; first (apply iLater_Sub; tcrush)].

Ltac lNext' := ettrans; first apply iAnd2_Sub; tcrush.
Ltac lThis' := ettrans; first apply iAnd1_Sub; tcrush.

Ltac lookup' :=
  lazymatch goal with
  | |- _ v⊢ₜ[ _ ] ?T1, _ <: ?T2, _ =>
    let T1' := eval hnf in T1 in
    match T1' with
    | (TAnd ?T11 ?T12) =>
      (* first [unify (label_of_ty T11) (label_of_ty T2); lThis | lNext] *)
      let ls := eval cbv in (label_of_ty T11, label_of_ty T2) in
      match ls with
      | (Some ?l1, Some ?l1) => lThis'
      | (Some ?l1, Some ?l2) => lNext'
      end
    end
  end.
Ltac ltcrush := tcrush; repeat lookup.
Ltac ltcrush' := tcrush; repeat lookup'.

(*******************)
(** DERIVED RULES **)
(*******************)

Section examples_lemmas.
Context {g}.

Lemma iT_All_Ex' T2 {Γ e1 x2 T1 T3} :
  Γ v⊢ₜ[ g ] e1: TAll T1 T2 →                        Γ v⊢ₜ[ g ] tv (var_vl x2) : T1 →
  T3 = T2.|[var_vl x2/] →
  (*────────────────────────────────────────────────────────────*)
  Γ v⊢ₜ[ g ] tapp e1 (tv (var_vl x2)) : T3.
Proof. intros; subst. exact: iT_All_Ex. Qed.

Lemma iT_Var' Γ x T1 T2 :
  Γ !! x = Some T1 →
  T2 = shiftN x T1 →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv (var_vl x) : T2.
Proof. intros; apply iT_Path'; pvar. Qed.

Lemma iT_Var0 Γ T :
  Γ !! 0 = Some T →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv (var_vl 0) : T.
Proof. intros; apply iT_Path'; pvar. Qed.

Lemma iT_Var_Sub Γ x T1 T2 :
  Γ !! x = Some T1 →
  Γ v⊢ₜ[ g ] shiftN x T1, 0 <: T2, 0 →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv (var_vl x) : T2.
Proof. by intros; apply iT_Path'; pvarsub. Qed.

Lemma iT_Var0_Sub Γ T1 T2 :
  Γ !! 0 = Some T1 →
  Γ v⊢ₜ[ g ] T1, 0 <: T2, 0 →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv (var_vl 0) : T2.
Proof. by intros; apply iT_Path'; pvarsub. Qed.

Lemma iT_Mu_E' Γ x T1 T2:
  Γ v⊢ₜ[ g ] tv (var_vl x): TMu T1 →
  T2 = T1.|[var_vl x/] →
  (*──────────────────────*)
  Γ v⊢ₜ[ g ] tv (var_vl x): T2.
Proof. intros; subst; auto. Qed.

Lemma iT_Sub_nocoerce T1 T2 {Γ e} :
  Γ v⊢ₜ[ g ] e : T1 →
  Γ v⊢ₜ[ g ] T1, 0 <: T2, 0 →
  Γ v⊢ₜ[ g ] e : T2.
Proof. intros. exact: (iT_Sub (i:=0)). Qed.
Hint Resolve iT_Sub_nocoerce : core.

Lemma path_tp_delay {Γ p T i j} (Hst: is_unstamped_ty' (length Γ) T) : i <= j →
  Γ v⊢ₚ[ g ] p : T, i → Γ v⊢ₚ[ g ] p : T, j.
Proof.
  intros Hle Hp.
  rewrite (le_plus_minus i j Hle); move: {j Hle} (j - i) => k.
  eapply iP_Sub, Hp.
  apply: iSub_AddIJ'; by [|lia].
Qed.

Lemma is_stamped_pvar i n : i < n → is_stamped_path n g (pv (var_vl i)).
Proof. eauto. Qed.
Lemma is_stamped_pvars i n l : i < n → is_stamped_ty n g (pv (var_vl i) @; l).
Proof. eauto using is_stamped_pvar. Qed.

Lemma iT_Let Γ t u T U :
  Γ v⊢ₜ[ g ] t : T →
  shift T :: Γ v⊢ₜ[ g ] u : shift U →
  is_stamped_ty (length Γ) g T →
  Γ v⊢ₜ[ g ] lett t u : U.
Proof. move=> Ht Hu HsT. apply /iT_All_E /Ht /iT_All_I /Hu /HsT. Qed.

(* Note how we must weaken the type (or its environment) to account for the
   self-variable of the created object. *)
Definition packTV n s := (ν {@ type "A" = (shift (idsσ n); s)}).

Lemma iD_Typ T {Γ l s σ}:
  T ~[ length Γ ] (g, (s, σ)) →
  is_stamped_σ (length Γ) g σ →
  is_unstamped_ty' (length Γ) T →
  Γ v⊢[ g ]{ l := dtysem σ s } : TTMemL l T T.
Proof. intros. apply (iD_Typ_Abs T); subtcrush. Qed.

Lemma packTV_typed' s T n Γ :
  g !! s = Some T →
  is_unstamped_ty' n T →
  n <= length Γ →
  Γ v⊢ₜ[ g ] packTV n s : typeEq "A" T.
Proof.
  move => Hlp HuT1 Hle; move: (Hle)  (HuT1) => /le_n_S Hles /is_unstamped_ren1_ty HuT2.
  move: (is_unstamped_nclosed_ty HuT1) => Hcl.

  (* XXX *)
  have HsT1 := unstamped_stamped_type g HuT1; move: (HsT1) => /is_stamped_ren1_ty HsT2.

  apply (iT_Sub_nocoerce (μ {@ typeEq "A" (shift T) }));
    last (ettrans; first apply: (iMu_Sub (T := {@ typeEq "A" T })); tcrush).
  apply iT_Obj_I; tcrush.
  apply (iD_Typ (shift T)); simpl; eauto 2.
  eapply extraction_inf_subst, is_stamped_ren1.
  by apply /extraction_weaken /Hle /pack_extraction.
Qed.

Lemma packTV_typed s T Γ :
  g !! s = Some T →
  is_unstamped_ty' (length Γ) T →
  Γ v⊢ₜ[ g ] packTV (length Γ) s : typeEq "A" T.
Proof. intros; exact: packTV_typed'. Qed.

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

Definition tApp Γ t s :=
  lett t (lett (packTV (S (length Γ)) s) (tapp x1 x0)).

Lemma typeApp_typed s Γ T U V t :
  Γ v⊢ₜ[ g ] t : TAll (type "A" >: ⊥ <: ⊤) U →
  (** This subtyping premise is needed to perform "avoidance", as in compilers
    for ML and Scala: that is, producing a type [V] that does not refer to
    variables bound by let in the expression. *)
  (∀ L, typeEq "A" (shiftN 2 T) :: L :: Γ v⊢ₜ[ g ] U.|[up (ren (+1))], 0 <: shiftN 2 V, 0) →
  is_unstamped_ty' (length Γ) T →
  is_unstamped_ty' (S (length Γ)) U →
  g !! s = Some (shift T) →
  Γ v⊢ₜ[ g ] tApp Γ t s : V.
Proof.
  move => Ht Hsub HuT1 HuU1 Hl.
  move: (HuT1) => /is_unstamped_ren1_ty HuT2; move: (HuT2) => /is_unstamped_ren1_ty HuT3.
  have HsT1 := unstamped_stamped_type g HuT1; move: (HsT1) => /is_stamped_ren1_ty HsT2.
  have HsU1 := unstamped_stamped_type g HuU1.
  rewrite -hrenS in HuT3.
  eapply iT_Let; [exact: Ht| |tcrush].
  eapply iT_Let; [by apply packTV_typed| |tcrush].
  rewrite /= -!hrenS -/(typeEq _ _).

  apply /iT_Sub_nocoerce /Hsub.

  eapply iT_All_Ex'; first exact: iT_Var'.
  apply: iT_Var_Sub; tcrush; rewrite /= hsubst_id //.
  rewrite !hsubst_comp; f_equal. autosubst.
Qed.

End examples_lemmas.

Hint Resolve is_stamped_pvar is_stamped_pvars iT_Sub_nocoerce : core.

Ltac var := exact: iT_Var0 || exact: iT_Var' || pvar.
Ltac varsub := (eapply iP_Var_Sub || eapply iP_Var0_Sub ||
  eapply iT_Var0_Sub || eapply iT_Var_Sub); first done.
Ltac mltcrush := tcrush; try ((apply iSub_Bind_1' || apply iSub_Bind_1); tcrush); repeat lookup.
