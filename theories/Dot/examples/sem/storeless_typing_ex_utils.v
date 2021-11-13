(**
Infrastructure for examples of DOT programs using stamped and storeless typing.
*)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn.
From D.Dot Require Export storeless_typing ex_utils hoas old_subtyping_derived_rules.
Export DBNotation old_subtyping_derived_rules.

Set Default Proof Using "Type".
Set Suggest Proof Using.

Implicit Types (L T U : ty) (v : vl) (e : tm) (d : dm) (ds : dms) (Γ : list ty).

(**********************)
(** STAMPED NOTATION **)
(**********************)
Bind Scope positive_scope with stamp.

Notation σ1 := ([] : vls).
Notation s1 := (1 %positive).

Notation σ2 := ([] : vls).
Notation s2 := (2 %positive).

Notation "'type' l = ( σ ; s )" := (l, dtysem σ s) (at level 60, l at level 50).

(****************)
(** AUTOMATION **)
(****************)

From D.Dot Require Import traversals core_stamping_defs.
From D.Dot Require Import unstampedness_binding.
Ltac tcrush_nclosed :=
  by [ | eapply (is_unstamped_nclosed_ty (b := OnlyVars)); stcrush].

(* For performance, keep these hints local to examples *)
#[global] Hint Extern 5 (is_unstamped_ty _ _ _) => try_once is_unstamped_weaken_ty : core.
#[global] Hint Extern 5 (is_unstamped_kind _ _ _) => try_once is_unstamped_weaken_kind : core.
#[global] Hint Extern 5 (is_unstamped_ren _ _ _ _) => progress cbn : core.

(** [tcrush] is the safest automation around. *)
Ltac tcrush := repeat first [ eassumption | reflexivity | typconstructor | stcrush ].
Ltac wtcrush := repeat first [fast_done | typconstructor | stcrush]; try solve [ done |
  first [
    by eauto 3 using is_unstamped_ren1_ty |
    try_once is_unstamped_weaken_ty | try_once is_unstamped_weaken_kind ]; eauto ].

#[global] Hint Extern 5 (nclosed _ _) => by solve_fv_congruence : fvc.

Ltac hideCtx :=
  let hideCtx' Γ := (let x := fresh "Γ" in set x := Γ) in
  match goal with
  | |- ?Γ v⊢ₜ _ : _ => hideCtx' Γ
  | |- ?Γ v⊢ₜ _, _ <: _, _ => hideCtx' Γ
  | |- ?Γ u⊢ₚ _ : _, _  => hideCtx' Γ
  | |- ?Γ v⊢{ _ := _  } : _ => hideCtx' Γ
  | |- ?Γ v⊢ds _ : _ => hideCtx' Γ
  end.

(* XXX drop *)
Ltac asideLaters' :=
  repeat first
    [ettrans; last (apply iSub_Later; tcrush)|
    ettrans; first (apply iLater_Sub; tcrush)].

Ltac lNext' := ettrans; first apply iAnd2_Sub; tcrush.
Ltac lThis' := ettrans; first apply iAnd1_Sub; tcrush.

Ltac lookup' :=
  lazymatch goal with
  | |- _ v⊢ₜ ?T1, _ <: ?T2, _ =>
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

Lemma iT_All_Ex' T2 {Γ e1 x2 T1 T3} :
  Γ v⊢ₜ e1 : TAll T1 T2 →                        Γ v⊢ₜ tv (vvar x2) : T1 →
  T3 = T2.|[vvar x2/] →
  (*────────────────────────────────────────────────────────────*)
  Γ v⊢ₜ tapp e1 (tv (vvar x2)) : T3.
Proof. intros; subst. exact: iT_All_Ex. Qed.

Lemma iT_Var' Γ x T1 T2 :
  Γ !! x = Some T1 →
  T2 = shiftN x T1 →
  (*──────────────────────*)
  Γ v⊢ₜ tv (vvar x) : T2.
Proof. intros; apply iT_Path'; pvar. Qed.

Lemma iT_Var0 Γ T :
  Γ !! 0 = Some T →
  (*──────────────────────*)
  Γ v⊢ₜ tv (vvar 0) : T.
Proof. intros; apply iT_Path'; pvar. Qed.

Lemma iT_Var_Sub Γ x T1 T2 :
  Γ !! x = Some T1 →
  Γ v⊢ₜ shiftN x T1, 0 <: T2, 0 →
  (*──────────────────────*)
  Γ v⊢ₜ tv (vvar x) : T2.
Proof. by intros; apply iT_Path'; pvarsub. Qed.

Lemma iT_Var0_Sub Γ T1 T2 :
  Γ !! 0 = Some T1 →
  Γ v⊢ₜ T1, 0 <: T2, 0 →
  (*──────────────────────*)
  Γ v⊢ₜ tv (vvar 0) : T2.
Proof. by intros; apply iT_Path'; pvarsub. Qed.

Lemma iT_Mu_E' Γ x T1 T2 :
  Γ v⊢ₜ tv (vvar x) : TMu T1 →
  T2 = T1.|[vvar x/] →
  is_unstamped_ty' (length Γ).+1 T1 →
  (*──────────────────────*)
  Γ v⊢ₜ tv (vvar x) : T2.
Proof. intros; subst; tcrush. Qed.

Lemma iT_ISub_nocoerce T1 T2 {Γ e} :
  Γ v⊢ₜ e : T1 →
  Γ v⊢ₜ T1, 0 <: T2, 0 →
  Γ v⊢ₜ e : T2.
Proof. intros. exact: (iT_ISub (i:=0)). Qed.
#[global] Hint Resolve iT_ISub_nocoerce : core.

Lemma path_tp_delay {Γ p T i j} (Hst : is_unstamped_ty' (length Γ) T) : i <= j →
  Γ u⊢ₚ p : T, i → Γ u⊢ₚ p : T, j.
Proof.
  intros Hle Hp.
  rewrite (le_plus_minus i j Hle); move: {j Hle} (j - i) => k.
  eapply iP_ISub, Hp.
  apply: iSub_AddIJ'; by [|lia].
Qed.

Lemma iT_Let Γ t u T U :
  Γ v⊢ₜ t : T →
  shift T :: Γ v⊢ₜ u : shift U →
  Γ v⊢ₜ lett t u : U.
Proof. move=> Ht Hu. apply /iT_All_E /Ht /iT_All_I /Hu. Qed.

(* Note how we must weaken the type (or its environment) to account for the
   self-variable of the created object. *)
Definition packTV n s := (ν {@ type "A" = (shift (idsσ n); s)}).

Lemma iD_Typ T {Γ l s σ} :
  is_unstamped_ty' (length Γ) T →
  Γ v⊢{ l := dtysem σ s } : TTMemL l T T.
Proof. intros. apply (iD_Typ_Abs_old T); subtcrush. exact: is_unstamped_nclosed_ty. Qed.

Lemma packTV_typed' s T n Γ :
  is_unstamped_ty' n T →
  n <= length Γ →
  Γ v⊢ₜ packTV n s : typeEq "A" T.
Proof.
  move => HuT1 Hle; move: (Hle)  (HuT1) => /le_n_S Hles /is_unstamped_ren1_ty HuT2.
  move: (is_unstamped_nclosed_ty HuT1) => Hcl.

  apply (iT_ISub_nocoerce (μ {@ typeEq "A" (shift T) }));
    last (ettrans; first apply: (iMu_Sub _ {@ typeEq "A" T }); tcrush).
  apply iT_Obj_I; tcrush.
  apply (iD_Typ (shift T)); simpl; eauto 2.
Qed.

Lemma packTV_typed s T Γ :
  is_unstamped_ty' (length Γ) T →
  Γ v⊢ₜ packTV (length Γ) s : typeEq "A" T.
Proof. intros; exact: packTV_typed'. Qed.

Definition tApp Γ t s :=
  lett t (lett (packTV (length Γ).+1 s) (tapp x1 x0)).

Lemma typeApp_typed s Γ T U V t :
  Γ v⊢ₜ t : TAll (type "A" >: ⊥ <: ⊤) U →
  (** This subtyping premise is needed to perform "avoidance", as in compilers
    for ML and Scala: that is, producing a type [V] that does not refer to
    variables bound by let in the expression. *)
  (∀ L, typeEq "A" (shiftN 2 T) :: L :: Γ v⊢ₜ U.|[up (ren (+1))], 0 <: shiftN 2 V, 0) →
  is_unstamped_ty' (length Γ) T →
  Γ v⊢ₜ tApp Γ t s : V.
Proof.
  move => Ht Hsub HuT1.
  move: (HuT1) => /is_unstamped_ren1_ty HuT2.
  move: (HuT2) => /is_unstamped_ren1_ty HuT3; rewrite -hrenS in HuT3.
  eapply iT_Let; [exact: Ht| ].
  eapply iT_Let; [by apply packTV_typed| ].
  rewrite /= -!hrenS -/(typeEq _ _).

  apply /iT_ISub_nocoerce /Hsub.

  eapply iT_All_Ex'; first exact: iT_Var'.
  apply: iT_Var_Sub; tcrush; rewrite /= hsubst_id //.
  rewrite !hsubst_comp; f_equal. autosubst.
Qed.

#[global] Hint Resolve iT_ISub_nocoerce : core.

Ltac var := exact: iT_Var0 || exact: iT_Var' || pvar.
Ltac varsub := (eapply iP_Var_Sub || eapply iP_Var0_Sub ||
  eapply iT_Var0_Sub || eapply iT_Var_Sub); first done.
Ltac mltcrush := tcrush; try ((apply iSub_Bind_1' || apply iSub_Bind_1); tcrush); repeat lookup.
