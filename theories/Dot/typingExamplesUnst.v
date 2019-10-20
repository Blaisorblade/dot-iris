(**
WIP examples constructing _unstamped_ syntactic typing derivations.
 *)
From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra typing_unstamped.

Implicit Types (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (Γ : list ty).

Lemma Subs_typed_nocoerce T1 T2 {Γ e} :
  Γ u⊢ₜ e : T1 →
  Γ u⊢ₜ T1, 0 <: T2, 0 →
  Γ u⊢ₜ e : T2.
Proof. rewrite -(iterate_0 tskip e). eauto. Qed.
Hint Resolve Subs_typed_nocoerce : core.

From D.Dot Require Import traversals unstampedness_binding.

Ltac typconstructor := match goal with
  | |- typed _ _ _ => constructor
  | |- dms_typed _ _ _ _ => constructor
  | |- dm_typed _ _ _ _ _ => constructor
  | |- path_typed _ _ _ _ => constructor
  | |- subtype _ _ _ _ _ => constructor
  end.

Ltac tcrush := repeat typconstructor; stcrush; try solve [ done |
  first [
    try_once is_unstamped_weaken_dm |
    try_once is_unstamped_weaken_ty ]; eauto ].

Example ex0 e Γ T:
  Γ u⊢ₜ e : T →
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ e : ⊤.
Proof. intros. apply (Subs_typed_nocoerce T TTop); tcrush. Qed.

Example ex1 Γ n T:
  Γ u⊢ₜ tv (ν {@ val "a" = vnat n}) : μ {@ val "a" : TNat }.
Proof.
  (* Help proof search: Avoid trying TMuI_typed, that's slow. *)
  apply VObj_typed; tcrush.
Qed.

Notation "'type' l = T  " := (l, dtysyn T) (at level 60, l at level 50).
Example ex2 Γ T :
  Γ u⊢ₜ tv (ν {@ type "A" = p0 @; "B" } ) : TMu (TAnd (TTMem "A" TBot TTop) TTop).
Proof. apply VObj_typed; tcrush. Qed.

(* Try out fixpoints. *)
Definition F3 T :=
  TMu (TAnd (TTMem "A" T T) TTop).

Example ex3 Γ T:
  Γ u⊢ₜ tv (ν {@ type "A" = F3 (p0 @; "A") } ) : F3 (F3 (TSel p0 "A")).
Proof. apply VObj_typed; tcrush. Qed.

Notation HashableString := (μ {@ val "hashCode" : TAll TUnit TNat }).
Definition KeysT : ty := μ {@
  type "Key" >: ⊥ <: ⊤;
  val "key": TAll HashableString (p1 @; "Key")
}.
Definition hashKeys : vl := ν {@
  type "Key" = TNat;
  val "key" = vabs (tapp (tproj (tv x0) "hashCode") tUnit)
}.

Definition KeysT' := μ {@
  type "Key" >: TNat <: ⊤;
  val "key": TAll HashableString (p1 @; "Key")
}.
(* IDEA for our work: use [(type "Key" >: TNat <: ⊤) ⩓ (type "Key" >: ⊥ <: ⊤)]. *)
Lemma Appv_typed' T2 {Γ e1 x2 T1 T3} :
  Γ u⊢ₜ e1: TAll T1 T2 →                        Γ u⊢ₜ tv (ids x2) : T1 →
  T3 = T2.|[ids x2/] →
  (*────────────────────────────────────────────────────────────*)
  Γ u⊢ₜ tapp e1 (tv (ids x2)) : T3.
Proof. intros; subst; by econstructor. Qed.

Lemma Var_typed' Γ x T1 T2 :
  Γ !! x = Some T1 →
  T2 = T1.|[ren (+x)] →
  (*──────────────────────*)
  Γ u⊢ₜ tv (var_vl x) : T2.
Proof. intros; subst; tcrush. Qed.

Lemma TMuE_typed' Γ x T1 T2:
  Γ u⊢ₜ tv (ids x): TMu T1 →
  T2 = T1.|[ids x/] →
  (*──────────────────────*)
  Γ u⊢ₜ tv (ids x): T2.
Proof. intros; subst; auto. Qed.

Lemma Sub_later_shift {Γ T1 T2 i j}
  (Hs1: is_unstamped_ty (length Γ) T1)
  (Hs2: is_unstamped_ty (length Γ) T2)
  (Hsub: Γ u⊢ₜ T1, S i <: T2, S j):
  Γ u⊢ₜ TLater T1, i <: TLater T2, j.
Proof.
  eapply Trans_stp; first exact: TLaterL_stp.
  by eapply Trans_stp, TLaterR_stp.
Qed.

Lemma Sub_later_shift_inv {Γ T1 T2 i j}
  (Hs1: is_unstamped_ty (length Γ) T1)
  (Hs2: is_unstamped_ty (length Γ) T2)
  (Hsub: Γ u⊢ₜ TLater T1, i <: TLater T2, j):
  Γ u⊢ₜ T1, S i <: T2, S j.
Proof.
  eapply Trans_stp; first exact: TLaterR_stp.
  by eapply Trans_stp, TLaterL_stp.
Qed.

Lemma Var_typed_sub Γ x T1 T2 :
  Γ !! x = Some T1 →
  Γ u⊢ₜ T1.|[ren (+x)], 0 <: T2, 0 →
  (*──────────────────────*)
  Γ u⊢ₜ tv (var_vl x) : T2.
Proof. intros; eapply Subs_typed_nocoerce; by [exact: Var_typed|]. Qed.

Lemma LSel_stp' Γ U {p l L i}:
  is_unstamped_ty (length Γ) L →
  Γ u⊢ₚ p : TTMem l L U, i →
  Γ u⊢ₜ L, i <: TSel p l, i.
Proof.
  intros.
  eapply Trans_stp; last exact: (@LSel_stp _ p).
  induction (plength p); rewrite /= ?iterate_0 ?iterate_S; tcrush.
  eapply Trans_stp; first exact: TAddLater_stp; tcrush.
Qed.

Lemma AddI_stp Γ T i (Hst: is_unstamped_ty (length Γ) T) :
  Γ u⊢ₜ T, 0 <: T, i.
Proof.
  elim: i => [|n IHn]; first tcrush.
  eapply Trans_stp; first apply IHn.
  eapply Trans_stp; [exact: TAddLater_stp | tcrush].
Qed.

Lemma AddIB_stp Γ T U i:
  Γ u⊢ₜ T, 0 <: U, 0 →
  Γ u⊢ₜ T, i <: U, i.
Proof.
  move => Hstp; elim: i => [|n IHn]; first tcrush.
  exact: TMono_stp.
Qed.

Lemma is_unstamped_pvar i n : i < n → is_unstamped_path n (pv (var_vl i)).
Proof. eauto. Qed.
Hint Resolve is_unstamped_pvar : core.
Lemma is_unstamped_pvars i n l : i < n → is_unstamped_ty n (pv (var_vl i) @; l).
Proof. eauto. Qed.
Hint Resolve is_unstamped_pvars : core.

Example hashKeys_typed Γ:
  Γ u⊢ₜ tv hashKeys : KeysT.
Proof.
  cut (Γ u⊢ₜ tv hashKeys : KeysT').
  { intros H.
    apply (Subs_typed_nocoerce KeysT'); first done.
    apply Mu_stp_mu; last stcrush.
    tcrush.
    eapply Trans_stp; first apply TAnd1_stp; tcrush.
  }
  apply VObj_typed; cbn; last by tcrush.
  eapply dcons_typed; tcrush.
  cbn; apply App_typed with (T1 := TUnit);
    last eapply (Subs_typed_nocoerce TNat); tcrush; cbn.

  pose (T0 := μ {@ val "hashCode" : TAll ⊤ 𝐍 }).

  have Htp: ∀ Γ', T0 :: Γ' u⊢ₜ tv x0 : val "hashCode" : TAll ⊤ TNat. {
    intros. eapply Subs_typed_nocoerce.
    eapply TMuE_typed'; by [exact: Var_typed'|].
    by apply TAnd1_stp; tcrush.
  }
  apply (Subs_typed_nocoerce (val "hashCode" : TAll ⊤ 𝐍)). exact: Htp.
  tcrush.
  eapply LSel_stp'; tcrush.
  eapply Var_typed_sub; by [|tcrush].
Qed.

Lemma Let_typed Γ t u T U :
  Γ u⊢ₜ t : T →
  T.|[ren (+1)] :: Γ u⊢ₜ u : U.|[ren (+1)] →
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ lett t u : U.
Proof. move=> Ht Hu HsT. apply /App_typed /Ht /Lam_typed /Hu /HsT. Qed.

(* Note how we must weaken the type (or its environment) to account for the
   self-variable of the created object. *)
Definition packTV T := (ν {@ type "A" = T.|[ren (+1)] }).

Lemma packTV_typed' T n Γ :
  is_unstamped_ty n T →
  n <= length Γ →
  Γ u⊢ₜ tv (packTV T) : typeEq "A" T.
Proof.
  move => HsT1 Hle; move: (Hle) (HsT1) => /le_n_S Hles /is_unstamped_ren1_ty HsT2.
  apply (Subs_typed_nocoerce (μ {@ typeEq "A" T.|[ren (+1)] }));
    last (eapply Trans_stp; first apply (@Mu_stp _ ({@ typeEq "A" T })); tcrush).
  apply VObj_typed; tcrush.
Qed.

Lemma packTV_typed T Γ :
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ tv (packTV T) : typeEq "A" T.
Proof. intros; exact: packTV_typed'. Qed.

Lemma val_LB T U Γ i x :
  Γ u⊢ₜ tv (ids x) : type "A" >: T <: U →
  Γ u⊢ₜ ▶ T, i <: (pv (ids x) @; "A"), i.
Proof. intros; apply /AddIB_stp /(@LSel_stp _ (pv _)); tcrush. Qed.

(* Lemma packTV_LB T n Γ i :
  is_unstamped_ty n T →
  n <= length Γ →
  Γ u⊢ₜ ▶ T, i <: (pv (packTV T) @; "A"), i.
Proof. intros; apply /val_LB /packTV_typed'. Qed. *)

Lemma val_UB T L Γ i x :
  Γ u⊢ₜ tv (ids x) : type "A" >: L <: T →
  Γ u⊢ₜ (pv (ids x) @; "A"), i <: ▶ T, i.
Proof. intros; eapply AddIB_stp, SelU_stp; tcrush. Qed.

(* Lemma packTV_UB T n Γ i :
  is_unstamped_ty n T →
  n <= length Γ →
  Γ u⊢ₜ (pv (packTV T) @; "A"), i <: ▶ T, i.
Proof. intros; by apply /val_UB /packTV_typed'. Qed. *)

Definition tApp Γ t T :=
  lett t (lett (tv (packTV T)) (tapp (tv x1) (tv x0))).

Lemma typeApp_typed Γ T U V t :
  Γ u⊢ₜ t : TAll (type "A" >: ⊥ <: ⊤) U →
  (** This subtyping premise is needed to perform "avoidance", as in compilers
    for ML and Scala: that is, producing a type [V] that does not refer to
    variables bound by let in the expression. *)
  (∀ L, typeEq "A" T.|[ren (+2)] :: L :: Γ u⊢ₜ U.|[up (ren (+1))], 0 <: V.|[ren (+2)], 0) →
  is_unstamped_ty (length Γ) T →
  is_unstamped_ty (S (length Γ)) U →
  Γ u⊢ₜ tApp Γ t T.|[ren (+1)] : V.
Proof.
  move => Ht Hsub HsT1 HsU1; move: (HsT1) => /is_unstamped_ren1_ty HsT2.
  move: (HsT2) => /is_unstamped_ren1_ty HsT3.
  rewrite -hrenS in HsT3.
  eapply Let_typed; [exact: Ht| |tcrush].
  eapply Let_typed; [by apply packTV_typed| |tcrush].
  rewrite /= -!hrenS -/(typeEq _ _).

  apply /Subs_typed_nocoerce /Hsub.

  eapply Appv_typed'; first exact: Var_typed'.
  apply: Var_typed_sub; repeat tcrush; rewrite /= hsubst_id //.
  rewrite !hsubst_comp; f_equal. autosubst.
Qed.
