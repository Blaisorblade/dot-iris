From stdpp Require Import strings.
From D Require Import tactics.
From D.Dot Require Import syn exampleInfra typing_unstamped.
From D.Dot Require Import unstampedness_binding.

Lemma is_unstamped_pvar i n : i < n → is_unstamped_path n (pv (var_vl i)).
Proof. eauto. Qed.
Hint Resolve is_unstamped_pvar : core.
Lemma is_unstamped_pvars i n l : i < n → is_unstamped_ty n (pv (var_vl i) @; l).
Proof. eauto. Qed.
Hint Resolve is_unstamped_pvars : core.

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

Lemma Subs_typed_nocoerce T1 T2 {Γ e} :
  Γ u⊢ₜ e : T1 →
  Γ u⊢ₜ T1, 0 <: T2, 0 →
  Γ u⊢ₜ e : T2.
Proof. rewrite -(iterate_0 tskip e). eauto. Qed.
Hint Resolve Subs_typed_nocoerce : core.

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
  Γ u⊢ₜ tv (ids x): μ T1 →
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

Lemma Let_typed Γ t u T U :
  Γ u⊢ₜ t : T →
  T.|[ren (+1)] :: Γ u⊢ₜ u : U.|[ren (+1)] →
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ lett t u : U.
Proof. move=> Ht Hu HsT. apply /App_typed /Ht /Lam_typed /Hu /HsT. Qed.

Lemma val_LB T U Γ i x :
  Γ u⊢ₜ tv (ids x) : type "A" >: T <: U →
  Γ u⊢ₜ ▶ T, i <: (pv (ids x) @; "A"), i.
Proof. intros; apply /AddIB_stp /(@LSel_stp _ (pv _)); tcrush. Qed.

Lemma val_UB T L Γ i x :
  Γ u⊢ₜ tv (ids x) : type "A" >: L <: T →
  Γ u⊢ₜ (pv (ids x) @; "A"), i <: ▶ T, i.
Proof. intros; eapply AddIB_stp, SelU_stp; tcrush. Qed.

(* These rules from storeless typing must be encoded somehow via variables. *)
(* Lemma packTV_LB T n Γ i :
  is_unstamped_ty n T →
  n <= length Γ →
  Γ u⊢ₜ ▶ T, i <: (pv (packTV T) @; "A"), i.
Proof. intros; apply /val_LB /packTV_typed'. Qed. *)

(* Lemma packTV_UB T n Γ i :
  is_unstamped_ty n T →
  n <= length Γ →
  Γ u⊢ₜ (pv (packTV T) @; "A"), i <: ▶ T, i.
Proof. intros; by apply /val_UB /packTV_typed'. Qed. *)

Lemma Dty_typed Γ T V l:
    is_unstamped_ty (S (length Γ)) T →
    Γ |d V u⊢{ l := dtysyn T } : TTMem l T T.
Proof. intros. apply dty_typed; tcrush. Qed.

(* We can derive rules Bind1 and Bind2 (the latter only conjectured) from
  "Type Soundness for Dependent Object Types (DOT)", Rompf and Amin, OOPSLA '16. *)
Lemma Bind1 Γ T1 T2 i:
  is_unstamped_ty (S (length Γ)) T1 → is_unstamped_ty (length Γ) T2 →
  iterate TLater i T1 :: Γ u⊢ₜ T1, i <: T2.|[ren (+1)], i →
  Γ u⊢ₜ μ T1, i <: T2, i.
Proof.
  intros Hus1 Hus2 Hsub.
  eapply Trans_stp; first exact: (Mu_stp_mu Hsub).
  exact: Mu_stp.
Qed.

Lemma Bind2 Γ T1 T2 i:
  is_unstamped_ty (length Γ) T1 → is_unstamped_ty (S (length Γ)) T2 →
  iterate TLater i T1.|[ren (+1)] :: Γ u⊢ₜ T1.|[ren (+1)], i <: T2, i →
  Γ u⊢ₜ T1, i <: μ T2, i.
Proof.
  intros Hus1 Hus2 Hsub; move: (Hus1) => /is_unstamped_ren1_ty Hus1'.
  eapply Trans_stp; last exact: (Mu_stp_mu Hsub).
  exact: Stp_mu.
Qed.

Lemma Bind1' Γ T1 T2:
  is_unstamped_ty (S (length Γ)) T1 → is_unstamped_ty (length Γ) T2 →
  T1 :: Γ u⊢ₜ T1, 0 <: T2.|[ren (+1)], 0 →
  Γ u⊢ₜ μ T1, 0 <: T2, 0.
Proof. intros; exact: Bind1. Qed.

Lemma Bind2' Γ T1 T2:
  is_unstamped_ty (length Γ) T1 → is_unstamped_ty (S (length Γ)) T2 →
  T1.|[ren (+1)] :: Γ u⊢ₜ T1.|[ren (+1)], 0 <: T2, 0 →
  Γ u⊢ₜ T1, 0 <: μ T2, 0.
Proof. intros; exact: Bind2. Qed.
