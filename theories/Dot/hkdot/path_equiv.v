(** * XXX Experiments on path equivalence. Compare and contrast with path_equiv2.v. *)

From D Require Import iris_prelude proper lty lr_syn_aux.
From D Require Import iris_extra.det_reduction.
From D Require Import swap_later_impl.
From D.Dot Require Import syn path_repl.
From D.Dot Require Import dlang_inst path_wp.
From D.pure_program_logic Require Import weakestpre.
From D.Dot Require Import dot_lty dot_semtypes sem_kind_dot unary_lr.

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : env) (l : label) (T : ty) (K : kind).

Definition dm_rel Σ := ∀ (args : astream) (ρ : env) (d1 d2 : dm), iProp Σ.
Definition dms_rel Σ := ∀ (args : astream) (ρ : env) (ds1 ds2 : dms), iProp Σ.
Definition vl_rel Σ := ∀ (args : astream) (ρ : env) (v1 v2 : vl), iProp Σ.

(** TODO #431: remove *)
#[export] Declare Instance persistence_unsound : ∀ {Σ} (P : iProp Σ), Persistent P.

(* Relational Semantic Path Typing. *)
Definition rsptp `{!dlangG Σ} p1 p2 i Γ (RV : vl_rel Σ) : iProp Σ :=
  <PB> ∀ ρ, sG⟦Γ⟧* ρ →
    ▷^i
    path_wp p1.|[ρ] (λI w1,
    path_wp p2.|[ρ] (λI w2,
      oClose RV ρ w1 w2)).
#[global] Arguments rsptp : simpl never.

(** Relational Semantic Subtyping. *)
Definition rsstpd `{!dlangG Σ} i Γ τ1 τ2 : iProp Σ :=
  <PB> ∀ ρ v1 v2,
    sG⟦Γ⟧*ρ → ▷^i (oClose τ1 ρ v1 v2 → oClose τ2 ρ v1 v2).
#[global] Arguments rsstpd : simpl never.

(** Delayed subtyping. *)
Notation "Γ rs⊨ T1 <:[ i  ] T2" := (rsstpd i Γ T1 T2) (at level 74, T1, T2 at next level).
(** Path typing *)
Notation "Γ rs⊨p p1 ~ p2 : τ , i" := (rsptp p1 p2 i Γ τ) (at level 74, p1, p1, τ, i at next level).

Section foo.
  Context `{HdotG : !dlangG Σ}.
  Implicit Types (RD : dm_rel Σ) (RDS : dms_rel Σ) (RV : vl_rel Σ) (SK : sf_kind Σ).

  Definition rlift_dm_dms l RD : dms_rel Σ := λI args ρ ds1 ds2,
    ∃ d1 d2, ⌜ dms_lookup l ds1 = Some d1 ∧ dms_lookup l ds2 = Some d2 ⌝ ∧
    RD args ρ d1 d2.
  Definition rlift_dm_vl l RD : vl_rel Σ := λI args ρ v1 v2,
    ∃ d1 d2, ⌜ v1 ,, l ↘ d1 ∧ v2 ,, l ↘ d2 ⌝ ∧
    RD args ρ d1 d2.

  (* Fixpoint ty_le (T : ty) (args : astream) (ρ1 ρ2 : env) (v1 v2 : vl) : iProp Σ :=
    match T with
    | TTop => True
    | TBot => False
    | TAnd T1 T2 =>
      ty_le T1 args ρ1 ρ2 v1 v2 ∧
      ty_le T2 args ρ1 ρ2 v1 v2
    | TOr T1 T2 =>
      ty_le T1 args ρ1 ρ2 v1 v2 ∨
      ty_le T2 args ρ1 ρ2 v1 v2
    | TLater T =>
      ▷ ty_le T args ρ1 ρ2 v1 v2
    | TPrim b => ⌜ v1 = v2 ⌝
    | TAll _ _ => False
    | TMu T =>
      ty_le T args (v1 .: ρ1) (v2 .: ρ2) v1 v2
    | _ => False
    end. *)
(* Print hoLty
Print hoD *)

  Definition rDVMem RV : dm_rel Σ := λI args ρ d1 d2,
    ∃ pmem1 pmem2, ⌜d1 = dpt pmem1⌝ ∧ ⌜d2 = dpt pmem2⌝ ∧
    path_wp pmem1 (λI w1, path_wp pmem2 (λI w2, RV args ρ w1 w2)).

  Definition rDTMem SK : dm_rel Σ := λI args ρ d1 d2,
    ∃ ψ1 ψ2, d1 ↗ ψ1 ∧ d2 ↗ ψ2 ∧
    (* Only one env here! *)
    SK ρ (packHoLtyO ψ1) (packHoLtyO ψ2).

  Definition rDAnd RD1 RD2 : dm_rel Σ := λI args ρ d1 d2,
    RD1 args ρ d1 d2 ∧ RD2 args ρ d1 d2.

  #[global] Instance rVTop : Top (vl_rel Σ) := λI args ρ v1 v2, True.
  #[global] Instance rVBot : Bottom (vl_rel Σ) := λI args ρ v1 v2, False.
  Definition rVAnd RV1 RV2 : vl_rel Σ := λI args ρ v1 v2, RV1 args ρ v1 v2 ∧ RV2 args ρ v1 v2.
  Definition rVOr RV1 RV2 : vl_rel Σ := λI args ρ v1 v2, RV1 args ρ v1 v2 ∨ RV2 args ρ v1 v2.
  Definition rVLater RV : vl_rel Σ := λI args ρ v1 v2, ▷ RV args ρ v1 v2.
  Definition rVAll RV1 RV2 : vl_rel Σ := ⊥.

  (* NOTE We use the "smaller" value! *)
  Definition rVMu1 RV : vl_rel Σ := λI args ρ v1 v2,
    □ RV args (v1 .: ρ) v1 v2.
  Class QuasiRefl RV : Prop :=
  { quasi_refl_l args ρ v1 v2 : RV args ρ v1 v2 ⊢ RV args ρ v1 v1
  ; quasi_refl_r args ρ v1 v2 : RV args ρ v1 v2 ⊢ RV args ρ v2 v2;
  }.
  Instance rVMu1_qper RV : QuasiRefl RV → QuasiRefl (rVMu1 RV).
  Proof.
    rewrite /rVMu1/=.
    constructor; intros; f_equiv.
    apply: quasi_refl_l.
    Fail apply: quasi_refl_r.
  Abort.

  Definition close RV : olty Σ := (* XXX better name *)
    Olty (λI args ρ v, □ RV args ρ v v).

  Lemma rsMu_Stp_Mu1 {Γ RV1 RV2 i} `{!SwapPropI Σ} `{!QuasiRefl RV1} :
    oLaterN i (close RV1) :: Γ rs⊨ RV1 <:[i] RV2 -∗
    Γ rs⊨ rVMu1 RV1 <:[i] rVMu1 RV2.
  Proof.
    pupd. iIntros "#Hstp !>" (ρ v1 v2) "#Hg".
    iApply mlaterN_impl. iIntros "#HT1".
    (* iApply ("Hstp" $! (v1 .: ρ) _ _ with "[$Hg] [HT1]"). *)
    iSpecialize ("Hstp" $! (v1 .: ρ) _ _ with "[$Hg] HT1").
    2: { iNext. iApply "Hstp". }
    iNext i.
    iModIntro.
    rewrite /rVMu1/=.
    iApply (quasi_refl_l with "[HT1]").
    iApply "HT1".
  Qed.

  (* NOTE We use both values! *)
  Definition rVMu RV : vl_rel Σ := λI args ρ v1 v2,
    □ (
      RV args (v1 .: ρ) v1 v2 ∧
      RV args (v2 .: ρ) v1 v2).

  #[global] Instance rVMu_qper RV : QuasiRefl RV → QuasiRefl (rVMu RV).
  Proof using HdotG.
    rewrite /rVMu/=.
    constructor; intros; iIntros "#[L R] !>".
    iSplit; by iApply quasi_refl_l.
    iSplit; by iApply quasi_refl_r.
  Qed.

  Lemma rsMu_Stp_Mu {Γ RV1 RV2 i} `{!SwapPropI Σ} `{!QuasiRefl RV1} :
    oLaterN i (close RV1) :: Γ rs⊨ RV1 <:[i] RV2 -∗
    Γ rs⊨ rVMu RV1 <:[i] rVMu RV2.
  Proof.
    pupd; iIntros "#Hstp !>" (ρ v1 v2) "#Hg".
    rewrite -mlaterN_impl /rVMu/= -!mlaterN_pers.
    iIntros "#[HT1 HT2] !>".
    iSplit; iApply ("Hstp" $! (_ .: ρ) _ _ with "[#$Hg]") => //; cbn.
    all: iNext i.
    iApply (quasi_refl_l with "HT1").
    iApply (quasi_refl_r with "HT2").
  Qed.
  #[global] Program Instance hsubst_vl_rel : HSubst vl (vl_rel Σ) :=
    λ sb RV args ρ, RV args (sb >> ρ).

  (* Doesn't typecheck. *)
  (* Lemma rVMu_shift RV : rVMu (shift RV) ≡ RV.
  Proof. move=> args ρ v. by rewrite /= (hoEnvD_weaken_one T args _ v). Qed. *)
  Lemma rsMu_Stp {Γ RV i} `{!QuasiRefl RV} :
    ⊢ Γ rs⊨ rVMu (shift RV) <:[i] RV.
  Proof.
    rewrite /rVMu /=.
    pupd; iIntros "!>" (???) "#Hg !> /= #[HT _]".
    (* by rewrite rVMu_shift. *)
    by rewrite/hsubst /hsubst_vl_rel; asimpl.
  Qed.

  (* XXX RV must be persistent *)
  Lemma rsStp_Mu {Γ RV i} `{!QuasiRefl RV} :
    ⊢ Γ rs⊨ RV <:[i] rVMu (shift RV).
  Proof.
    rewrite /rVMu /=.
    pupd; iIntros "!>" (???) "#Hg !> /= #HT !>".
    (* by rewrite rVMu_shift; iFrame. *)
    rewrite/hsubst /hsubst_vl_rel; asimpl. iFrame "HT".
  Qed.

  Definition rVVMem l RV : vl_rel Σ := λI args ρ v1 v2,
    rlift_dm_vl l (rDVMem RV) args ρ v1 v2.
  Definition rVTMem l SK : vl_rel Σ := λI args ρ v1 v2,
    rlift_dm_vl l (rDTMem SK) args ρ v1 v2.

  Definition vl_sel' vp l ψ : iProp Σ := ∃ d, ⌜vp ,, l ↘ d⌝ ∧ d ↗ ψ.
  (**
  XXX
  The sensible thing for parametricity needs two environments... but for type equivalence?
  What does it mean that "v1 and v2 are related at type p.A"?
  So we need to save a relation with each type :-(
  *)
  Definition rVSel p l : vl_rel Σ := λI args ρ v1 v2,
    ∃ ψ,
      path_wp p.|[ρ] (λI vp, vl_sel' vp l ψ) ∧
      ψ args v1 ∧ ψ args v2.

  Definition rVPrim b : vl_rel Σ := λI args ρ v1 v2,
    ⌜ v1 = v2 ⌝ ∧ oPrim b args ρ v1.
  Definition rVSing p : vl_rel Σ := λI args ρ v1 v2,
    oSing p args ρ v1 ∧ oSing p args ρ v2.
  Definition rVLam RV : vl_rel Σ := λI args ρ v1 v2,
    RV (atail args) (ahead args .: ρ) v1 v2.
  Definition rVApp RV p : vl_rel Σ := λI args ρ v1 v2,
    path_wp p.|[ρ] (λI w, RV (acons w args) ρ v1 v2).

  (* Path-refinement, half of path equality. With 1 environment! *)
  Fixpoint ty_le (T : ty) : vl_rel Σ :=
    match T with
    | TTop => rVTop
    | TBot => rVBot
    | TAnd T1 T2 =>
      rVAnd (ty_le T1) (ty_le T2)
    | TOr T1 T2 =>
      rVOr (ty_le T1) (ty_le T2)
    | TLater T =>
      rVLater (ty_le T)
    | TAll T1 T2 =>
      rVAll (ty_le T1) (ty_le T2)
    | TMu T =>
      rVMu (ty_le T)
    | TVMem l T =>
      rVVMem l (ty_le T)
    | kTTMem l K =>
      rVTMem l K⟦ K ⟧
    | kTSel _ p l => rVSel p l
    | TPrim b => rVPrim b
    | TSing p => rVSing p
    | TLam T => rVLam (ty_le T)
    | TApp T p => rVApp (ty_le T) p
    end.

  (* By induction, both values better be in V⟦ T ⟧ args ρ. *)
  (* Fixpoint ty_le_dm (T : ty) (args : astream) (ρ : env) (d1 d2 : dm) {struct T} : iProp Σ :=
    match T with
    | TTop => True
    | TAnd T1 T2 =>
      ty_le_dm T1 args ρ d1 d2 ∧
      ty_le_dm T2 args ρ d1 d2
    | TVMem l T =>
    | kTTMem l K =>
    | _ => False
    end
    with *)


End foo.
