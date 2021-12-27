From iris.algebra Require Import list.
From D Require Import iris_prelude proper lty lr_syn_aux.
From D Require Import iris_extra.det_reduction.
From D Require Import swap_later_impl.
From D.Dot Require Import syn path_repl.
From D.Dot Require Import dlang_inst path_wp.
From D.pure_program_logic Require Import weakestpre.
From D.Dot Require Import dot_lty dot_semtypes sem_kind_dot unary_lr.

(*
TODO:
focus on types we need for path equivalence, aka the arguments of type functions:
TA ::= mu x. TA | TA & TA | { A ::  K } | Top

Even something like:
TA ::= ... | { a : T }
while somewhat sensible, it goes beyond what we need, and takes in more types
(or should we use [{ a : TA }] ?).
*)

Implicit Types
  (Σ : gFunctors)
  (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
  (ρ : env) (l : label).
Implicit Types (K : kind).

Definition dm_rel Σ := ∀ (ρ1 ρ2 : env) (d1 d2 : dm), iProp Σ.
Definition dms_rel Σ := ∀ (ρ1 ρ2 : env) (ds1 ds2 : dms), iProp Σ.
Definition vl_rel Σ := ∀ (args1 args2 : astream) (ρ1 ρ2 : env) (v1 v2 : vl), iProp Σ.

Definition dm_relO Σ := env -d> env -d> dm -d> dm -d> iPropO Σ.
Definition dms_relO Σ := env -d> env -d> dms -d> dms -d> iPropO Σ.
Definition vl_relO Σ := astream -d> astream -d> env -d> env -d> vl -d> vl -d> iPropO Σ.

Definition rsCtxO Σ : ofe := listO (vl_relO Σ).

Reserved Notation "rG⟦ Γ ⟧*" (at level 10).
Fixpoint env_rstyped `{!dlangG Σ} (Γ : rsCtxO Σ) (ρ1 ρ2 : var → vl) : iProp Σ :=
  match Γ with
  | φ :: Γ' => rG⟦ Γ' ⟧* (stail ρ1) (stail ρ2) ∧ φ anil anil ρ1 ρ2 (shead ρ1) (shead ρ2)
  | [] => True
  end
where "rG⟦ Γ ⟧*" := (env_rstyped Γ).
#[global] Instance : Params (@env_rstyped) 2 := {}.

Section env_rstyped.
  Context `{!dlangG Σ}.
  #[global] Instance ids_vl_rel : Ids (vl_relO Σ) := λ _, inhabitant.
  #[global] Instance rename_vl_rel : Rename (vl_relO Σ) :=
    λ r RV args1 args2 ρ1 ρ2, RV args1 args2 (r >>> ρ1) (r >>> ρ2).

  #[global] Program Instance hsubst_vl_rel {Σ} : HSubst vl (vl_relO Σ) :=
    λ sb RV args1 args2 ρ1 ρ2, RV args1 args2 (sb >> ρ1) (sb >> ρ2).
  Ltac renLemmas_vl_rel :=
    hnf; rewrite /hsubst /hsubst_vl_rel => /= *;
    do 4 (apply FunctionalExtensionality.functional_extensionality_dep => ?); autosubst.

  #[global] Instance HSubstLemmas_vl_rel : HSubstLemmas vl (vl_relO Σ).
  Proof. split => //; renLemmas_vl_rel. Qed.
  #[global] Instance : Sort (vl_relO Σ) := {}.

  Definition env_rstyped_nil ρ1 ρ2 : rG⟦ [] ⟧* ρ1 ρ2 ⊣⊢ True := reflexivity _.
  Definition env_rstyped_cons ρ1 ρ2 τ (Γ : rsCtxO Σ) :
    rG⟦ τ :: Γ ⟧* ρ1 ρ2 ⊣⊢ rG⟦ Γ ⟧* (stail ρ1) (stail ρ2) ∧ τ anil anil ρ1 ρ2 (shead ρ1) (shead ρ2) := reflexivity _.

  #[global] Instance env_rstyped_ne n : Proper (dist n ==> eq ==> eq ==> dist n) (env_rstyped (Σ := Σ)).
  Proof.
    elim => [|T1 G1 IHG1] [|T2 G2] /=; [done|inversion 1..|] =>
      /(Forall2_cons_1 _ _ _ _) [HT HG] ρ1 _ <- ρ2 _ <-; f_equiv.
    { apply IHG1; [apply HG|done..]. }
    apply: HT.
  Qed.

  #[global] Instance env_rstyped_proper : Proper (equiv ==> eq ==> eq ==> equiv) (env_rstyped (Σ := Σ)).
  Proof.
    move=> Γ1 Γ2 /equiv_dist HΓ _ ρ1 -> _ ρ2 ->. apply /equiv_dist => n. exact: env_rstyped_ne.
  Qed.

  Lemma rs_interp_env_lookup (Γ : rsCtxO Σ) ρ1 ρ2 (RV : vl_relO Σ) x :
    Γ !! x = Some RV →
    rG⟦ Γ ⟧* ρ1 ρ2 -∗ shiftN x RV anil anil ρ1 ρ2 (ρ1 x) (ρ2 x).
  Proof.
    elim: Γ ρ1 ρ2 x => [//|τ' Γ' IHΓ] ρ1 ρ2 x Hx /=.
    iDestruct 1 as "[Hg Hv]". move: x Hx => [ [->] | x Hx] /=.
    - iApply "Hv".
    - iApply (IHΓ (stail ρ1) (stail ρ2) x Hx with "Hg").
  Qed.
End env_rstyped.

Section judgments.
  Context {Σ}.
  Implicit Types (RV : vl_relO Σ) (RD : dm_relO Σ) (RDS : dms_relO Σ).

  (* Relational Semantic Path Typing. *)
  Definition rsptp `{!dlangG Σ} p1 p2 i Γ RV : iProp Σ :=
    |==> ∀ ρ1 ρ2,
      rG⟦Γ⟧* ρ1 ρ2 →
      ▷^i
      path_wp p1.|[ρ1] (λI w1,
      path_wp p2.|[ρ2] (λI w2,
        RV anil anil ρ1 ρ2 w1 w2)).
  #[global] Arguments rsptp : simpl never.

  (** Relational Semantic Subtyping. *)
  Definition rsstpd `{!dlangG Σ} i Γ (RV1 RV2 : vl_relO Σ) : iProp Σ :=
    |==> ∀ ρ1 ρ2 v1 v2,
      rG⟦Γ⟧* ρ1 ρ2 →
      ▷^i (RV1 anil anil ρ1 ρ2 v1 v2 → RV2 anil anil ρ1 ρ2 v1 v2).
  #[global] Arguments rsstpd : simpl never.

  (** Multi-definition typing *)
  Definition rsdstp `{!dlangG Σ} ds1 ds2 Γ RDS : iProp Σ :=
    |==> ⌜wf_ds ds1⌝ ∧ ⌜wf_ds ds2⌝ ∧
      ∀ ρ1 ρ2,
      ⌜path_includes (pv (ids 0)) ρ1 ds1 ⌝ →
      ⌜path_includes (pv (ids 0)) ρ2 ds2 ⌝ →
      rG⟦Γ⟧* ρ1 ρ2 →
      RDS ρ1 ρ2 ds1.|[ρ1] ds2.|[ρ2].
  #[global] Arguments rsdstp : simpl never.

  (** Definition typing *)
  Definition rsdtp `{!dlangG Σ} l d1 d2 Γ RDS : iProp Σ :=
    rsdstp [(l, d1)] [(l, d2)] Γ RDS.
  #[global] Arguments rsdtp : simpl never.

  #[global] Instance rsstpd_proper `{!dlangG Σ} i : Proper3 (rsstpd i).
  Proof. solve_proper_ho. Qed.
End judgments.

#[global] Instance: Params (@rsstpd) 3 := {}.

(** Delayed subtyping. *)
Notation "Γ rs⊨ T1 <:[ i  ] T2" := (rsstpd i Γ T1 T2) (at level 74, T1, T2 at next level).
(** Path typing *)
Notation "Γ rs⊨p p1 == p2 : τ , i" := (rsptp p1 p2 i Γ τ)
  (at level 74, p1, p2, τ, i at next level).
(** Single-definition typing *)
Notation "Γ rs⊨ {  l := d1 = d2  } : T" := (rsdtp l d1 d2 Γ T) (at level 64, d1, d2, l, T at next level).
(** Multi-definition typing *)
Notation "Γ rs⊨ds ds1 = ds2  : T" := (rsdstp ds1 ds2 Γ T) (at level 64, ds1, ds2, T at next level).

Definition rVLaterN {Σ} n (RV : vl_relO Σ) : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2, ▷^n RV args1 args2 ρ1 ρ2 v1 v2.
Notation rVLater := (rVLaterN 1).
#[global] Instance: Params (@rVLaterN) 2 := {}.

Section foo.
  Context `{HdotG : !dlangG Σ}.
  Set Default Proof Using "HdotG".
  Implicit Types (RD : dm_rel Σ) (RDS : dms_rel Σ) (RV : vl_relO Σ).
  Implicit Types (T : olty Σ) (SK : sf_kind Σ).

  Definition rlift_dm_dms l RD : dms_rel Σ := λI ρ1 ρ2 ds1 ds2,
    ∃ d1 d2, ⌜ dms_lookup l ds1 = Some d1 ∧ dms_lookup l ds2 = Some d2 ⌝ ∧
    RD ρ1 ρ2 d1 d2.
  Definition rlift_dm_vl l RD : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2,
    ∃ d1 d2, ⌜ v1 @ l ↘ d1 ∧ v2 @ l ↘ d2 ⌝ ∧
    RD ρ1 ρ2 d1 d2.

  (* Fixpoint ty_le (T : ty) (args1 args2 : astream) (ρ1 ρ2 : env) (v1 v2 : vl) : iProp Σ :=
    match T with
    | TTop => True
    | TBot => False
    | TAnd T1 T2 =>
      ty_le T1 args1 args2 ρ1 ρ2 v1 v2 ∧
      ty_le T2 args1 args2 ρ1 ρ2 v1 v2
    | TOr T1 T2 =>
      ty_le T1 args1 args2 ρ1 ρ2 v1 v2 ∨
      ty_le T2 args1 args2 ρ1 ρ2 v1 v2
    | TLater T =>
      ▷ ty_le T args1 args2 ρ1 ρ2 v1 v2
    | TPrim b => ⌜ v1 = v2 ⌝
    | TAll _ _ => False
    | TMu T =>
      ty_le T args1 args2 (v1 .: ρ1) (v2 .: ρ2) v1 v2
    | _ => False
    end. *)
(* Print hoLty
Print hoD *)

  Definition rDVMem RV : dm_rel Σ := λI ρ1 ρ2 d1 d2,
    ∃ pmem1 pmem2, ⌜d1 = dpt pmem1⌝ ∧ ⌜d2 = dpt pmem2⌝ ∧
    path_wp pmem1 (λI w1, path_wp pmem2 (λI w2, RV anil anil ρ1 ρ2 w1 w2)).

  Definition rDTMemK SK : dm_rel Σ := λI ρ1 ρ2 d1 d2,
    ∃ ψ1 ψ2, d1 ↗ ψ1 ∧ d2 ↗ ψ2 ∧
    (* Only one env here! *)
    SK ρ1 (packHoLtyO ψ1) (packHoLtyO ψ2).

  Definition rDAnd RD1 RD2 : dm_rel Σ := λI ρ1 ρ2 d1 d2,
    RD1 ρ1 ρ2 d1 d2 ∧ RD2 ρ1 ρ2 d1 d2.

  #[global] Instance rVTop : Top (vl_relO Σ) := λI args1 args2 ρ1 ρ2 v1 v2, True.
  #[global] Instance rVBot : Bottom (vl_relO Σ) := λI args1 args2 ρ1 ρ2 v1 v2, False.
  Definition rVAnd RV1 RV2 : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2, RV1 args1 args2 ρ1 ρ2 v1 v2 ∧ RV2 args1 args2 ρ1 ρ2 v1 v2.
  Definition rVOr RV1 RV2 : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2, RV1 args1 args2 ρ1 ρ2 v1 v2 ∨ RV2 args1 args2 ρ1 ρ2 v1 v2.
  Definition rVAll RV1 RV2 : vl_relO Σ := ⊥.

  Definition close RV : olty Σ := (* XXX better name *)
    Olty (λI args ρ v, RV args args ρ ρ v v).
  (* XXX Better name since we add more props *)
  Class QuasiRefl RV T : Prop :=
  { quasi_refl_l args1 args2 ρ1 ρ2 v1 v2 : RV args1 args2 ρ1 ρ2 v1 v2 ⊢ close RV args1 ρ1 v1
  ; quasi_refl_r args1 args2 ρ1 ρ2 v1 v2 : RV args1 args2 ρ1 ρ2 v1 v2 ⊢ close RV args2 ρ2 v2
  ; to_olty args ρ v : close RV args ρ v ⊣⊢ T args ρ v
  }.
(*
  (* NOTE We use the "smaller" value! *)
  Definition rVMu1 RV : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2,
    RV args1 args2 (v1 .: ρ) v1 v2.

  Instance rVMu1_qper RV : QuasiRefl RV → QuasiRefl (rVMu1 RV).
  Proof.
    rewrite /rVMu1/=.
    constructor; intros.
    apply: quasi_refl_l.
    Fail apply: quasi_refl_r.
  Abort.

  Lemma rsMu_Stp_Mu1 {Γ RV1 RV2 i} `{!SwapPropI Σ} `{!QuasiRefl RV1} :
    oLaterN i (close RV1) :: Γ rs⊨ RV1 <:[i] RV2 -∗
    Γ rs⊨ rVMu1 RV1 <:[i] rVMu1 RV2.
  Proof.
    iIntros ">#Hstp !>" (ρ v1 v2) "Hg".
    iApply mlaterN_impl. iIntros "#HT1".
    iApply ("Hstp" $! (v1 .: ρ) _ _ with "[$Hg] HT1").
    iNext i.
    rewrite /rVMu1/=.
    iApply (quasi_refl_l with "HT1").
  Qed. *)

  Definition rVMu RV : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2,
    RV args1 args2 (v1 .: ρ1) (v2 .: ρ2) v1 v2.

  #[global] Instance rVMu_qper RV T : QuasiRefl RV T → QuasiRefl (rVMu RV) (oMu T).
  Proof.
    rewrite /rVMu/=.
    constructor; intros; rewrite /close/=. 3: { apply to_olty. }
    all: iIntros "#H".
    - by iApply quasi_refl_l.
    - by iApply quasi_refl_r.
  Qed.

  Lemma rsMu_Stp_Mu {Γ RV1 RV2 i} `{!SwapPropI Σ} :
    rVLaterN i RV1 :: Γ rs⊨ RV1 <:[i] RV2 -∗
    Γ rs⊨ rVMu RV1 <:[i] rVMu RV2.
  Proof.
    iIntros ">#Hstp !>" (ρ1 ρ2 v1 v2) "Hg". iApply mlaterN_impl. iIntros "#HT".
    rewrite /rVMu/=. iApply ("Hstp" $! (_ .: ρ1) (_ .: ρ2) _ _ with "[$Hg] HT").
    iApply "HT".
  Qed.

  Lemma rVMu_shift RV : rVMu (shift RV) ≡ RV.
  Proof. done. Qed.

  Lemma rsStp_Refl {Γ RV i} :
    ⊢ Γ rs⊨ RV <:[i] RV.
  Proof. iIntros "!>" (????) "#Hg !> /= #$". Qed.

  (*
  Goal ∃ r : relation (vl_rel Σ),
    Proper (respectful (≡@{vl_relO Σ}) (respectful r (flip impl))) equiv.
    unfold vl_rel.
    progress unfold vl_relO.
    Fail progress unfold vl_rel.
  eexists.
      Set Typeclasses Debug Verbosity 3.
  (* simple apply trans_co_eq_inv_impl_morphism. *)
  typeclasses eauto. *)

  Lemma rsMu_Stp {Γ RV i} :
    ⊢ Γ rs⊨ rVMu (shift RV) <:[i] RV.
  Proof.
    (* XXX Very slow! *)
    (* rewrite rVMu_shift. apply rsStp_Refl. *)
(*
    eapply bi_emp_valid_proper.
    apply rsstpd_proper; [done|..|done].
    simple apply (rVMu_shift RV).
    simple apply rsStp_Refl. *)

    (* Set Debug Tactic Unification. *)

    iIntros "!>" (????) "#Hg !> /= #HT".
    iApply "HT".
  Qed.

  Lemma rsStp_Mu {Γ RV i} :
    ⊢ Γ rs⊨ RV <:[i] rVMu (shift RV).
  Proof.
    iIntros "!>" (????) "#Hg !> /= #HT".
    iApply "HT".
  Qed.

  Definition rVVMem l RV : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2,
    rlift_dm_vl l (rDVMem RV) args1 args2 ρ1 ρ2 v1 v2.
  Definition rVTMemK l SK : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2,
    rlift_dm_vl l (rDTMemK SK) args1 args2 ρ1 ρ2 v1 v2.

From D.Dot Require Import hkdot.
Import HkDot.

  (* Lemma rD_TypK_Abs {Γ} T (K : sf_kind Σ) s σ l :
    Γ rs⊨ oLater T ∷[ 0 ] K -∗
    s ↝[ σ ] T -∗
    Γ rs⊨ { l := dtysem σ s } : cTMemK l K. *)

  (* Lemma rVTy_intro l Γ i SK s σ T :
    let v := vobj [(l, dtysem σ s)] in
    s ↝[ σ ] T -∗
    Γ rs⊨p pv v == pv v : rVTMemK l SK, i. *)
  Lemma rVTy_intro l Γ i SK s σ T :
    let v := vobj [(l, dtysem σ s)] in
    s ↝[ σ ] T -∗
    Γ rs⊨p pv v == pv v : rVMu (rVTMemK l (sf_sngl (oLater T))), i.
  Proof.
    intros v.
    rewrite /rsptp.
    iDestruct 1 as (φ Hγφ) "#Hγ".
    iIntros "!>" (??) "#Hg !> /=".
    rewrite !path_wp_pv_eq /= /rVTMemK /rlift_dm_vl /rDTMemK /=.
    iExists _, _; iSplit; first iIntros "!%".
    {
      split; red; eexists; split_and! => //;
        apply dms_lookup_head.
    }
    cbn.
    set σ1 := σ.|[up ρ1].|[v.[ρ1]/].
    set σ2 := σ.|[up ρ2].|[v.[ρ2]/].
    iExists (hoEnvD_inst σ1 φ), (hoEnvD_inst σ2 φ).
    do 2 (iSplit; [by iApply (dm_to_type_intro with "Hγ")|]).
    (* by iSplit; iIntros (w) "#H"; iNext; rewrite /= (Hγφ _ _). *)
    repeat iSplit; iIntros (w) "#H /="; iNext.
    all: rewrite /= {}/σ1 {}/σ2.
    all: rewrite /= ?(Hγφ _ _) //=.
    { asimpl. iApply "H". }
    admit.
    admit.
    (* Both goals suffer from an environment mismatch.
    But they might follow if we know that T has kind K... which would require T
    to respect the relation between environments!
    In turn, we must check that all types respect all the relational semantics.
    *)
  Admitted.

  (* Lemma rVTy_intro l Γ i SK (T : ty) :
    let p := pv (vobj [(l, dtysyn T)]) in
    ⊢ Γ rs⊨p p == p : rVTMemK l SK, i.
  Proof.
    rewrite /rsptp.
    iIntros "!>" (??) "#Hg !> /=".
    rewrite !path_wp_pv_eq /=.
    rewrite /rVTMemK /rlift_dm_vl.
    iExists _, _; iSplit; first iIntros "!%".
    {
      split; red; eexists; split_and! => //;
        apply dms_lookup_head.
    }
    unfold rDTMemK.
    iExists (hoEnvD_inst (σ.|[ρ]) φ). iSplit.
    by iApply (dm_to_type_intro with "Hγ").
    by iSplit; iIntros (v) "#H"; iNext; rewrite /= (Hγφ _ _). *)

  Definition vl_sel' vp l ψ : iProp Σ := ∃ d, ⌜vp @ l ↘ d⌝ ∧ d ↗ ψ.
  (**
  XXX
  The sensible thing for parametricity needs two environments... but for path/type equivalence?
  What does it mean that "v1 and v2 are related at type p.A"?
  So we need to save a relation with each type :-(
  XXX2 : luckily, we don't really need this for path equivalence.
  *)
  Definition rVSel p l : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2,
    ∃ (ψ1 ψ2 : hoD Σ),
      path_wp p.|[ρ1] (λI vp, vl_sel' vp l ψ1) ∧
      ψ1 args1 v1 ∧
      path_wp p.|[ρ1] (λI vp, vl_sel' vp l ψ2) ∧
      ψ2 args2 v2.

  Definition rVPrim b : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2,
    ⌜ v1 = v2 ⌝ ∧ oPrim b args1 ρ1 v1 ∧ oPrim b args2 ρ2 v2.
  #[global] Instance: `{QuasiRefl (rVPrim b) (oPrim b)}.
  Proof.
    rewrite /rVPrim; constructor; intros; simpl; last iSplit.
    4: by iIntros "#$".
    all: by iIntros "#(? & ? & ?)"; iFrame "#".
  Qed.
  Definition rVSing p : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2,
    oSing p args1 ρ1 v1 ∧ oSing p args2 ρ2 v2.
  Definition rVLam RV : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2,
    RV (atail args1) (atail args2) (ahead args1 .: ρ1) (ahead args2 .: ρ2) v1 v2.
  Definition rVApp RV p : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2,
    path_wp p.|[ρ1] (λI w1,
    path_wp p.|[ρ2] (λI w2,
    RV (acons w1 args1) (acons w2 args2) ρ1 ρ2 v1 v2)).

  (* Path-refinement, half of path equality. With 1 environment! *)
  Fixpoint ty_le (T : ty) : vl_relO Σ :=
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
      rVTMemK l K⟦ K ⟧
    | kTSel _ p l => rVSel p l
    | TPrim b => rVPrim b
    | TSing p => rVSing p
    | TLam T => rVLam (ty_le T)
    | TApp T p => rVApp (ty_le T) p
    end.
  (* By induction, both values better be in V⟦ T ⟧ args1 args2 ρ. *)


End foo.

(* Exercise for the reader: remember the point is that all _consumers_ respect
path equality. So for each elimination rule from supported types, we must prove
functionality! *)
