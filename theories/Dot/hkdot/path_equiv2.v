From iris.algebra Require Import list.
From D.pure_program_logic Require Import weakestpre.
From D Require Import iris_prelude lr_syn_aux lty.
From D Require Import iris_extra.det_reduction.
From D Require Import swap_later_impl.
From D.Dot Require Import syn path_repl.
From D.Dot Require Import dlang_inst path_wp.
From D.Dot Require Import dot_lty dot_semtypes sem_kind_dot unary_lr.
From D.Dot Require Import hkdot.
Import HkDot.
(* Import last to override side effects. *)
From D Require Import proper.

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
SubClass dms_rel Σ := ∀ (ρ1 ρ2 : env) (ds1 ds2 : dms), iProp Σ.
Definition vl_rel Σ := ∀ (args1 args2 : astream) (ρ1 ρ2 : env) (v1 v2 : vl), iProp Σ.

Definition dm_relO Σ := env -d> env -d> dm -d> dm -d> iPropO Σ.
Definition dms_relO Σ := env -d> env -d> dms -d> dms -d> iPropO Σ.
Definition vl_relO Σ := astream -d> astream -d> env -d> env -d> vl -d> vl -d> iPropO Σ.

(** ** A "coherent" relational type, containing all semantics of a type.
That is, semantics for both definition lists and values, and proofs that they
agree appropriately. *)
Module crel_mixin.
  #[local] Set Primitive Projections.
  Record pred {Σ} (RDS : dms_rel Σ) (RV : vl_rel Σ) : Prop := Mk {
    def2defs_head {l d1 d2 ds1 ds2 ρ1 ρ2} :
      RDS ρ1 ρ2 [(l, d1)] [(l, d2)] ⊢ RDS ρ1 ρ2 ((l, d1) :: ds1) ((l, d2) :: ds2);
    mono {l d1 d2 ds1 ds2 ρ1 ρ2} :
      dms_hasnt ds1 l → dms_hasnt ds2 l →
      RDS ρ1 ρ2 ds1 ds2 ⊢ RDS ρ1 ρ2 ((l, d1) :: ds1) ((l, d2) :: ds2);
    commute {ds1 ds2 ρ1 ρ2} :
      RDS ρ1 ρ2 (selfSubst ds1) (selfSubst ds2) ⊢ RV anil anil ρ1 ρ2 (vobj ds1) (vobj ds2);
  }.
End crel_mixin.
Arguments crel_mixin.Mk {Σ _ _}.

Module crel.
  Record t {Σ} := Mk {
    to_dms :> dms_rel Σ;
    to_vl : vl_relO Σ;
    mixin : crel_mixin.pred to_dms to_vl;
  }.
  #[global] Arguments t : clear implicits.
  #[global] Arguments Mk {Σ}.
  Arguments to_dms {_} !_.
  #[global] Instance : Params (@to_dms) 1 := {}.
  Arguments to_vl {_} !_.
  #[global] Instance : Params (@to_vl) 1 := {}.
End crel.
Add Printing Constructor crel.t.
Notation c2v := crel.to_vl.
Coercion crel.to_dms : crel.t >-> dms_rel.
Notation CRel RDS RV := (crel.Mk RDS RV (crel_mixin.Mk _ _ _)).

Section crel_mixin'.
  Context {Σ} (c : crel.t Σ).
  Import crel crel_mixin.

  Lemma crel_def2defs_head {l d1 d2 ds1 ds2 ρ1 ρ2} :
    to_dms c ρ1 ρ2 [(l, d1)] [(l, d2)] ⊢ to_dms c ρ1 ρ2 ((l, d1) :: ds1) ((l, d2) :: ds2).
  Proof. apply /def2defs_head /mixin. Qed.
  Lemma crel_mono {l d1 d2 ds1 ds2 ρ1 ρ2} :
      dms_hasnt ds1 l → dms_hasnt ds2 l →
      to_dms c ρ1 ρ2 ds1 ds2 ⊢ to_dms c ρ1 ρ2 ((l, d1) :: ds1) ((l, d2) :: ds2).
  Proof. apply /mono /mixin. Qed.

  Lemma crel_commute {ds1 ds2 ρ1 ρ2} :
    to_dms c ρ1 ρ2 (selfSubst ds1) (selfSubst ds2) ⊢ to_vl c anil anil ρ1 ρ2 (vobj ds1) (vobj ds2).
  Proof. apply /commute /mixin. Qed.
End crel_mixin'.

Section crel_ofe.
  Import crel.
  Context {Σ}.

  Let crel_car : Type := dms_relO Σ * vl_relO Σ.

  Let iso : crel.t Σ -> crel_car :=
    λ T : crel.t Σ, (to_dms T, to_vl T).
  #[local] Instance crel_equiv : Equiv (crel.t Σ) := λ A B, iso A ≡ iso B.
  #[local] Instance crel_dist : Dist (crel.t Σ) := λ n A B, iso A ≡{n}≡ iso B.
  Lemma crel_ofe_mixin : OfeMixin (crel.t Σ).
  Proof. exact: (iso_ofe_mixin iso). Qed.

  Canonical Structure crelO := Ofe (crel.t Σ) crel_ofe_mixin.

  Let crel_pred : crel_car -> Prop := uncurry crel_mixin.pred.

  Let crel_pred_alt (c : crel_car) : Prop :=
    let RDS := fst c in
    let RV := snd c in
    (∀ l d1 d2 ds1 ds2 ρ1 ρ2,
      RDS ρ1 ρ2 [(l, d1)] [(l, d2)] ⊢ RDS ρ1 ρ2 ((l, d1) :: ds1) ((l, d2) :: ds2)) ∧
    (∀ l d1 d2 ds1 ds2 ρ1 ρ2,
      dms_hasnt ds1 l → dms_hasnt ds2 l →
      RDS ρ1 ρ2 ds1 ds2 ⊢ RDS ρ1 ρ2 ((l, d1) :: ds1) ((l, d2) :: ds2)) ∧
    (∀ ds1 ds2 ρ1 ρ2,
      RDS ρ1 ρ2 (selfSubst ds1) (selfSubst ds2) ⊢ RV anil anil ρ1 ρ2 (vobj ds1) (vobj ds2)).

  #[local] Instance : LimitPreserving crel_pred.
  Proof.
    apply (limit_preserving_ext crel_pred_alt). {
      move=> [RDS RV]; rewrite /crel_pred_alt /crel_pred; split => H.
      by destruct_and?.
      by destruct H.
    }
    repeat apply limit_preserving_and;
      repeat (apply limit_preserving_forall; intro);
      repeat apply limit_preserving_entails;
      move=> n [RDS1 RV1] [RDS2 RV2] [/= Hds Hv];
      first [apply: Hds|apply: Hv].
  Qed.

  #[global] Instance cofe_crel : Cofe crelO.
  Proof.
    apply (iso_cofe_subtype' crel_pred (λ '(ds, o), crel.Mk ds o) iso).
    by case.
    by [].
    by case.
    apply _.
  Qed.
End crel_ofe.
Arguments crelO : clear implicits.

Section crel_ofe_proper.
  Import crel.
  Context {Σ}.

  #[global] Instance crel_to_vl_ne : NonExpansive (crel.to_vl (Σ := Σ)).
  Proof. by move=> ???[/= _ H]. Qed.
  #[global] Instance crel_to_vl_proper : Proper1 (crel.to_vl (Σ := Σ)) :=
    ne_proper _.

  (* TODO: How should this instance be best written? *)
  #[global] Instance crel_to_dms_ne n :
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) (crel.to_dms (Σ := Σ)).
  Proof. intros ?? [Heq _]. solve_proper_ho. Qed.
  #[global] Instance crel_to_dms_proper :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) (crel.to_dms (Σ := Σ)).
  Proof. intros ?? [Heq _]. solve_proper_ho. Qed.
End crel_ofe_proper.

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

(* XXX we use [ρ1] asymmetrically, matching the [rDTMemK]. But this can't work! *)
Notation rsstpiK_env i T1 T2 K ρ1 ρ2 := (▷^i K ρ1 (envApply T1 ρ1) (envApply T2 ρ2))%I.
Notation rsstpiK' i Γ T1 T2 K := (∀ ρ1 ρ2, rG⟦Γ⟧* ρ1 ρ2 → rsstpiK_env i T1 T2 K ρ1 ρ2)%I.
Definition rsstpiK `{!dlangG Σ} i Γ T1 T2 (K : sf_kind Σ) : iProp Σ :=
  |==> rsstpiK' i Γ T1 T2 K.

Section judgments.
  Context {Σ}.
  Implicit Types (RV : vl_relO Σ) (RD : dm_relO Σ) (RDS : dms_relO Σ) (RC : crel.t Σ).

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
  Definition rsdstp `{!dlangG Σ} ds1 ds2 Γ RC : iProp Σ :=
    |==> ⌜wf_ds ds1⌝ ∧ ⌜wf_ds ds2⌝ ∧
      ∀ ρ1 ρ2,
      ⌜path_includes (pv (ids 0)) ρ1 ds1 ⌝ →
      ⌜path_includes (pv (ids 0)) ρ2 ds2 ⌝ →
      rG⟦Γ⟧* ρ1 ρ2 →
      RC ρ1 ρ2 ds1.|[ρ1] ds2.|[ρ2].
  #[global] Arguments rsdstp : simpl never.

  (** Definition typing *)
  Definition rsdtp `{!dlangG Σ} l d1 d2 Γ RC : iProp Σ :=
    rsdstp [(l, d1)] [(l, d2)] Γ RC.
  #[global] Arguments rsdtp : simpl never.

  #[global] Instance rsptp_proper `{!dlangG Σ} p1 p2 i : Proper2 (rsptp p1 p2 i).
  Proof. solve_proper_ho. Qed.
  #[global] Instance rsstpd_proper `{!dlangG Σ} i : Proper3 (rsstpd i).
  Proof. solve_proper_ho. Qed.

  (* Problems if we don't import [proper] last (https://github.com/coq/coq/issues/12206). *)
  (* #[global] Instance rsdstp_proper (* `{!dlangG Σ} *) ds1 ds2 : Proper2 (rsdstp ds1 ds2).
  Proof.
    (* { solve_proper_ho. } *)
    Import D.prelude.
    (* XXX repeat side effects *)
    solve_proper_prepare; repeat no_eq_f_equiv.
    { solve_proper_ho. }
(* From D Require Import proper.  *)
    Fail f_equiv.
    Import D.proper.
    by f_equiv.
    Undo.
    Import stdpp.tactics.
    Fail f_equiv.
    Import D.proper.
    by f_equiv.
  Abort. *)
  #[global] Instance rsdstp_proper `{!dlangG Σ} ds1 ds2 : Proper2 (rsdstp ds1 ds2).
  Proof. solve_proper_ho. Qed.

  #[global] Instance rsdtp_proper `{!dlangG Σ} l d1 d2 : Proper2 (rsdtp l d1 d2).
  Proof. solve_proper_ho. Qed.

  #[global] Instance rsstpiK_proper `{!dlangG Σ} i : Proper4 (rsstpiK i).
  Proof. solve_proper_ho. Qed.
End judgments.

#[global] Instance: Params (@rsptp) 5 := {}.
#[global] Instance: Params (@rsstpd) 3 := {}.
#[global] Instance: Params (@rsdstp) 4 := {}.
#[global] Instance: Params (@rsdtp) 5 := {}.
#[global] Instance: Params (@rsstpiK) 3 := {}.

(** Delayed subtyping. *)
Notation "Γ rs⊨ T1 <:[ i  ] T2" := (rsstpd i Γ T1 T2) (at level 74, T1, T2 at next level).
(** Path typing *)
Notation "Γ rs⊨p p1 = p2 : τ , i" := (rsptp p1 p2 i Γ τ)
  (at level 64, p1, p2, τ, i at next level).
(** Single-definition typing *)
Notation "Γ rs⊨ {  l := d1 = d2  } : T" := (rsdtp l d1 d2 Γ T) (at level 64, d1, d2, l, T at next level).
(** Multi-definition typing *)
Notation "Γ rs⊨ds ds1 = ds2  : T" := (rsdstp ds1 ds2 Γ T) (at level 64, ds1, ds2, T at next level).

(* TODO <:: could work for base subtyping? It's really meant for subkinding
but... *)
Notation "Γ rs⊨ T1 <::[ i  ] T2 ∷ K" := (rsstpiK i Γ T1 T2 K)
  (at level 74, i, T1, T2, K at next level).
Notation "Γ rs⊨ T1 =[ i  ] T2 ∷ K" :=
  (Γ rs⊨ T1 <::[ i  ] T2 ∷ K ∧ Γ rs⊨ T2 <::[ i  ] T1 ∷ K)%I
  (at level 74, i, T1, T2, K at next level).
Notation "Γ rs⊨ T ∷[ i  ] K" := (Γ rs⊨ T <::[ i ] T ∷ K)
  (at level 74, T, K at next level).


Definition rVLaterN {Σ} n (RV : vl_relO Σ) : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2, ▷^n RV args1 args2 ρ1 ρ2 v1 v2.
Notation rVLater := (rVLaterN 1).
#[global] Instance: Params (@rVLaterN) 2 := {}.

Definition rlift_dm_dms `{!dlangG Σ} l (RD : dm_relO Σ) : dms_relO Σ := λI ρ1 ρ2 ds1 ds2,
  ∃ d1 d2, ⌜ dms_lookup l ds1 = Some d1 ∧ dms_lookup l ds2 = Some d2 ⌝ ∧
  RD ρ1 ρ2 d1 d2.
Definition rlift_dm_vl `{!dlangG Σ} l (RD : dm_relO Σ) : vl_relO Σ := λI args1 args2 ρ1 ρ2 v1 v2,
  ∃ d1 d2, ⌜ v1 @ l ↘ d1 ∧ v2 @ l ↘ d2 ⌝ ∧
  RD ρ1 ρ2 d1 d2.
Section rlift_dm_lemmas.
  Context `{HdotG : !dlangG Σ}.
  #[local] Arguments dms_lookup : simpl never.

  Lemma rlift_dm_dms_head_intro RD l1 l2 ρ1 ρ2 d1 d2 ds1 ds2 (Heq : l1 = l2) :
    RD ρ1 ρ2 d1 d2 -∗
    rlift_dm_dms l1 RD ρ1 ρ2 ((l2, d1) :: ds1) ((l2, d2) :: ds2).
  Proof. rewrite Heq /rlift_dm_dms !dms_lookup_head. eauto 10. Qed.

  Lemma rlift_dm_dms_singleton_eq' RD l1 l2 ρ1 ρ2 d1 d2 :
    rlift_dm_dms l1 RD ρ1 ρ2 [(l2, d1)] [(l2, d2)] ⊣⊢
    ⌜ l1 = l2 ⌝ ∧ RD ρ1 ρ2 d1 d2.
  Proof.
    rewrite /rlift_dm_dms; iSplit. {
      iDestruct 1 as (d1' d2' [?%dms_lookup_head_inv ?%dms_lookup_head_inv]) "?".
      naive_solver.
    }
    iIntros "[<- ?]". by iApply rlift_dm_dms_head_intro.
  Qed.

  Lemma rlift_dm_dms_singleton_eq RD l ρ1 ρ2 d1 d2 :
    rlift_dm_dms l RD ρ1 ρ2 [(l, d1)] [(l, d2)] ⊣⊢
    RD ρ1 ρ2 d1 d2.
  Proof.
    by rewrite rlift_dm_dms_singleton_eq' pure_True // (left_id True%I bi_and).
  Qed.

  #[program] Definition rlift_dm_c l (RD : dm_relO Σ) : crel.t Σ :=
    CRel (rlift_dm_dms l RD) (rlift_dm_vl l RD).
  Next Obligation.
    intros. rewrite rlift_dm_dms_singleton_eq'.
    iIntros "[<- ?]". by iApply rlift_dm_dms_head_intro.
  Qed.
  Next Obligation.
    intros. rewrite /rlift_dm_dms. f_equiv => d1'; f_equiv => d2'.
    iDestruct 1 as ([Hl1 Hl2]) "H".
    repeat erewrite dms_lookup_mono => //. eauto.
  Qed.
  Next Obligation.
    intros. rewrite /rlift_dm_dms /rlift_dm_vl. f_equiv => d1; f_equiv => d2.
    iDestruct 1 as ([Hl1 Hl2]) "$".
    iIntros "!%"; split; exact: objLookupIntro.
  Qed.
  Lemma rlift_dm_c_singleton l RD ρ1 ρ2 d1 d2 :
    rlift_dm_c l RD ρ1 ρ2 [(l, d1)] [(l, d2)] ≡ RD ρ1 ρ2 d1 d2.
  Proof. apply rlift_dm_dms_singleton_eq. Qed.

  #[global] Instance rlift_dm_dms_ne l : NonExpansive (rlift_dm_dms l).
  Proof. solve_proper_ho. Qed.
  #[global] Instance rlift_dm_dms_proper l : Proper1 (rlift_dm_dms l) :=
    ne_proper _.
  #[global] Instance rlift_dm_vl_ne l : NonExpansive (rlift_dm_vl l).
  Proof. solve_proper_ho. Qed.
  #[global] Instance rlift_dm_vl_proper l : Proper1 (rlift_dm_vl l) :=
    ne_proper _.

  #[global] Instance rlift_dm_c_ne l : NonExpansive (rlift_dm_c l).
  Proof. rewrite /rlift_dm_c; split => /=; solve_proper_ho. Qed.

  #[global] Instance rlift_dm_c_proper l : Proper1 (rlift_dm_c l) :=
    ne_proper _.
End rlift_dm_lemmas.
#[global] Instance : Params (@rlift_dm_c) 3 := {}.

Section foo.
  Context `{HdotG : !dlangG Σ}.
  Set Default Proof Using "HdotG".
  Implicit Types (RD : dm_rel Σ) (RDS : dms_rel Σ) (RV : vl_relO Σ).
  Implicit Types (T : olty Σ) (SK : sf_kind Σ).
  Implicit Types (RC : crel.t Σ).

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

  Definition rVTop : vl_relO Σ := ⊤.
  Definition rVBot : vl_relO Σ := ⊥.
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

  Definition rCVMem l RV : crel.t Σ :=
    rlift_dm_c l (rDVMem RV).
  Definition rCTMemK l SK : crel.t Σ :=
    rlift_dm_c l (rDTMemK SK).

  Notation rVVMem l RV := (c2v (rCVMem l RV)).
  Notation rVTMemK l SK := (c2v (rCTMemK l SK)).

  #[program] Definition rCAnd RC1 RC2 : crel.t Σ :=
    CRel
      (λI ρ1 ρ2 ds1 ds2, RC1 ρ1 ρ2 ds1 ds2 ∧ RC2 ρ1 ρ2 ds1 ds2)
      (rVAnd (c2v RC1) (c2v RC2)).
  Next Obligation. intros. by rewrite /= -!crel_def2defs_head. Qed.
  Next Obligation. intros. by rewrite /= -!crel_mono. Qed.
  Next Obligation. intros. by rewrite /rVAnd -!crel_commute. Qed.

  Lemma rsdtp_eq Γ RC l d1 d2 :
    Γ rs⊨ { l := d1 = d2 } : RC ⊣⊢
    |==> ∀ ρ1 ρ2,
      ⌜path_includes (pv (ids 0)) ρ1 [(l, d1)] ⌝ →
      ⌜path_includes (pv (ids 0)) ρ2 [(l, d2)] ⌝ →
      rG⟦Γ⟧* ρ1 ρ2 →
      RC ρ1 ρ2 [(l, d1.|[ρ1])] [(l, d2.|[ρ2])].
  Proof.
    rewrite /rsdtp /rsdstp /= !pure_True ?(left_id _ bi_and) //.
    exact: NoDup_singleton.
  Qed.

  Lemma rsdtp_eq' Γ RD l d1 d2 :
    Γ rs⊨ { l := d1 = d2 } : rlift_dm_c l RD ⊣⊢
    |==> ∀ ρ1 ρ2,
      ⌜path_includes (pv (ids 0)) ρ1 [(l, d1)] ⌝ →
      ⌜path_includes (pv (ids 0)) ρ2 [(l, d2)] ⌝ →
      rG⟦Γ⟧* ρ1 ρ2 →
      RD ρ1 ρ2 d1.|[ρ1] d2.|[ρ2].
  Proof. rewrite rsdtp_eq; properness => //. apply rlift_dm_c_singleton. Qed.

  Lemma rD_TypK_Abs_0 {Γ} T SK s σ l :
    s ↝[ σ ] T -∗
    Γ rs⊨ oLater T ∷[ 0 ] SK -∗
    Γ rs⊨ { l := dtysem σ s = dtysem σ s } : rCTMemK l SK.
  Proof.
    rewrite rsdtp_eq'. iDestruct 1 as (φ Hγφ) "#Hγ".
    iIntros ">#HT !>" (?? Hpid1 Hpid2) "#Hg".
    iExists (hoEnvD_inst σ.|[ρ1] φ), (hoEnvD_inst σ.|[ρ2] φ).
    do 2 (iDestruct (dm_to_type_intro with "Hγ") as "-#$"; first done).
    iApply (sf_kind_proper with "(HT Hg)") => args v /=;
      f_equiv; symmetry; exact: Hγφ.
  Qed.

  Lemma rD_TypK_Abs {Γ} T1 T2 SK s1 s2 σ1 σ2 l :
    s1 ↝[ σ1 ] T1 -∗
    s2 ↝[ σ2 ] T2 -∗
    Γ rs⊨ oLater T1 <::[ 0 ] oLater T2 ∷ SK -∗
    (* WEIRD, the [=] symbol should be for the symmetric closure! *)
    Γ rs⊨ { l := dtysem σ1 s1 = dtysem σ2 s2 } : rCTMemK l SK.
  Proof.
    rewrite rsdtp_eq'.
    iDestruct 1 as (φ1 Hγφ1) "#Hγ1".
    iDestruct 1 as (φ2 Hγφ2) "#Hγ2".
    iIntros ">#HT !>" (?? Hpid1 Hpid2) "#Hg".
    iExists (hoEnvD_inst σ1.|[ρ1] φ1), (hoEnvD_inst σ2.|[ρ2] φ2).
    do 2 (iSplit; [by iApply dm_to_type_intro|]).
    iApply (sf_kind_proper with "(HT Hg)") => args v /=; f_equiv; symmetry.
    exact: Hγφ1.
    exact: Hγφ2.
  Qed.

  Lemma rK_Sel {Γ} l (SK : sf_kind Σ) p1 p2 i :
    Γ rs⊨p p1 = p2 : rVTMemK l SK, i -∗
    (* Γ rs⊨ oSel p1 l =[ i ] oSel p2 l ∷ SK. *)
    Γ rs⊨ oSel p1 l <::[ i ] oSel p2 l ∷ SK.
  Proof.
    iIntros ">#Hp !> %ρ1 %ρ2 Hg". iSpecialize ("Hp" with "Hg"); iNext i.
    rewrite path_wp_eq; iDestruct "Hp" as (v1 Hal1%alias_paths_pv_eq_1) "Hp".
    rewrite path_wp_eq; iDestruct "Hp" as (v2 Hal2%alias_paths_pv_eq_1) "Hp".
    iDestruct "Hp" as (d1 d2 [Hl1 Hl2] ψ1 ψ2) "(#Hl1 & #Hl2 & HK)".
    iApply (sf_kind_sub_internal_proper with "[] [] HK").
    all: by iApply oSel_equiv_intro.
  Qed.

  Lemma rK_Sel' {Γ} l (SK : sf_kind Σ) p1 p2 i :
    Γ rs⊨p p1 = p2 : rVTMemK l SK, i -∗
    (* Γ rs⊨ oSel p1 l =[ i ] oSel p2 l ∷ SK. *)
    Γ rs⊨ oSel p1 l =[ i ] oSel p2 l ∷ SK.
  Proof.
    iIntros "#HK"; iSplit; iApply rK_Sel; [done|].
    (* TODO: symmetry (unprovable yet) *)
  Abort.

(*
     -∗
    Γ rs⊨p T = T p2 : rVTMemK l SK, i -∗
    Γ rs⊨p oApp T p1 = oApp T p2 : rVTMemK l SK, i -∗
    Γ rs⊨ oSel p1 l <::[ i ] oSel p2 l ∷ SK -∗ *)

  Lemma oTApp_respects_eq {Γ} l (SK : sf_kind Σ) p1 p2 i RC T :
    Γ rs⊨p p1 = p2 : c2v RC, i -∗
    Γ rs⊨ T ∷[ i ] sf_kpi (close $ c2v RC) SK -∗
    Γ rs⊨ oTApp T p1 <::[ i ] oTApp T p2 ∷
      (* [SK] must respect [p1 = p2]? *)
      SK .sKp[ p1 /].
  Proof.
    iIntros ">#Hp >#HT !> %ρ1 %ρ2 #Hg".
    iSpecialize ("Hp" with "Hg"); iSpecialize ("HT" with "Hg"); iNext i;
    iClear "Hg".
    rewrite path_wp_eq; iDestruct "Hp" as (v1 Hal1%alias_paths_pv_eq_1) "Hp".
    rewrite path_wp_eq; iDestruct "Hp" as (v2 Hal2%alias_paths_pv_eq_1) "Hp".
    (* XXX This takes the goal to [SK (v1 .: ρ1) ...], and even with 2 envs we'd use [v1]. *)
    iEval (rewrite /kpSubstOne /= (alias_paths_elim_eq _ Hal1) path_wp_pv_eq).
    (* XXX we need _two_ arguments here? But [SK] must use [v1] for both. *)
    iSimpl in "HT".
    iSpecialize ("HT" $! v1).
    Fail iSpecialize ("HT" with "Hp").
    iApply (sf_kind_sub_internal_proper with "[] [] (HT [])").
    3: {
      iClear "HT".
      (* Unprovable: does not match ["Hp"].
        Provable if [c2v RC] is contravariant in last argument (so, if v2 = v1
        symmetrically), but rather change ["HT"]? sf_kpi should take [RC] not
        [close $ c2v RC]. *)
      admit.
    }
    (* XXX bump Iris *)
    Bind Scope bi_scope with bi_car.
    all: iIntros (args w).
    all: rewrite /_oTApp/= alias_paths_elim_eq // path_wp_pv_eq //.
    by iApply (iff_refl emp).
    rewrite /envApply /acurry /=.
    (* Argument mismatch, because "HT" takes only [v1] *)
    (* Maybe provable if [v1] and [v2] were "equivalent" and [T] respected that. *)
    admit.
    all: fail.
  Abort.

  #[global, program] Instance rCTop : Top (crel.t Σ) :=
    CRel ⊤ ⊤.
  Solve All Obligations with eauto.

  Lemma rD_Nil Γ :
    ⊢ Γ rs⊨ds [] = [] : ⊤.
  Proof. by iModIntro; repeat iSplit; last iIntros "**". Qed.

  Lemma rD_Cons Γ d1 d2 ds1 ds2 l RC1 RC2 :
    dms_hasnt ds1 l →
    dms_hasnt ds2 l →
    Γ rs⊨ { l := d1 = d2 } : RC1 -∗
    Γ rs⊨ds ds1 = ds2 : RC2 -∗
    Γ rs⊨ds (l, d1) :: ds1 = (l, d2) :: ds2 : rCAnd RC1 RC2.
  Proof.
    rewrite rsdtp_eq; iIntros (Hlds1 Hlds2) ">#HT1 >(% & % & #HT2) !>"; repeat iSplit.
    1-2: by iIntros "!%"; cbn; constructor => //; by rewrite -dms_hasnt_notin_eq.
    iIntros (ρ1 ρ2 [Hpid1 Hpids1]%path_includes_split [Hpid2 Hpids2]%path_includes_split) "#Hg".
    iSpecialize ("HT1" $! _ _ Hpid1 Hpid2 with "Hg").
    iSpecialize ("HT2" $! _ _ Hpids1 Hpids2 with "Hg").
    iSplit; first by iApply crel_def2defs_head.
    iApply (crel_mono with "HT2"). all: exact: dms_hasnt_subst.
  Qed.

  (* Useful derived rules. *)
  Lemma rD_Sing Γ d1 d2 l RC :
    Γ rs⊨ { l := d1 = d2 } : RC -∗ Γ rs⊨ds [(l, d1)] = [(l, d2)] : rCAnd RC ⊤.
  Proof. by iIntros "#H"; iApply (rD_Cons with "H"); last iApply rD_Nil. Qed.

  Lemma rCAnd_rCTop RC : rCAnd RC ⊤ ≡ RC.
  Proof. split => /=; repeat intro; apply: (right_id _ bi_and). Qed.

  (** Not part of the official type system, but very convenient for examples. *)
  Lemma rD_Sing' Γ d1 d2 l RC :
    Γ rs⊨ { l := d1 = d2 } : RC -∗ Γ rs⊨ds [(l, d1)] = [(l, d2)] : RC.
  Proof. by rewrite rD_Sing rCAnd_rCTop. Qed.

  Lemma rP_Obj_I Γ RC ds1 ds2 :
    rVLater (c2v RC) :: Γ rs⊨ds ds1 = ds2 : RC -∗
    Γ rs⊨p pv (vobj ds1) = pv (vobj ds2) : rVMu (c2v RC), 0.
  Proof.
    iIntros ">(%Hwf1 & %Hwf2 & #Hds) !> %ρ1 %ρ2 #Hg /=".
    rewrite !path_wp_pv_eq /=. iLöb as "IH".
    iApply crel_commute. rewrite !norm_selfSubst.
    iApply ("Hds" $! (vobj _ .: ρ1) (vobj _ .: ρ2) with "[%] [%] [$IH $Hg]").
    exact: path_includes_self.
    exact: path_includes_self.
  Qed.

  (* Lemma rVTy_intro l Γ i SK s σ T :
    let v := vobj [(l, dtysem σ s)] in
    s ↝[ σ ] T -∗
    Γ rs⊨p pv v = pv v : rVTMemK l SK, i. *)
  Lemma rVTy_intro' l Γ SK s σ T :
    let v := vobj [(l, dtysem σ s)] in
    s ↝[ σ ] T -∗
    rVLater (rVTMemK l (sf_sngl (oLater T))) :: Γ rs⊨ oLater T ∷[ 0 ] sf_sngl (oLater T) -∗
    Γ rs⊨p pv v = pv v : rVMu (rVTMemK l (sf_sngl (oLater T))), 0.
  Proof.
    iIntros (v) "#Hs #HK".
    iApply rP_Obj_I.
    iApply rD_Sing'.
    iApply (rD_TypK_Abs_0 with "Hs HK").
  Qed.

    (* intros v.
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
  Admitted. *)

  (* Lemma rVTy_intro l Γ i SK (T : ty) :
    let p := pv (vobj [(l, dtysyn T)]) in
    ⊢ Γ rs⊨p p = p : rVTMemK l SK, i.
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
  XXX2 : luckily, we don't really need this for path equivalence. Just equivalence!
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
