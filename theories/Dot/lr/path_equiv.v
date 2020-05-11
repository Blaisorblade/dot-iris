From iris.proofmode Require Import tactics.
From iris.bi Require Import big_op.

From D Require Import iris_prelude succ_notation proper lr_syn_aux lty.
From D Require Import swap_later_impl.
From D.Dot Require Import syn dlang_inst dot_lty unary_lr.

Unset Program Cases.
Set Suggest Proof Using.
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (Σ : gFunctors)
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : var → vl) (l : label).

Class IApprox Σ `{!dlangG Σ} (A : Type) :=
  iapprox : A → A → iProp Σ.
Arguments IApprox _ {_} _.
Arguments iapprox _ _ _ _ !_ !_ /.
(* Level taken from ≡. *)
Notation "x ≈ y" := (iapprox x y) (at level 70, no associativity).
Notation "(≈)" := iapprox (only parsing).
Notation "x ≈@{ Σ } y" := (iapprox (Σ := Σ) x y) (at level 70, no associativity, only parsing).
Notation "(≈@{ Σ })" := (iapprox (Σ := Σ)) (only parsing).

Notation IApproxPersistent A := (∀ x y : A, Persistent (x ≈ y)).
Section iapprox_instances.
  Context `{!dlangG Σ}.

  Global Instance list_iapprox `{!IApprox Σ A} : IApprox Σ (list A) := fix big_sepL2 xs1 xs2 :=
    match xs1, xs2 with
    | [], [] => emp
    | x1 :: l1, x2 :: l2 => x1 ≈ x2 ∗ big_sepL2 l1 l2
    | _, _ => False
    end%I.
  Global Instance list_iapprox_persistent `{!IApprox Σ A} `{!IApproxPersistent A}:
    IApproxPersistent (list A).
  Proof. elim => [|???] [|??]; cbn; apply _. Defined.

  Global Instance label_pair_iapprox `{!IApprox Σ A}: IApprox Σ (label * A) :=
    λI '(l1, d1) '(l2, d2), ⌜l1 = l2⌝ ∧ d1 ≈ d2.
  Global Instance label_pair_iapprox_persistent `{!IApprox Σ A} `{!IApproxPersistent A} :
    IApproxPersistent (label * A).
  Proof. intros [] []; apply _. Defined.
End iapprox_instances.
(* The built-in hint doesn't work. *)

Global Hint Extern 1 (@Persistent (uPredI (iResUR ?Σ))
  (@iapprox ?Σ ?Hdlang (label * ?A)
    (@label_pair_iapprox ?Σ ?Hdlang ?A ?B) ?x ?y)) =>
      simple apply @label_pair_iapprox_persistent : typeclass_instances.

Section iapprox_instances.
  Context `{!dlangG Σ}.

  Global Instance iprop_iapprox : IApprox Σ (iProp Σ) :=
    λI P Q, □(P ↔ Q).
  Global Instance iprop_iapprox_persistent : IApproxPersistent (iProp Σ) := _.

  Global Instance fun_iapprox {A} `{!IApprox Σ B}: IApprox Σ (A → B) :=
    λI f1 f2, ∀ a, f1 a ≈ f2 a.
  Global Instance fun_iapprox_persistent {A} `{!IApprox Σ B}
    `{IApproxPersistent B} : IApproxPersistent (A → B) := _.
  Global Instance discrete_fun_iapprox {A} {B : ofeT} `{!IApprox Σ B} :
    IApprox Σ (A -d> B) := fun_iapprox.
  Global Instance discrete_fun_iapprox_persistent {A} {B : ofeT} `{!IApprox Σ B}
    `{IApproxPersistent B} : IApproxPersistent (A -d> B) := fun_iapprox_persistent.

  Fixpoint dm_approx d1 d2 {struct d1} : iProp Σ :=
    let _ : IApprox Σ path := path_approx in
    match d1, d2 with
    | dpt p1, dpt p2 => p1 ≈ p2
    | dtysem σ1 s1, dtysem σ2 s2 =>
      ∃ i (φ1 φ2 : hoEnvD Σ i), s1 ↝[ σ1 ] φ1 ∧ s2 ↝[ σ2 ] φ2 ∧
      (**
        This equivalence implicitly quantifies over arbitrary arguments.

        So, it does not constrain type members to respect themselves
        path-equality; that is checked by the kinding judgments when creating
        objects.

        Moreover, this does not imply that equivalence-respecting types
        respect kind-directed type equivalence. That is an additional condition.
        So this isn't enough to relate [F (lambda x. x.A)] to [F (lambda x. U)], even if
        [F :: ∀ x : {A :: L .. U}. K].
        *)
        φ1 ≈ φ2
      (* Beware we quantify over all arguments and environments; sometimes we
      should only quantify over arguments and environments satisfying
      constraints from kind/environment. *)
    | _, _ => False
    end
  with vl_approx v1 v2 {struct v1} : iProp Σ :=
    let _ : IApprox Σ dm := dm_approx in
    match v1, v2 with
    | vobj ds1, vobj ds2 => ds1 ≈ ds2
    (* Hm, what if the functions contain different values? *)
    | _, _ => ⌜v1 = v2⌝
    end
  with path_approx p1 p2 {struct p1} : iProp Σ :=
    let _ : IApprox Σ vl := vl_approx in
    let _ : IApprox Σ path := path_approx in
    match p1, p2 with
    | pv v1, pv v2 => v1 ≈ v2
    | pself p1 l1, pself p2 l2 => p1 ≈ p2 ∧ ⌜l1 = l2⌝
    | _, _ => False
    end%I.

  Global Instance iapprox_vl : IApprox Σ vl := vl_approx.
  Global Instance iapprox_dm : IApprox Σ dm := dm_approx.
  Global Instance iapprox_path : IApprox Σ path := path_approx.
  Global Arguments iapprox_vl /.
  Global Arguments iapprox_dm /.
  Global Arguments iapprox_path /.

  Fixpoint iapprox_dm_persistent d1 d2 {struct d1}: Persistent (d1 ≈ d2)
  with iapprox_vl_persistent v1 v2 {struct v1}: Persistent (v1 ≈ v2)
  with iapprox_path_persistent p1 p2 {struct p1}: Persistent (p1 ≈ p2).
  Proof.
    all: [> destruct d1, d2| destruct v1, v2| destruct p1, p2]; cbn; apply _.
  Qed.

  Global Existing Instance iapprox_dm_persistent.
  Global Existing Instance iapprox_vl_persistent.
  Global Existing Instance iapprox_path_persistent.

  Global Instance vec_iapprox `{!IApprox Σ A}: IApprox Σ (vec A i) :=
    fix rec i :=
      match i with
      | 0 => λI xs1 xs2, True
      | i.+1 => λI xs1 xs2,
        vhead xs1 ≈ vhead xs2 ∗ vtail xs1 ≈ vtail xs2
      end.
  Global Instance vec_iapprox_persistent `{!IApprox Σ A}
    `{IApproxPersistent A} i : IApproxPersistent (vec A i).
  Proof. elim: i; apply _. Qed.

  (* Split in half. *)
  Definition olty_le {i} (T1 T2 : olty Σ i) : iProp Σ :=
    □ (∀ args1 args2 ρ1 ρ2 v1 v2,
      args1 ≈ args2 -∗ ρ1 ≈ ρ2 -∗ v1 ≈ v2 -∗ T1 args1 ρ1 v1 -∗ T2 args2 ρ2 v2).

  Global Instance olty_iapprox {i} : IApprox Σ (olty Σ i) := λI T1 T2,
    olty_le T1 T2 ∗
    olty_le T2 T1.
  Global Instance olty_iapprox_persistent {i} : IApproxPersistent (olty Σ i) := _.

End iapprox_instances.

Class OProper `{!dlangG Σ} {i} (T : olty Σ i) :=
  iproper_olty : ⊢ olty_le T T.
  (* iproper_olty args1 args2 ρ1 ρ2 v1 v2 :
    ⊢@{iPropI Σ} args1 ≈ args2 -∗ ρ1 ≈ ρ2 -∗ v1 ≈ v2 -∗ T args1 ρ1 v1 ≡ T args2 ρ2 v2 *)

Section oproper_instances.
  Context `{Hdlang: !dlangG Σ}.

  Ltac oproper_prepare :=
    rewrite /OProper; iIntros "!>" (args1 args2 ρ1 ρ2 v1 v2) "#Ha #Hρ #Hv /=".

  Global Instance oproper_top i: OProper (i:=i) oTop.
  Proof. by oproper_prepare. Qed.
  Global Instance oproper_bot i: OProper (i:=i) oBot.
  Proof. by oproper_prepare. Qed.

  Lemma iproper_olty_rew {i} (T : olty Σ i) `{!OProper T}:
    ∀ args1 args2 ρ1 ρ2 v1 v2 ,
      args1 ≈ args2 -∗ ρ1 ≈ ρ2 -∗ v1 ≈ v2 -∗ T args1 ρ1 v1 -∗ T args2 ρ2 v2.
  Proof. iApply (iproper_olty (T := T)). Qed.

  Global Instance oproper_and {i} `{!OProper T, !OProper U}: OProper (i:=i) (oAnd T U).
  Proof.
    oproper_prepare; iDestruct 1 as "[HT HU]"; iSplit;
    by iApply (iproper_olty_rew with "Ha Hρ Hv").
  Qed.

  Global Instance oproper_or {i} `{!OProper T, !OProper U}: OProper (i:=i) (oOr T U).
  Proof.
    oproper_prepare; iDestruct 1 as "[H|H]"; [iLeft|iRight];
      by iApply (iproper_olty_rew with "Ha Hρ Hv H").
  Qed.
  Lemma approx_scons ρ1 ρ2 v1 v2 :
    ρ1 ≈ ρ2 -∗ v1 ≈ v2 -∗ v1 .: ρ1 ≈@{Σ} v2 .: ρ2.
  Proof using Hdlang. by iIntros "#Hρ #Hv" ([|x]) "/=". Qed.

  Global Instance oproper_mu {i} `{!OProper T}: OProper (i:=i) (oMu T).
  Proof.
    oproper_prepare; iIntros "H"; iApply (iproper_olty_rew with "Ha [] Hv H");
    by iApply approx_scons.
  Qed.
  Lemma oproper_osel_ext i p1 p2 l : p1 ≈ p2 -∗ olty_le (oSelN i p1 l) (oSelN i p2 l).
  Proof.
    iIntros "#Hp"; oproper_prepare; rewrite !path_wp_eq.
    iDestruct 1 as (w1 Heq1 d1 φ1 Hl1) "#[Hl1 Hv1]".
    have [w2 Heq2]: ∃ w2, path_wp_pure p2.|[ρ2] (eq w2) by admit.
    have [d2 Hl2]: ∃ d2, w2 @ l ↘ d2 by admit.
    iAssert (w1 ≈ w2) as "Hw". admit.
    iAssert (d1 ≈ d2) as "Hd". admit.
    (* XXX editor config *)
    iAssert (∃ φ2, d2 ↗n[ i ] φ2)%I as (φ2) "Hl2". admit.
    iAssert (▷ □ φ2 args2 v2)%I as "Hv2". admit.
    rewrite /vl_sel.
    by eauto 10 with iFrame.
    (* by iExists w2; iFrame (Heq2); iExists φ2, d2; iFrame (Hl2) "Hl2". *)
  Admitted.
  Global Instance oproper_osel i p l : OProper (oSelN i p l).
  Proof.
    rewrite /OProper; iApply oproper_osel_ext.
    (* Reflexivity. *)
  Admitted.

End oproper_instances.

  (* Context `{!dlangG Σ, !SwapPropI Σ}. *)
