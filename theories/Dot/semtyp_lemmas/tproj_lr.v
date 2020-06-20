(** * Semantic lemmas for Scala 2 type projections [T#A].

This shows how to restrict type projections to be sound and usable in Dotty.

This is developed as an extension of guarded DOT (gDOT), described in
https://iris-project.org/pdfs/2020-dot-submission.pdf
(some details are being changed).

Because of the interest to the wider Scala community,
this file has extensive informal comments.

The comments use a "naive" understanding of types as sets; this Coq
development is based on this understanding, but with some restrictions
discussed in the paper.
*)
From iris.proofmode Require Import tactics.
From D Require Import swap_later_impl.
From D.Dot Require Import unary_lr dsub_lr sub_lr path_repl_lr.

Implicit Types (Σ : gFunctors).
Implicit Types (v: vl) (e: tm) (d: dm) (ds: dms) (ρ : env) (l : label).

Set Suggest Proof Using.
Set Default Proof Using "Type*".

Definition oExists `{!dlangG Σ} {n} (T : oltyO Σ 0) (U : oltyO Σ n) : oltyO Σ n :=
  Olty (λI args ρ v,
  ∃ w,
  (* w ∈ T *)
  oClose T ρ w ∧
  (* v ∈ w.A *)
  U args (w .: ρ) v).

(**
Semantic proofs of typing lemmas for existentials.

I adapted the rules from https://dl.acm.org/doi/pdf/10.1145/3290322 (see
[≤∃L] and [≤∃R] in Fig. 4).

Lionel Parreaux pointed me to that paper and suggested they are the
"standard" rules for "implicit" existentials.
*)
Section existentials.
  Context `{!dlangG Σ}.

  (** Rule [∃-<:] (called [≤∃L] in the link). *)
  Lemma sEx_Stp `{!SwapPropI Σ} Γ S T (U : oltyO Σ 0) i :
    oLaterN i (oShift S) :: Γ s⊨ T <:[i] oShift U -∗
    Γ s⊨ oExists S T <:[i] U.
  Proof.
    rewrite !sstpd_to_sstpi; iIntros "/= #Hstp %ρ %v Hg".
    iDestruct 1 as (w) "[HS HT]".
    iApply ("Hstp" $! (w .: ρ) v with "[$Hg $HS] HT").
  Qed.

  (** Rule [<:-∃] (called [≤∃L] in the link). *)
  Lemma sStp_Ex `{!SwapPropI Σ} Γ S T (U : oltyO Σ 0) i p :
    Γ s⊨p p : S, i -∗
    Γ s⊨ T <:[i] opSubst p U -∗
    Γ s⊨ T <:[i] oExists S U.
  Proof.
    iIntros "/= #HpS #Hstp %ρ #Hg".
    iSpecialize ("HpS" with "Hg"); iSpecialize ("Hstp" with "Hg"); iNext i.
    iApply (subtype_trans with "Hstp"); iIntros "%v HvUp".
    iDestruct (path_wp_agree with "HpS HvUp") as (w _) "?".
    by iExists w.
  Qed.

End existentials.

(**
  This semantic type models upper-bound-only type projections using
  (model-level) existentials and normal DOT type members:
    [V[[T#A]](ρ) = { v | ∃ w ∈ V[[T]](ρ). v ∈ V[[w.A]](ρ) }].
*)
Definition oProjN `{!dlangG Σ} n A (T : oltyO Σ 0) : oltyO Σ n :=
  Olty (λI args ρ v,
  ∃ w,
  (* w ∈ T *)
  oClose T ρ w ∧
  (* v ∈ w.A *)
  oSelN n (pv (ids 0)) A args (w .: ρ) v).
Notation oProj A T := (oProjN 0 A T).

(** Technical infrastructure for setoid rewriting. *)
Instance: Params (@oProjN) 4 := {}.

Section type_proj_setoid_equality.
  Context `{!dlangG Σ}.

  Definition oProjN_oExists `{!dlangG Σ} n A T:
    oProjN n A T ≡ oExists T (oSelN n (pv (ids 0)) A) := reflexivity _.

  Global Instance oProjN_ne n A : NonExpansive (oProjN n A).
  Proof. solve_proper_ho. Qed.
  Global Instance oProjN_proper n A : Proper ((≡) ==> (≡)) (oProjN n A) := ne_proper _.

  Lemma oProjN_eq n A T args ρ v :
    oProjN n A T args ρ v ⊣⊢ ∃ w, oClose T ρ w ∧ vl_sel w A args v.
  Proof. by simpl; f_equiv => w; rewrite path_wp_pv_eq. Qed.

  Lemma oProjN_eq_2 n A T args ρ v :
    oProjN n A T args ρ v ⊣⊢
    ∃ w d ψ, ⌜w @ A ↘ d⌝ ∧ oClose T ρ w ∧ d ↗n[ n ] ψ ∧ ▷ ψ args v.
  Proof.
    rewrite oProjN_eq; f_equiv => w.
    rewrite and_exist_l; f_equiv => ψ; rewrite and_exist_l; f_equiv => d.
    by rewrite (assoc bi_and) [(_ ∧ (⌜_⌝))%I](comm bi_and) -(assoc bi_and).
  Qed.
End type_proj_setoid_equality.

(** Semantic proofs of typing lemmas for projections. *)
Section type_proj.
  Context `{!dlangG Σ}.

  (**
    Existentials on a singleton coincide with path substitution:
    [∃ x: p.type. T = T[x:=p]].
   *)
  Lemma oExists_oSing p (T : oltyO Σ 0) :
    oExists (oSing p) T ≡ opSubst p T.
  Proof.
    move=> args ρ v. rewrite /= path_wp_eq.
    by properness; rewrite ?alias_paths_pv_eq_1.
  Qed.

  (**
    Projections from a singleton coincide with selections:
    [p.type#A = p.A].
   *)
  Lemma oProj_oSing A p :
    oProj A (oSing p) ≡ oSel p A.
  Proof.
    rewrite oProjN_oExists oExists_oSing.
    (* Reduce path substitution. *)
    by move=> args ρ v /=; f_equiv=>w; rewrite path_wp_pv_eq.
  Qed.

  (** TODO: other rules should be derivable from the rules for existentials. *)
  (**
    Here and below, we use indexed subtyping [Γ ⊨ T <:^i U] to satisfy the
    restrictions discussed above. These restrictions are not specific to type
    projections but are also needed for type selections [p.A].

    On a first read, you should read [Γ ⊨ T <:^i U] as [Γ ⊢ T <: U]; see the
    paper for more discussion.

    In short, to show a subtyping relation [T1 <: T2], we must show that
    any value [v] in [T1] is also in [T2].

    Because types can contain free variables, we have environments [ρ],
    typed by typing contexts [Γ], but you can ignore them at first.
  *)

  (**
    Type projections are covariant: if T <: U then T#A <: U#A, or formally:

    Γ ⊨ T <:^i U
    ------------------------
    Γ ⊨ T#A <:^i U#A
  *)
  Lemma sProj_Stp_Proj A Γ T U i :
    Γ s⊨ T <:[i] U -∗
    Γ s⊨ oProj A T <:[i] oProj A U.
  Proof.
    iIntros "#Hsub %ρ Hg %v"; iSpecialize ("Hsub" with "Hg"); iNext i.
    (**
      From [T <: U] we must show [T#A <: U#A], that is, that any [v] in [T#A]
      is in [U#A]. Recall the definition of [T#A]:

        [V[[T#A]](ρ) = { v | ∃ w ∈ V[[T]](ρ). v ∈ V[[w.A]](ρ) }].

      So assume [v] is in [T#A]; then there exists a [w] in [T] such that [v]
      is in [w.A]. But then [w] is in [U], because [T <: U].
      So we have [w ∈ U] and [v ∈ w.A], that is, [v ∈ U#A].
    *)

    rewrite !oProjN_eq. iDestruct 1 as (w) "(HTw & Hφ)"; iExists w; iFrame "Hφ".
    iApply ("Hsub" with "HTw").
  Qed.

  (**
    Type projections are subtypes of their upper bound.

    ------------------------
    Γ ⊨ { A :: L .. U }T#A <:^i U
  *)
  Lemma sProj_Stp_U A Γ L U i :
    ⊢ Γ s⊨ oProj A (oTMem A L U) <:[i] U.
  Proof.
    iIntros "%ρ Hg %v"; iNext i.
    rewrite oProjN_eq; iDestruct 1 as (w) "(HTw & HselV)".
    (*
      After unfolding definitions, we must show that [v] is in [U],
      assuming that [v] is in [w.A] where [w] is in [{ A :: L .. U }].
      From existing results for type selections, it follows that
      [v] is in [U].
    *)
    iApply (vl_sel_ub with "HselV HTw").
  Qed.

  (**
    Type projections are subtypes of their upper bound: a more general statement.

    Γ ⊨ T <:^i { A :: L .. U }
    ------------------------
    Γ ⊨ T#A <:^i U
  *)
  Lemma sProj_Stp_U' A Γ T L U i :
    Γ s⊨ T <:[i] oTMem A L U -∗
    Γ s⊨ oProj A T <:[i] U.
  Proof.
    iIntros "#Hp".
    iApply sStp_Trans; first iApply (sProj_Stp_Proj with "Hp").
    iApply sProj_Stp_U.
  Qed.

  (**
    Projections [T#A] are lower bounded by type selections [p.A]:

    Γ ⊨ p :^i T
    ------------------------
    Γ ⊨ p.A <:^i T#A
  *)
  (**
    Derive this rule from the above ones: rewrite the selection as a
    projection from a singleton type, then use covariance of projections, and
    finally use [sSngl_Stp_Self] to show that [p.type <: T].
  *)
  Lemma sSel_Stp_Proj A Γ T i p :
    Γ s⊨p p : T, i -∗
    Γ s⊨ oSel p A <:[i] oProj A T.
  Proof.
    iIntros "#Hp". rewrite -oProj_oSing.
    iApply sProj_Stp_Proj. iApply (sSngl_Stp_Self with "Hp").
  Qed.

  (**
    Combining the two above rules for projections with the existing system,
    we even get lower bounds for projections from inhabited types:

    Γ ⊨ T <:^i { A :: L .. U }
    Γ ⊨ p :^i T
    ------------------------
    Γ ⊨ L <:^i T#A

    But this is _not_ the Scala 2 lower-bound rule (which doesn't require [p]
    to exist), and it is not directly usable for a typechecker.
    The only typing rule we can use in Scala is
    [sSel_Stp_Proj], and to use that the user needs to get a value of type
    [p.A] in the usual, safe way:
    if [e] has type [L], then [e : p.A] has types [p.A] and [T#A].

    However, a typechecker might relax this restriction if it can prove [T]
    has an inhabiting path (that is, that it is realizable, in the sense
    used in Dotty), even if the value has not been constructed.

    Such reasoning is needed to enable compiling:
    [trait T { type A = Int }; def f(x: Int): T#A = x].

    The value can even use assumptions in the typing context (which might be
    more liberal than the Dotty rules); as usual, code in absurd typing
    contexts cannot run.
  *)
  Lemma sProj_Stp_L A Γ T L U i p :
    Γ s⊨ T <:[i] oTMem A L U -∗
    Γ s⊨p p : T, i -∗
    Γ s⊨ L <:[i] oProj A T.
  Proof.
    iIntros "#Hsub #Hp".
    iApply sStp_Trans; last iApply (sSel_Stp_Proj with "Hp").
    iApply sStp_Sel.
    iApply (sP_Sub with "Hp Hsub").
  Qed.

  (** In fact, if [p] has more specific bounds, we can use those too. *)
  Lemma sProj_Stp_L_Gen A Γ T1 T2 L U i p :
    Γ s⊨ T2 <:[i] oTMem A L U -∗
    Γ s⊨ T2 <:[i] T1 -∗
    Γ s⊨p p : T2, i -∗
    Γ s⊨ L <:[i] oProj A T1.
  Proof.
    iIntros "#HsubBounds #Hsub #HpT2".
    iDestruct (sP_Sub with "HpT2 Hsub") as "HpT1".
    iApply sStp_Trans; last iApply (sSel_Stp_Proj with "HpT1").
    iApply sStp_Sel.
    iApply (sP_Sub with "HpT2 HsubBounds").
  Qed.

  (** And [sProj_Stp_L] is indeed a special case of [sProj_Stp_L_Gen]. *)
  Lemma sProj_Stp_L' A Γ T L U i p :
    Γ s⊨ T <:[i] oTMem A L U -∗
    Γ s⊨p p : T, i -∗
    Γ s⊨ L <:[i] oProj A T.
  Proof.
    iIntros "#Hsub #Hp".
    iApply (sProj_Stp_L_Gen with "Hsub [] Hp").
    iApply sStp_Refl.
  Qed.

  (**
    TODO: Scala probably has more typing rules.
    Check them, or provide counterexamples.
  *)
End type_proj.
