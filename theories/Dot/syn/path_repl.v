(** * Path substitution and replacement.

Path replacement replaces one occurrence of a path [p] by another path [q],
without affecting other occurrences of [p].

Path substitution replaces all occurrences of path [pv (ids 0)] by another
path [p], and shifts

We define these operations as relations (whose definition is comparatively
clear), and then we define functions and prove them correct (here and in
[path_repl_lemmas.v]).
*)
From stdpp Require Import relations.
From D.Dot.syn Require Import syn.

Implicit Types
         (T : ty) (v w : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (l : label).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Notation unshift T := T.|[ren pred].
Notation unshiftV v := v.[ren pred].

Reserved Notation   "v1 ~vp[ p := q  ] v2"  (at level 70).
Reserved Notation   "d1 ~dp[ p := q  ] d2"  (at level 70).
Reserved Notation "ds1 ~dsp[ p := q  ] ds2" (at level 70).
Reserved Notation   "p1 ~pp[ p := q  ] p2"  (at level 70).
Reserved Notation   "T1 ~Tp[ p := q  ] T2"  (at level 70).

(** ** The path replacement judgment, as defined in the pDOT paper.
[T1 ~Tp[ p := q ] T2] means that [T2] is obtained from [T1] by replacing
_one_ occurrence of [p] by [q]. We also use the reflexive-transitive closure
of this judgemnt.
*)
Inductive vl_path_repl (p q : path) : vl → vl → Prop :=
| vl_path_repl_vobj ds1 ds2 :
  ds1 ~dsp[ p := q ] ds2 →
  vobj ds1 ~vp[ p := q ] vobj ds2
where "v1 ~vp[ p := q  ] v2" := (vl_path_repl p q v1 v2)
with dm_path_repl (p q : path) : dm → dm → Prop :=
| dm_path_repl_dtysyn T1 T2 :
  T1 ~Tp[ p := q ] T2 →
  dtysyn T1 ~dp[ p := q ] dtysyn T2
(* | dm_path_repl_dpt p1 p2 :
  p1 ~pp[ p := q ] p2 →
  dpt p1 ~dp[ p := q ] dpt p2 *)
where "d1 ~dp[ p := q  ] d2" := (dm_path_repl p q d1 d2)
with dms_path_repl (p q : path) : dms → dms → Prop :=
| dms_path_repl_cons1 l d1 d2 ds :
  d1 ~dp[ p := q ] d2 →
  (l, d1) :: ds ~dsp[ p := q ] (l, d2) :: ds
| dms_path_repl_cons2 l d ds1 ds2 :
  ds1 ~dsp[ p := q ] ds2 →
  (l, d) :: ds1 ~dsp[ p := q ] (l, d) :: ds2
where "ds1 ~dsp[ p := q  ] ds2" := (dms_path_repl p q ds1 ds2)
with path_path_repl (p q : path) : path → path → Prop :=
| path_path_repl_base : p ~pp[ p := q ] q
| path_path_repl_pv v1 v2 :
  v1 ~vp[ p := q ] v2 →
  pv v1 ~pp[ p := q ] pv v2
| path_path_repl_self p1 p2 l :
  p1 ~pp[ p := q ] p2 →
  pself p1 l ~pp[ p := q ] pself p2 l
where "p1 ~pp[ p := q  ] p2" := (path_path_repl p q p1 p2)
with ty_path_repl (p q : path) : ty → ty → Prop :=
| ty_path_repl_TAnd1 T1 T2 U :
  T1 ~Tp[ p := q ] T2 →
  TAnd T1 U ~Tp[ p := q ] TAnd T2 U
| ty_path_repl_TAnd2 T1 T2 U :
  T1 ~Tp[ p := q ] T2 →
  TAnd U T1 ~Tp[ p := q ] TAnd U T2
| ty_path_repl_TOr1 T1 T2 U :
  T1 ~Tp[ p := q ] T2 →
  TOr T1 U ~Tp[ p := q ] TOr T2 U
| ty_path_repl_TOr2 T1 T2 U :
  T1 ~Tp[ p := q ] T2 →
  TOr U T1 ~Tp[ p := q ] TOr U T2
| ty_path_repl_TLater T1 T2 :
  T1 ~Tp[ p := q ] T2 →
  TLater T1 ~Tp[ p := q ] TLater T2
| ty_path_repl_TAll1 S1 S2 T :
  S1 ~Tp[ p := q ] S2 →
  TAll S1 T ~Tp[ p := q ] TAll S2 T
| ty_path_repl_TAll2 S T1 T2 :
  T1 ~Tp[ shift p := shift q ] T2 →
  TAll S T1 ~Tp[ p := q ] TAll S T2
| ty_path_repl_TMu T1 T2 :
  T1 ~Tp[ shift p := shift q ] T2 →
  TMu T1 ~Tp[ p := q ] TMu T2
| ty_path_repl_TVMem T1 T2 l :
  T1 ~Tp[ p := q ] T2 →
  TVMem l T1 ~Tp[ p := q ] TVMem l T2
| ty_path_repl_TTMem1 T1 T2 U l :
  T1 ~Tp[ p := q ] T2 →
  TTMem l T1 U ~Tp[ p := q ] TTMem l T2 U
| ty_path_repl_TTMem2 T1 T2 U l :
  T1 ~Tp[ p := q ] T2 →
  TTMem l U T1 ~Tp[ p := q ] TTMem l U T2
| ty_path_repl_TSel p1 p2 l :
  p1 ~pp[ p := q ] p2 →
  TSel p1 l ~Tp[ p := q ] TSel p2 l
(* | ty_path_repl_TSing p1 p2 :
  p1 ~pp[ p := q ] p2 →
  TSing p1 ~Tp[ p := q ] TSing p2 *)
where "T1 ~Tp[ p := q  ] T2" := (ty_path_repl p q T1 T2).

(* Lemma path_path_repl_id p1 p2 p : p1 ~pp[ p := p ] p2 → p1 = p2.
Proof. by elim; intros; simplify_eq/=. Qed. *)

Notation   "v1 ~vp[ p := q  ]* v2"  := (rtc (vl_path_repl   p q) v1 v2)   (at level 70).
Notation   "d1 ~dp[ p := q  ]* d2"  := (rtc (dm_path_repl   p q) d1  d2)  (at level 70).
Notation "ds1 ~dsp[ p := q  ]* ds2" := (rtc (dms_path_repl  p q) ds1 ds2) (at level 70).
Notation   "p1 ~pp[ p := q  ]* p2"  := (rtc (path_path_repl p q) p1 p2)   (at level 70).
Notation   "T1 ~Tp[ p := q  ]* T2"  := (rtc (ty_path_repl   p q) T1 T2)   (at level 70).

(* Lemma ty_path_repl_id p T1 T2 : T1 ~Tp[ p := p ] T2 → T1 = T2.
Proof.
  intros Hr; dependent induction Hr; rewrite ?IHHr //;
    f_equiv; exact: path_path_repl_id.
Qed. *)

(**
Define substitution of [pv (ids 0)] by [p] as a relation, in terms of the
transitive closure of path replacement.
Since the result of path substitution is [shift T'], it's clear that all
occurrences of [pv (ids 0)] have been replaced. *)
Definition path_repl_one T p T' :=
  T ~Tp[ pv (ids 0) := shift p ]* shift T'.
Notation "T .Tp[ p /]~ T'" := (path_repl_one T p T') (at level 65).

(**
We also define path replacement as a function, and prove it correct in
[psubst_ty_rtc_sufficient].
*)
Reserved Notation "v .v[ p := q  ]" (at level 65).
Reserved Notation "d .d[ p := q  ]" (at level 65).
Reserved Notation "r .p[ p := q  ]" (at level 65).
Reserved Notation "T .T[ p := q  ]" (at level 65).

(* This still cannot substitute in dtysem, so we still need some
unstampedness check, or just to forbid dtysem. *)
Fixpoint psubst_vl p q v : vl :=
  match v with
  | vobj d => vobj (map (mapsnd (psubst_dm p q)) d)
  | _ => v
  end
where "v .v[ p := q  ]" := (psubst_vl p q v)
with psubst_dm p q d : dm :=
  match d with
  (* | dpt r => dpt (psubst_path p q r) *)
  | dtysyn T => dtysyn (psubst_ty p q T)
  | _ => d
  end
where "d .d[ p := q  ]" := (psubst_dm p q d)
with psubst_ty p q T : ty := match T with
| TTop => TTop
| TBot => TBot
| TAnd T1 T2 => TAnd (T1 .T[ p := q ]) (T2 .T[ p := q ])
| TOr T1 T2 => TOr (T1 .T[ p := q ]) (T2 .T[ p := q ])
| TLater T => TLater (T .T[ p := q ])
| TAll S T => TAll (S .T[ p := q ]) (T .T[ shift p := shift q ])
| TMu T => TMu (T .T[ shift p := shift q ])
| TVMem l T => TVMem l (T .T[ p := q ])
| TTMem l L U => TTMem l (L .T[ p := q ]) (U .T[ p := q ])
| TSel r l => TSel (r .p[ p := q ]) l
| TPrim _ => T
| TSing _ => T
(* | TSing r => TSing (r .p[ p := q ]) *)
end
where "T .T[ p := q  ]" := (psubst_ty p q T)
with psubst_path p q r : path :=
  match (decide (r = p)) with
  | left _ => q
  | _ =>
    match r with
    | pv v => pv (psubst_vl p q v)
    | pself r' l => pself (r' .p[ p := q ]) l
    end
end
where "r .p[ p := q  ]" := (psubst_path p q r).
    (* XXX Update comment.
    While these values can in turn contain paths, pDOT path replacement
    doesn't substitute inside such values (because in pDOT such values cannot
    appear in paths); lemma [psubst_path_rtc_sufficient] shows this
    functional path replacement agrees with relational path replacement.

    This operation is also used to build functional path substitution, for use
    on unstamped types. And for unstamped types, lemma [psubst_one_implies]
    shows this function is correct, relative to relational path substitution.

    This design was chosen when values could not contain paths; now that values
    _can_ contain paths, we could probably modify substitution to traverse
    paths inside values.
    *)

(* Lemma psubst_path_self p q: p .p[ p := q ] = q.
Proof. case: p => /= *; by rewrite decide_True. Qed. *)

Section closure.
  Context `{RA : relation A} `{RB : relation B} `{RC : relation C}.

  Local Hint Constructors rtc : core.

  (** Congruence lemma for transitive closure. Binary variant of [rtc_congruence]. *)

  Lemma rtc_congruence2 (f : A → B → C) a1 a2 b1 b2 :
    (∀ a1 a2 b, RA a1 a2 → RC (f a1 b) (f a2 b)) →
    (∀ a b1 b2, RB b1 b2 → RC (f a b1) (f a b2)) →
    rtc RA a1 a2 → rtc RB b1 b2 →
    rtc RC (f a1 b1) (f a2 b2).
  Proof. induction 3; induction 1; eauto. Qed.
End closure.

Section decide_psubst.
(** Instances of [rtc_congruence] where inference needs help. *)
  Local Hint Constructors vl_path_repl dm_path_repl dms_path_repl
    path_path_repl ty_path_repl : core.

  Lemma path_path_repl_self_rtc p q p1 p2 l :
    p1 ~pp[ p := q ]* p2 →
    pself p1 l ~pp[ p := q ]* pself p2 l.
  Proof. apply rtc_congruence with (f := (λ p, pself p l)); auto. Qed.

  Lemma ty_path_repl_TSel_rtc p q p1 p2 l :
    p1 ~pp[ p := q ]* p2 →
    TSel p1 l ~Tp[ p := q ]* TSel p2 l.
  Proof. apply rtc_congruence with (f := (λ p, TSel p l)); auto. Qed.

  Lemma dms_path_repl_cons_rtc p q l d1 d2 ds1 ds2 :
    d1 ~dp[ p := q ]* d2 →
    ds1 ~dsp[ p := q ]* ds2 →
    (l, d1) :: ds1 ~dsp[ p := q ]* (l, d2) :: ds2.
  Proof. eapply rtc_congruence2 with (f := λ d ds, (l, d) :: ds); auto. Qed.

  (** The reflexive, transitive closure of path replacement agrees with path
  substitution. *)

  Notation psubst_rtc_sufficient_vl_def v1 := (∀ v2 p q,
    v1 .v[ p := q ] = v2 → v1 ~vp[ p := q ]* v2).
  Notation psubst_rtc_sufficient_dm_def d1 := (∀ d2 p q,
    d1 .d[ p := q ] = d2 → d1 ~dp[ p := q ]* d2).
  Notation psubst_rtc_sufficient_path_def p1 := (∀ p2 p q,
    p1 .p[ p := q ] = p2 → p1 ~pp[ p := q ]* p2).
  Notation psubst_rtc_sufficient_ty_def T1 := (∀ T2 p q,
    T1 .T[ p := q ] = T2 → T1%ty ~Tp[ p := q ]* T2).

  Lemma psubst_rtc_sufficient_mut :
    (∀ t, True) ∧ (∀ v, psubst_rtc_sufficient_vl_def v) ∧
    (∀ d, psubst_rtc_sufficient_dm_def d) ∧ (∀ p, psubst_rtc_sufficient_path_def p) ∧
    (∀ T, psubst_rtc_sufficient_ty_def T).
  Proof.
    apply syntax_mut_ind; intros; subst => //=;
      try (case_decide as Hdec; first (rewrite Hdec; apply rtc_once; constructor));
      eauto using rtc_refl, path_path_repl_self_rtc, ty_path_repl_TSel_rtc, rtc_congruence;
      try by [eapply rtc_congruence2; eauto 2].

    eapply rtc_congruence; first by eauto.
    generalize dependent ds; elim => [//|[l d] ds IHds] /= /Forall_cons [Hd Hds].
    by apply /dms_path_repl_cons_rtc /IHds /Hds /Hd.
  Qed.

  Lemma psubst_vl_rtc_sufficient v1 v2 p q :
    v1 .v[ p := q ] = v2 →
    v1 ~vp[ p := q ]* v2.
  Proof. apply psubst_rtc_sufficient_mut. Qed.
  Lemma psubst_dm_rtc_sufficient d1 d2 p q :
    d1 .d[ p := q ] = d2 →
    d1 ~dp[ p := q ]* d2.
  Proof. apply psubst_rtc_sufficient_mut. Qed.
  Lemma psubst_path_rtc_sufficient p1 p2 p q :
    p1 .p[ p := q ] = p2 →
    p1 ~pp[ p := q ]* p2.
  Proof. apply psubst_rtc_sufficient_mut. Qed.
  Lemma psubst_ty_rtc_sufficient T1 T2 p q :
    T1 .T[ p := q ] = T2 →
    T1 ~Tp[ p := q ]* T2.
  Proof. apply psubst_rtc_sufficient_mut. Qed.
End decide_psubst.

(**
Finally, we can also define path substitution as a function.
Its proofs of correctness is in [path_repl_lemmas.v], in lemmas
[psubst_one_implies] and [psubst_subst_agree_ty].
*)
Definition psubst_one_base_vl v p := v .v[ pv (ids 0) := shift p ].
Definition psubst_one_vl v p := unshiftV (psubst_one_base_vl v p).
Notation "v .vp[ p /]" := (psubst_one_vl v p) (at level 65).

Definition psubst_one_base_path q p := q .p[ pv (ids 0) := shift p ].
Definition psubst_one_path q p := unshift (psubst_one_base_path q p).
Notation "q .pp[ p /]" := (psubst_one_path q p) (at level 65).

Definition psubst_one_base_ty T p := T .T[ pv (ids 0) := shift p ].
Definition psubst_one_ty T p := unshift (psubst_one_base_ty T p).
Notation "T .Tp[ p /]" := (psubst_one_ty T p) (at level 65).

Definition psubst_one_base_dm d p := d .d[ pv (ids 0) := shift p ].
Definition psubst_one_dm d p := unshift (psubst_one_base_dm d p).
Notation "d .dp[ p /]" := (psubst_one_dm d p) (at level 65).
