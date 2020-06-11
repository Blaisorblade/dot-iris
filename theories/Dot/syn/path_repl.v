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

Reserved Notation "p1 ~pp[ p := q  ] p2" (at level 70).
Inductive path_path_repl (p q : path) : path → path → Prop :=
| path_path_repl_base : p ~pp[ p := q ] q
| path_path_repl_self p1 p2 l :
  p1 ~pp[ p := q ] p2 →
  pself p1 l ~pp[ p := q ] pself p2 l
where "p1 ~pp[ p := q  ] p2" := (path_path_repl p q p1 p2) .

Lemma path_path_repl_id p1 p2 p : p1 ~pp[ p := p ] p2 → p1 = p2.
Proof. by elim; intros; simplify_eq/=. Qed.

Notation path_path_repl_rtc p q := (rtc (path_path_repl p q)).
Notation "p1 ~pp[ p := q  ]* p2" := (path_path_repl_rtc p q p1 p2) (at level 70).

Reserved Notation "T1 ~Tp[ p := q  ] T2" (at level 70).

(** ** The path replacement judgment, as defined in the pDOT paper.
[T1 ~Tp[ p := q ] T2] means that [T2] is obtained from [T1] by replacing
_one_ occurrence of [p] by [q]. We also use the reflexive-transitive closure
of this judgemnt.
*)
Inductive ty_path_repl (p q : path) : ty → ty → Prop :=
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
| ty_path_repl_TAll1 T1 T2 U :
  T1 ~Tp[ p := q ] T2 →
  TAll T1 U ~Tp[ p := q ] TAll T2 U
| ty_path_repl_TAll2 T1 T2 U :
  T1 ~Tp[ shift p := shift q ] T2 →
  TAll U T1 ~Tp[ p := q ] TAll U T2
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
| ty_path_repl_TSing p1 p2 :
  p1 ~pp[ p := q ] p2 →
  TSing p1 ~Tp[ p := q ] TSing p2
where "T1 ~Tp[ p := q  ] T2" := (ty_path_repl p q T1 T2).

Notation ty_path_repl_rtc p q := (rtc (ty_path_repl p q)).
Notation "T1 ~Tp[ p := q  ]* T2" := (ty_path_repl_rtc p q T1 T2) (at level 70).

Lemma ty_path_repl_id p T1 T2 : T1 ~Tp[ p := p ] T2 → T1 = T2.
Proof.
  intros Hr; dependent induction Hr; rewrite ?IHHr //;
    f_equiv; exact: path_path_repl_id.
Qed.

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
Reserved Notation "r .p[ p := q  ]" (at level 65).
Fixpoint psubst_path p q r : path := match (decide (r = p)) with
| left _ => q
| _ =>
  match r with
  | pv _ => r
  (* While these values can in turn contain paths, pDOT path replacement
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
  | pself r' l => pself (r' .p[ p := q ]) l
  end
end
where "r .p[ p := q  ]" := (psubst_path p q r).

Lemma psubst_path_id p q : q .p[ p := p ] = q.
Proof. elim: q => /= *; case_decide; by f_equal. Qed.

Lemma psubst_path_self p q: p .p[ p := q ] = q.
Proof. case: p => /= *; by rewrite decide_True. Qed.

Reserved Notation "T .T[ p := q  ]" (at level 65).
Fixpoint psubst_ty p q T : ty := match T with
| TTop => TTop
| TBot => TBot
| TAnd T1 T2 => TAnd (T1 .T[ p := q ]) (T2 .T[ p := q ])
| TOr T1 T2 => TOr (T1 .T[ p := q ]) (T2 .T[ p := q ])
| TLater T1 => TLater (T1 .T[ p := q ])
| TAll T1 T2 => TAll (T1 .T[ p := q ]) (T2 .T[ shift p := shift q ])
| TMu T1 => TMu (T1 .T[ shift p := shift q ])
| TVMem l T1 => TVMem l (T1 .T[ p := q ])
| TTMem l T1 T2 => TTMem l (T1 .T[ p := q ]) (T2 .T[ p := q ])
| TSel r l => TSel (r .p[ p := q ]) l
| TPrim _ => T
| TSing r => TSing (r .p[ p := q ])
end
where "T .T[ p := q  ]" := (psubst_ty p q T).

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
  Local Hint Constructors path_path_repl ty_path_repl : core.

  (** Instances of [rtc_congruence] where inference needs help. *)
  Lemma path_path_repl_self_rtc p q p1 p2 l :
    p1 ~pp[ p := q ]* p2 →
    pself p1 l ~pp[ p := q ]* pself p2 l.
  Proof. apply rtc_congruence with (f := (λ p, pself p l)); auto. Qed.

  Lemma ty_path_repl_TSel_rtc p1 q1 p q l :
    p1 ~pp[ p := q ]* q1 →
    TSel p1 l ~Tp[ p := q ]* TSel q1 l.
  Proof. apply rtc_congruence with (f := (λ p, TSel p l)); auto. Qed.

  (** The reflexive, transitive closure of path replacement agrees with path
  substitution. In fact, there can be only 0 or 1 steps anyway. *)
  Lemma psubst_path_rtc_sufficient p1 q1 p q :
    p1 .p[ p := q ] = q1 →
    p1 ~pp[ p := q ]* q1.
  Proof.
    intros; subst q1.
    elim: p1 => [v|p1 IHp1 l] /=; case_decide as Hdec;
      [ | done | | exact: path_path_repl_self_rtc];
    rewrite Hdec; apply rtc_once; constructor.
  Qed.

  Lemma psubst_ty_rtc_sufficient T1 T2 p q :
    T1 .T[ p := q ] = T2 →
    T1 ~Tp[ p := q ]* T2.
  Proof.
    intros <-; move: p q.
    induction T1; intros; simpl; eauto using rtc_congruence, rtc_congruence2,
      ty_path_repl_TSel_rtc, psubst_path_rtc_sufficient, rtc_refl.
  Qed.
End decide_psubst.

(**
Finally, we can also define path substitution as a function.
Its proofs of correctness is in [path_repl_lemmas.v], in lemmas
[psubst_one_implies] and [psubst_subst_agree_ty].
*)
Definition psubst_one_base_path q p := q .p[ pv (ids 0) := shift p ].
Definition psubst_one_path q p := unshift (psubst_one_base_path q p).
Notation "q .pp[ p /]" := (psubst_one_path q p) (at level 65).

Definition psubst_one_base_ty T p := T .T[ pv (ids 0) := shift p ].
Definition psubst_one_ty T p := unshift (psubst_one_base_ty T p).
Notation "T .Tp[ p /]" := (psubst_one_ty T p) (at level 65).
