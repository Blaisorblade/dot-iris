From iris.proofmode Require Import tactics.
From Coq.ssr Require Import ssrbool.

From D.Dot Require Import syn syn.path_repl.
From D.Dot Require Import stampingDefsCore.

Implicit Types (Pv : vl → Prop).
Set Nested Proofs Allowed.

Notation unshifts T := (∃ T', T = shift T').
Notation unshifts_vl v := (∃ v', v = shiftV v').
Notation pred := Nat.pred.
Notation unshiftV v := v.[ren pred].

Lemma shift_unshift `{Sort X} (x : X): unshift (shift x) = x.
Proof. by rewrite hsubst_comp hsubst_id. Qed.

Lemma shift_unshift_vl v: unshiftV (shiftV v) = v.
Proof. by rewrite subst_comp subst_id. Qed.

Implicit Types
         (T : ty) (v w : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (Γ : ctx) (vs : vls) (l : label).

Definition psubst_one_base T p := (T .T[ pv (ids 0) := shift p ]).
Definition psubst_one T p := (unshift (psubst_one_base T p)).

Definition psubst_one_works T p := (unshifts (psubst_one_base T p)).

Definition unshiftsN `{Sort X} i (x : X) := x.|[upn i (ren pred)].|[upn i (ren (+1))] = x.
Definition unshiftsN_vl i v := v.[upn i (ren pred)].[upn i (ren (+1))] = v.

Definition unshifts_vl_equiv v : unshiftsN_vl 0 v ↔ unshifts_vl v.
Proof.
  rewrite /unshiftsN_vl !iterate_0; split.
  by exists (unshiftV v).
  by destruct 1; simplify_eq; rewrite shift_unshift_vl.
Qed.

Definition unshifts_equiv `{Sort X} (x : X) : unshiftsN 0 x ↔ unshifts x.
Proof.
  rewrite /unshiftsN !iterate_0; split.
  by exists (unshift x).
  by destruct 1; simplify_eq; rewrite shift_unshift.
Qed.

Lemma ren_comp r s : ren r >> ren s = ren (r >>> s).
Proof. done. Qed.
Lemma up_reduce s x : (up s (S x) : vl) = shiftV (s x).
Proof. by rewrite -rename_subst. Qed.

Notation upn_mp1 i := (upn i (ren (pred >>> (+1)))).

Lemma ren_const x i : x ≠ i → upn_mp1 i x = var_vl x.
Proof.
  move => /Nat.eqb_spec.
  elim: i x => [|i IHi] x Hne //=; rewrite ?iterate_0; first by cbv; case_match.
  case: x Hne => [//|x] Hne. by rewrite iterate_S up_reduce (IHi x Hne).
Qed.

Lemma unstamped_val_unshifts v i n :
  is_unstamped_path n (pv v) → v ≠ ids i → unshiftsN_vl i v.
Proof.
  move E: (pv v) => p Hu Hne; destruct Hu as [? w _ [j ?]|]; simplify_eq/=.
  have {}Hne: j ≠ i by naive_solver.
  rewrite /unshiftsN_vl subst_comp up_comp_n.
  exact: ren_const.
Qed.

(* Lemma unstamped_val_unshifts_0 v n :
  is_unstamped_path n (pv v) → v ≠ ids 0 → unshifts_vl v.
Proof. rewrite -unshifts_vl_equiv; apply unstamped_val_unshifts. Qed. *)

Lemma is_unstamped_path_root n p :
  is_unstamped_path n p →
  is_unstamped_path n (pv (path_root p)).
Proof. elim: p => //=; intros; with_is_unstamped inverse; eauto. Qed.

Lemma unstamped_path_unshifts_n p i n :
  path_root p ≠ ids i → is_unstamped_path n p → unshiftsN_vl i (path_root p).
Proof. intros Hne Hu%is_unstamped_path_root. exact: unstamped_val_unshifts. Qed.

(*
(* Unused for now; generalize? *)
Lemma psubst_one_base_unshifts_path q p :
  unshifts_vl (path_root q) →
  unshifts (q .p[ pv (ids 0) := shift p]).
Proof.
  intros [v' Hu].
  exists (unshift (q .p[ pv (ids 0) := shift p])).
  move: p Hu; induction q => p //=; try case_decide;
    rewrite ?shift_unshift // => Hp.
  - by rewrite Hp /= !subst_comp.
  - by rewrite (IHq p Hp) /= shift_unshift.
Qed. *)


Definition psubst_one_path_gen i q p :=
  q .p[ pv (ids i) := shiftN (S i) p ].
Definition psubst_one_ty_gen i T p :=
  T .T[ pv (ids i) := shiftN (S i) p ].

Lemma unshiftsN_shiftN i p : unshiftsN i (shiftN (S i) p).
Proof.
  rewrite /unshiftsN.
  elim: i => [|i]; first by rewrite shift_unshift.
  rewrite {2}(hrenS _ (S i)) => <-.
  rewrite !hsubst_comp.
  abstract autosubst.
Qed.

Lemma psubst_one_path_gen_unshifts_gen i n q p :
  is_unstamped_path n q →
  unshiftsN i (psubst_one_path_gen i q p).
Proof.
  move: p i; induction q => p i Hu //; last by inverse Hu;
    rewrite /psubst_one_path_gen /unshiftsN in IHq |- *; f_equal/=; eauto.
  hnf; cbn. case_decide; simplify_eq/=; first exact: unshiftsN_shiftN.
  have ?: v ≠ var_vl i by naive_solver.
  suff Hr: unshiftsN_vl i v by f_equal.
  exact: unstamped_val_unshifts.
Qed.

Lemma psubst_one_base_unshifts_gen i n T p :
  is_unstamped_ty n T → unshiftsN i (psubst_one_ty_gen i T p).
Proof.
  rewrite /psubst_one_ty_gen /unshiftsN.
  move: p i n; induction T => p0 i n Hu; f_equal/=; with_is_unstamped inverse;
    rewrite -?hrenS -?iterate_S; eauto; exact: psubst_one_path_gen_unshifts_gen.
Qed.

Lemma psubst_one_base_unshifts {n T} p:
  is_unstamped_ty n T → psubst_one_works T p.
Proof.
  exists (unshift (psubst_one_base T p)).
  rewrite /psubst_one_base.
  have := psubst_one_base_unshifts_gen 0 n T p.
  by rewrite /unshiftsN /psubst_one_ty_gen ?iterate_S !iterate_0 => ->.
Qed.

(** This lemma shows that functional path substitution function implies
relational path substitution (the main one we use). *)
Lemma psubst_one_implies n T p T'
  (Hu : is_unstamped_ty n T) :
  psubst_one T p = T' → T .Tp[ p /]~ T'.
Proof.
  have := psubst_one_base_unshifts p Hu.
  case; rewrite /psubst_one /psubst_one_base => T'' Hw Heq.
  rewrite -Heq. apply psubst_ty_rtc_sufficient.
  by rewrite Hw shift_unshift.
Qed.

(**
https://en.wikipedia.org/wiki/Idempotence#Idempotent_functions *)
Definition IdempotentUnary {A} (f: A → A) := ∀ x, f (f x) = f x.

Lemma decide_unshift_proof {T} : T ≠ shift (unshift T) → unshifts T → False.
Proof. move => Hne [T' Hn]. apply: Hne. by rewrite Hn shift_unshift. Qed.

Definition decide_unshift T : unshifts T + (unshifts T → False) :=
  match decide (T = shift (unshift T)) with
  | left Heq => inl (ex_intro _ (unshift T) Heq)
  | right Hne => inr (decide_unshift_proof Hne)
  end.
Instance decision_unshift T : Decision (∃ T', T = shift T').
Proof. by destruct (decide_unshift T) as [Heq|Hne]; [left|right]. Qed.

(* Definition unshift_opt (T : ty) : option ty :=
  if decide (T = (unshiftB T).|[ren (+1)])
  then Some (unshiftB T)
  else None. *)

(** Lemma [psubst_path_implies] requires [path_repl_longer], which
requires a diversion to prove.
I'm not sure going through sizes is the shortest proof, but that's the
obvious way on paper, and works well in Coq too. *)
Section psubst_path_implies_lemmas.
  Definition append_ls p (ls : list label) : path := foldr (flip pself) p ls.

  Fixpoint path_size p := match p with
    | pv _ => 0
    | pself p _ => 1 + path_size p
    end.

  Lemma occurs_in_path_repl {p1 p2 p q} :
    p1 ~pp[ p := q ] p2 →
    ∃ n, n + path_size p = path_size p1.
  Proof.
    elim => [|p1' p2' l Hr [n IHr]];
      [ by exists 0 | exists (S n); by rewrite /= IHr].
  Qed.

  Lemma path_size_append p ls :
    path_size (append_ls p ls) = length ls + path_size p.
  Proof. by elim: ls => /= [| _ ls ->]. Qed.

  Lemma path_repl_longer ls {p p1 p2 q l} :
    p1 ~pp[ p := q ] p2 →
    ~append_ls p1 (l :: ls) = p.
  Proof.
    move => /occurs_in_path_repl [ls' Hr] /(f_equal path_size).
    rewrite /= path_size_append. lia.
  Qed.
End psubst_path_implies_lemmas.

(** Path substitution agrees with path replacement. *)
Lemma psubst_path_implies p1 p2 p q :
  p1 ~pp[ p := q ] p2 →
  p1 .p[ p := q ] = p2.
Proof.
  move => Hr.
  elim: Hr => [|p1' p2' l Hr IHr] /=; first exact: psubst_path_self.
  case_decide as Hdec => //; last by rewrite -IHr.
  exfalso; exact: (path_repl_longer []).
Qed.

Goal ~(∀ p q, IdempotentUnary (psubst_path p q)).
Proof.
  move => Hpsubst_path_idempotent.
  set p0 := pv (ids 0).
  move: (Hpsubst_path_idempotent p0 (pself p0 "A") p0).
  by repeat (simplify_eq/=; case_decide).
Qed.


Lemma psubst_path_pv_idempotent v q
  (Heq : psubst_path (pv v) q q = q):
  IdempotentUnary (psubst_path (pv v) q).
Proof.
  elim => [vr|r' IHq l] /=; repeat (case_decide; simplify_eq/=); by f_equal.
Qed.

Lemma psubst_one_shift_id q r : shift r .p[ pv (ids 0) := q ] = shift r.
Proof.
  elim: r => /= [v|r -> //]; case_decide => //; destruct v; simplify_eq.
Qed.

Lemma psubst_path_one_idempotent q:
  IdempotentUnary (psubst_path (pv (ids 0)) (shift q)).
Proof. apply psubst_path_pv_idempotent, psubst_one_shift_id. Qed.

  (* move: p; induction T => p0; try by [f_equal/=; eauto].
  f_equal/=; eauto.

  set T' := λ i, T .T[ pv (ids i) := iterate (λ T, shift T) (i+1) p0 ].
  rewrite !hsubst_comp up_comp.
  rewrite IHT1.
  SearchAbout (up _ >> up _).
  autosubst.
Abort. *)

(*
Lemma psubst_one_sufficient T1 T2 p q :
  psubst_one T1 p = T2 →
  T1 .Tp[ p /]~ T2.
Proof.
  rewrite /psubst_one.
  move: (psubst_one_base_unshifts T1 p) => [T' Hrew] <-.
  rewrite Hrew shift_unshift.
  apply psubst_ty_rtc_sufficient, Hrew.
Qed. *)

(**
  Never even remotely true. One thing substitutes away, another substitutes
  in the same conrtext. Pick carefully! *)
(* Lemma equiv p q r r':
  shift r' = psubst_path (pv (ids 0)) (shift q) r →
  r' = psubst_path (pv (ids 0)) q r.
Proof.
  elim: r => /= [v|r IHr l]; case_decide.
  (* rewrite shift_unshift. *)
  by rewrite hsubst_comp hsubst_id. *)

Lemma psubst_path_idempotent: ∀ p q,
  psubst_path p q q = q →
  IdempotentUnary (psubst_path p q).
Proof.
  move => p q Heq r.
  elim E: r => [v|r' IHq l] //=; case_decide as Hdec0; simplify_eq/= => //;
    case_decide as Hdec1; simplify_eq; f_equal => //.
  rewrite Hdec1.
  exfalso.
  apply Hdec0. rewrite -Hdec1. f_equal. rewrite -Heq.
Abort.

Section  psubst_path_idempotent_counterexample.
Variable l : string.
Let q := pv (ids 0).
Let p := pself q l.
Let r := p.
Let r' := pself r l.
Ltac check := cbn; repeat (case_decide; simplify_eq/=); try done.
(* rewrite /r/p/q/=; repeat (case_decide; cbn); naive_solver. *)

Goal q .p[ p := q ] = q.
Proof. check. Qed.

Goal pself r l ≠ p.
Proof. check. Qed.
Goal pself (r .p[ p := q ]) l = p.
Proof. check. Qed.
Goal psubst_path p q q = q.
Proof. check. Qed.

Goal (r .p[ p := q ]) .p[ p := q ] = r .p[ p := q ].
Proof. check. Qed.

Lemma foo : r' .p[ p := q ] .p[ p := q ] ≠ r' .p[ p := q ].
Proof. check. Qed.

Goal ~IdempotentUnary (psubst_path p q).
Proof. move => /(_ r'). apply foo. Qed.

Lemma not_psubst_path_idempotent: ~∀ p q,
  psubst_path p q q = q →
  IdempotentUnary (psubst_path p q).
Proof. move => /(_ p q _ r'). check. eauto. Qed.
End psubst_path_idempotent_counterexample.

(* Lemma replacing_again_wont_save_you p q p1 p2:
  p1 ≠ p2 →
  p1 .p[ p := q ] ≠ p2 → ~ p1 ~pp[ p := q ]* p2.
Proof.
  move => Hne Hne2 Hr.
  elim: Hr Hne Hne2 => [//|p1' p2' {}p2 Hh Ht IHr] Hne Hne2.
  move: (Hh) => /psubst_path_implies Hq1.
  simplify_eq.
  apply IHr => //.
  by rewrite psubst_path_idempotent.
Qed. *)

(* Lemma psubst_path_rtc_dec p1 p2 p q :
  Decision (p1 ~pp[ p := q ]* p2).
Proof.
  case: (decide (p1 = p2)) => [->|Hne]; first by left; constructor.
  case: (decide (p1 .p[ p := q ] = p2)) => [<-|Hne2];
    first by left; exact: psubst_path_rtc_sufficient.
  right => Hrepl. exact: replacing_again_wont_save_you.
Qed. *)


Section psubst_path_implies_lemmas_extras.
  Lemma occurs_in_path_repl_append {p1 p2 p q} :
    p1 ~pp[ p := q ] p2 →
    ∃ ls, append_ls p ls = p1.
  Proof.
    elim => [|p1' p2' l' Hr [ls' IHr]];
      [ exists [] | exists (l' :: ls')]; by simplify_eq.
  Qed.

  Lemma paths_well_founded {ls1 ls2 p q l} :
    append_ls q (l :: ls1) = p →
    ~append_ls p ls2 = q.
  Proof.
    move => /(f_equal path_size) Heq1 /(f_equal path_size) Heq2.
    move: Heq1 Heq2. rewrite !path_size_append /=. lia.
  Qed.

  Lemma path_repl_longer2 ls {p p1 p2 q l} :
    p1 ~pp[ p := q ] p2 →
    ~append_ls p1 (l :: ls) = p.
  Proof.
    move => /occurs_in_path_repl_append [ls' Hr] Happ.
    exact: paths_well_founded.
  Qed.
End psubst_path_implies_lemmas_extras.

(* Useful ???*)
Lemma psubst_path_eq p q r: psubst_path p q r =
  match (decide (r = p)) with
  | left _ => q
  | _ =>
    match r with
    | pv _ => r
    | pself r' l => pself (psubst_path p q r') l
    end
  end.
Proof. by case: r. Qed.
