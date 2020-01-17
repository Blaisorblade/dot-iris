From iris.proofmode Require Import tactics.
From D.Dot Require Import syn syn.path_repl.
From D.Dot Require Import stampingDefsCore unstampedness_binding closed_subst.

Implicit Types
         (T : ty) (v w : vl) (t : tm) (d : dm) (ds : dms) (p q : path)
         (Γ : ctx) (vs : vls) (l : label).

From Coq.ssr Require Import ssrbool.
(** [ssrbool] shadows [pred], shadow it back. *)
Notation pred := Nat.pred.
Set Implicit Arguments.

Definition unshiftsN `{Sort X} i (x : X) := x.|[upn i (ren pred)].|[upn i (ren (+1))] = x.
Definition unshiftsN_vl i v := v.[upn i (ren pred)].[upn i (ren (+1))] = v.

Lemma shift_unshift `{Sort X} (x : X): unshift (shift x) = x.
Proof. by rewrite hsubst_comp hsubst_id. Qed.

Lemma unshiftsN_shiftN i p : unshiftsN i (shiftN (S i) p).
Proof.
  rewrite /unshiftsN.
  elim: i => [|i]; first by rewrite shift_unshift.
  rewrite {2}(hrenS _ (S i)) => <-.
  rewrite !hsubst_comp.
  abstract autosubst.
Qed.

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
  is_unstamped_path' n (pv v) → v ≠ ids i → unshiftsN_vl i v.
Proof.
  move E: (pv v) => p. move E': (n, InType) => I Hu Hne.
  destruct Hu as [? w _ Hs|]; simplify_eq/=.
  destruct Hs as [|[j ?]]; simplify_eq/=.
  have {}Hne: j ≠ i by naive_solver.
  rewrite /unshiftsN_vl subst_comp up_comp_n.
  exact: ren_const.
Qed.

Definition psubst_one_path_gen i q p :=
  q .p[ pv (ids i) := shiftN (S i) p ].
Definition psubst_one_ty_gen i T p :=
  T .T[ pv (ids i) := shiftN (S i) p ].

Lemma psubst_one_path_gen_unshifts_gen i n q p :
  is_unstamped_path' n q →
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
  is_unstamped_ty' n T → unshiftsN i (psubst_one_ty_gen i T p).
Proof.
  rewrite /psubst_one_ty_gen /unshiftsN.
  move: p i n; induction T => p0 i n Hu; f_equal/=; with_is_unstamped inverse;
    rewrite -?hrenS -?iterate_S; eauto; exact: psubst_one_path_gen_unshifts_gen.
Qed.

Notation unshifts x := (∃ x', x = shift x').

Lemma psubst_one_base_unshifts {n T} p:
  is_unstamped_ty' n T → unshifts (psubst_one_ty_base T p).
Proof.
  intros Hu; exists (unshift (psubst_one_ty_base T p)).
  rewrite /psubst_one_ty_base.
  have := psubst_one_base_unshifts_gen 0 p Hu.
  by rewrite /unshiftsN /psubst_one_ty_gen ?iterate_S !iterate_0 => ->.
Qed.

(** This lemma shows that functional path substitution function implies
relational path substitution (the main one we use). *)
Lemma psubst_one_implies n T p T' :
  is_unstamped_ty' n T →
  psubst_one_ty T p = T' → T .Tp[ p /]~ T'.
Proof.
  move => /(psubst_one_base_unshifts p) [T''].
  rewrite /psubst_one_ty /psubst_one_ty_base => Hw <-.
  apply psubst_ty_rtc_sufficient.
  by rewrite Hw shift_unshift.
Qed.

Lemma is_unstamped_path_subst_gen i n p q :
  is_unstamped_path' (S i + n) q →
  is_unstamped_path' n p →
  is_unstamped_path' (S i + n) (psubst_one_path_gen i q p).
Proof.
  rewrite /psubst_one_path_gen.
  move: p i; induction q => p i Hu Hup //=; last by (constructor;
    inverse Hu; simplify_eq/=; eauto).
  case_decide; simplify_eq => //.
  (* eauto 4 using is_unstamped_sub_ren_path, is_unstamped_weaken_path with lia. *)
  eapply is_unstamped_sub_ren_path, Hup; eauto with lia.
Qed.

Lemma is_unstamped_ty_subst_gen i n T p :
  is_unstamped_ty' (S i + n) T →
  is_unstamped_path' n p →
  is_unstamped_ty' (S i + n) (psubst_one_ty_gen i T p).
Proof.
  rewrite /psubst_one_ty_gen /unshiftsN.
  move: p i n; induction T => p0 i n Hu; f_equal/=; with_is_unstamped inverse;
    constructor; rewrite -?hrenS -?iterate_S /=;
    change (S (i + n)) with (S i + n); eauto; exact: is_unstamped_path_subst_gen.
Qed.

Lemma is_unstamped_ty_subst n T p :
  is_unstamped_ty' (S n) T →
  is_unstamped_path' n p →
  is_unstamped_ty' n (psubst_one_ty T p).
Proof.
  intros HuT Hup; have /= := (is_unstamped_ty_subst_gen (i := 0) HuT Hup).
  rewrite /psubst_one_ty /psubst_one_ty_gen -/(psubst_one_ty_base T p).
  have [T' ->] := (psubst_one_base_unshifts p HuT).
  rewrite shift_unshift. apply is_unstamped_ren_ty.
Qed.

Lemma upn_app i v s :
  upn i (v .: s) i = shiftVN i v.
Proof.
  elim: i => [|i IHi] //=.
  by rewrite subst_id iterate_0.
  by rewrite iterate_S up_reduce IHi -renS.
Qed.

Lemma upn_reduce i s x :
  upn (S i) s (S x) =@{vl} shiftV (upn i s x).
Proof. by rewrite iterate_S up_reduce. Qed.

Lemma upn_app_ids_ne x i v :
  x ≠ i → upn i ((v .: ids) >> ren (+1)) x = ids x.
Proof.
  move => /Nat.eqb_spec.
  elim: i x => [|i IHi] x Hne //=. by rewrite iterate_0 /scons/=; case_match.
  case: x Hne => /= [|x] Hne.
  autosubst.
  by rewrite upn_reduce IHi.
Qed.

(* relative of [hren_upn] *)
Lemma ren_upn i v : v.[ren (+i)].[upn i (ren (+1))] = v.[ren (+S i)].
Proof.
  move: (ren_upn_gen i 0 1). by rewrite plusnS !plusnO subst_comp =>->.
Qed.

Lemma psubst_subst_agree_path_gen p v i n :
  is_unstamped_path' n p →
  psubst_one_path_gen i p (pv v) = p.|[ upn i ((v .: ids) >> ren (+1)) ].
Proof.
  rewrite /psubst_one_path_gen; move: i.
  induction p => i //=; f_equal/=; intros; with_is_unstamped inverse; last eauto with f_equal.
  simpl in *; destruct_or!; try done; ev; case_decide; simplify_eq/=; f_equal.
  by rewrite -up_comp_n /= upn_app ren_upn.
  rewrite upn_app_ids_ne; naive_solver.
Qed.

Lemma psubst_subst_agree_ty_gen T v i n :
  is_unstamped_ty' n T →
  psubst_one_ty_gen i T (pv v) = T.|[ upn i ((v .: ids) >> ren (+1)) ].
Proof.
  rewrite /psubst_one_ty_gen; move: i n.
  induction T => i n Hu //=; with_is_unstamped inverse; f_equal/=;
  rewrite -?(renS, iterate_S); eauto; exact: psubst_subst_agree_path_gen.
Qed.

Lemma psubst_subst_agree_path p n v
  (Hu : is_unstamped_path' n p) :
  p .pp[ pv v /] = p .|[ v /].
Proof.
  have := psubst_subst_agree_path_gen v 0 Hu.
  rewrite iterate_0 /psubst_one_path /psubst_one_path_base /psubst_one_path_gen => ->.
  rewrite -(shift_unshift p.|[v/]); f_equal.
  by rewrite hsubst_comp.
Qed.

Lemma psubst_subst_agree_ty T n v
  (Hu : is_unstamped_ty' n T) :
  T .Tp[ pv v /] = T .|[ v /].
Proof.
  have := psubst_subst_agree_ty_gen v 0 Hu.
  rewrite iterate_0 /psubst_one_ty /psubst_one_ty_base /psubst_one_ty_gen => ->.
  rewrite -(shift_unshift T.|[v/]); f_equal.
  by rewrite hsubst_comp.
Qed.
