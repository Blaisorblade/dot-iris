(**
Lemmas on SynFuncs.v needed for proofs on the operational semantics.
To reduce compile times, unary_lr should not depend on this file.
This file should load as little Iris code as possible, to reduce compile times. But we must import operational.
 *)
From Dot Require Import tactics dotsyn operational.

(** Rewrite v ↗ ds to vobj ds' ↗ ds. *)
Ltac simplOpen ds' :=
  lazymatch goal with
  | H: ?v @ ?l ↘ ?d |-_=>
    inversion H as (ds & -> & _)
  end.

(** Determinacy of obj_opens_to. *)
Lemma objLookupDet v l d1 d2: v @ l ↘ d1 -> v @ l ↘ d2 -> d1 = d2.
Proof.
  rewrite /objLookup; intros; ev; by subst; injectHyps; optFuncs_det.
Qed.
Ltac objLookupDet :=
  lazymatch goal with
  | H1: ?v @ ?l ↘ ?d1, H2: ?v @ ?l ↘ ?d2 |- _=>
    assert (d2 = d1) as ? by (eapply objLookupDet; eassumption); injectHyps
  end.

(** Auxiliary definitions to prove [lookup_reverse_length], since a direct inductive proof appers to fail (but
see rev_append_map for an approach that has a chance). *)
Fixpoint indexr {X} (i: nat) (xs: list X) : option X :=
  match xs with
  | [] => None
  | x :: xs =>
    if decide (i = length xs) then Some x else indexr i xs
  end.

Lemma indexr_max {X} (T: X) i vs:
                       indexr i vs = Some T ->
                       i < length vs.
Proof.
  induction vs; first done; rewrite /lt in IHvs |- *; move => /= H.
  case_decide; subst; [ lia | eauto ].
Qed.
Hint Resolve indexr_max.

Lemma lookup_reverse_indexr {X} (ds: list X) l: reverse ds !! l = indexr l ds.
Proof.
  elim: ds l => [|d ds IHds] l //=.
  case_decide; subst.
  - rewrite reverse_cons lookup_app_r reverse_length ?Nat.sub_diag //=.
  - case (decide (l < length ds)) => Hl.
    + rewrite reverse_cons lookup_app_l ?reverse_length //=.
    + assert (l > length ds) by omega.
      assert (indexr l ds = None). {
        destruct (indexr l ds) eqn:? => //.
        assert (l < length ds) by (eapply indexr_max; eauto); lia.
      }
      rewrite lookup_ge_None_2 ?reverse_length //=.
Qed.

Lemma lookup_reverse_length {X} l (d: X) ds: l = length ds → reverse (d :: ds) !! l = Some d.
Proof.
  intros; subst. rewrite lookup_reverse_indexr /=. case_decide => //=.
Qed.

Lemma obj_lookup_cons d ds: vobj (d :: ds) @ length ds ↘ d.|[vobj (d :: ds)/].
Proof.
  hnf. eexists; split; trivial.
  rewrite /selfSubst /=. apply lookup_reverse_length. by rewrite map_length.
Qed.

Lemma indexr_extend {X} vs n x (T: X):
                       indexr n vs = Some T ->
                       indexr n (x::vs) = Some T.
Proof.
  move => H /=; assert (n < length vs) by naive_solver; by case_decide; first lia.
Qed.
Hint Resolve indexr_extend.

Lemma lookup_reverse_extend {X} l (d: X) ds:
  reverse ds !! l = Some d →
  reverse (d :: ds) !! l = Some d.
Proof.
  intros; subst. rewrite -> lookup_reverse_indexr in *. by apply indexr_extend.
Qed.

Lemma rev_append_map {X Y} (xs1 xs2: list X) (f: X → Y): rev_append (map f xs1) (map f xs2) = map f (rev_append xs1 xs2).
Proof.
  elim: xs1 xs2 => [|x xs1 IH] xs2 //=. eapply (IH (x :: xs2)).
Qed.
Lemma reverse_map {X Y} (xs: list X) (f: X → Y): reverse (map f xs) = map f (reverse xs).
Proof. rewrite /reverse. eapply (rev_append_map xs []). Qed.

Lemma lookup_map {X Y} x (xs: list X) (f: X → Y) l: xs !! l = Some x → map f xs !! l = Some (f x).
Proof.
  elim: xs l => /= [|x' xs IH] [|l] //= Hl; by [cinject Hl | apply IH].
Qed.

(* Lemma lookup_map_inv {X Y} x (xs: list X) (f: X → Y) l: map f xs !! l = Some (f x) → xs !! l = Some x. *)
(* Proof. *)
(*   elim: xs l => [|x' xs IH] [|l] //=. (* ONLY FOR F INDUCTIVE! *) *)

(* Lemma obj_lookup_extend d ds l: *)
(*   vobj ds @ l ↘ d.|[vobj ds/] → *)
(*   vobj (d :: ds) @ l ↘ d.|[vobj (d :: ds)/]. *)
(* Proof. *)
(*   hnf. *)
(*   intros (ds0 & Heq & Hl). cinject Heq. *)
(*   eexists; split; trivial. *)
(*   move: Hl. rewrite /selfSubst /lookup_reverse_indexr /= => Hl. *)
(*   apply lookup_reverse_extend. *)
(*   move: Hl. rewrite /hsubst /HSubst_dm !reverse_map => Hl. *)
(*   apply lookup_map. apply lookup_map_inv in Hl. apply Hl. *)
(*   (* eauto using lookup_map, lookup_map_inv. *) *)
(* Qed. *)


(* Auxiliary lemma for [length_idsσ]. *)
Lemma length_idsσr n r: length (idsσ n).|[ren r] = n.
Proof.
  elim : n r => [r | n IHn r] => //.
  asimpl. by rewrite IHn.
Qed.

Lemma length_idsσ n: length (idsσ n) = n.
Proof. pose proof (length_idsσr n (+0)) as Hr. asimpl in Hr. exact Hr. Qed.

Lemma subst_sigma_idsσ ρ n : length ρ = n →
                (subst_sigma (idsσ n) ρ) ≡ ρ.
Proof.
  rewrite /subst_sigma. move :n.
  induction ρ => *; subst => //; asimpl.
  f_equal. by apply IHρ.
Qed.

Lemma to_subst_app_is_lookup ρ x: x < length ρ → ρ !! x = Some (to_subst ρ x).
Proof.
  elim :ρ x => [|v ρ IHρ] [|x] //= Hl; try lia.
  rewrite to_subst_cons /=.
  apply IHρ; lia.
Qed.

Lemma rename_to_subst ρ1 ρ2 : (+length ρ1) >>> to_subst (ρ1 ++ ρ2) = to_subst ρ2.
Proof. induction ρ1; by asimpl. Qed.

Lemma undo_to_subst ρ : (+length ρ) >>> to_subst ρ = ids.
Proof.
  pose proof (rename_to_subst ρ []) as H. rewrite app_nil_r in H; asimpl in H. exact H.
Qed.

Lemma to_subst_weaken ρ1 ρ2 ρ3:
  upn (length ρ1) (ren (+length ρ2)) >> to_subst (ρ1 ++ ρ2 ++ ρ3) =
  to_subst (ρ1 ++ ρ3).
Proof.
  induction ρ1; asimpl.
  - by rewrite rename_to_subst.
  - by f_equal.
Qed.

Lemma to_subst_up ρ1 ρ2 v:
  upn (length ρ1) (v.[ren (+length ρ2)] .: ids) >> to_subst (ρ1 ++ ρ2) =
  to_subst (ρ1 ++ v :: ρ2).
Proof.
  induction ρ1; asimpl.
  - rewrite undo_to_subst. by asimpl.
  - by f_equal.
Qed.

Lemma closed_subst_vl_id v σ: nclosed_vl v 0 → v.[σ] = v.
Proof.
  intro Hcl. rewrite (Hcl σ ids) /=; first by asimpl.
  intros; omega.
Qed.

Lemma closed_to_subst ρ x: cl_ρ ρ → x < length ρ → nclosed_vl (to_subst ρ x) 0.
  elim: ρ x => /= [|v ρ IHρ] [|x] Hcl Hl; asimpl; try omega; inverse Hcl; try by [].
  by apply IHρ; try omega.
Qed.

Lemma fv_to_subst `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) ρ:
  nclosed a (length ρ) → cl_ρ ρ →
  nclosed (a.|[to_subst ρ]) 0.
Proof.
  rewrite /nclosed /nclosed_vl => Hcla Hclρ s1 s2 _ /=; asimpl.
  apply Hcla.
  intros x Hl; asimpl; rewrite !(closed_subst_vl_id (to_subst ρ x)); auto using closed_to_subst.
Qed.

Lemma fv_to_subst_vl v ρ:
  nclosed_vl v (length ρ) → cl_ρ ρ →
  nclosed_vl (v.[to_subst ρ]) 0.
Proof.
  rewrite /nclosed /nclosed_vl => Hclv Hclρ s1 s2 _ /=; asimpl.
  apply Hclv.
  intros x Hl; asimpl; rewrite !(closed_subst_vl_id (to_subst ρ x)); auto using closed_to_subst.
Qed.

(** Variants of [fv_to_subst] and [fv_to_subst_vl] for more convenient application. *)
Lemma fv_to_subst' `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) ρ a':
  nclosed a (length ρ) → cl_ρ ρ →
  a' = (a.|[to_subst ρ]) →
  nclosed a' 0.
Proof. intros; subst. by apply fv_to_subst. Qed.
Lemma fv_to_subst_vl' v ρ v':
  nclosed_vl v (length ρ) → cl_ρ ρ →
  v' = (v.[to_subst ρ]) →
  nclosed_vl v' 0.
Proof. intros; subst. by apply fv_to_subst_vl. Qed.

Implicit Types (T: ty).
Lemma lookup_success Γ x T: Γ !! x = Some T → x < length Γ.
Proof. apply lookup_lt_Some. Qed.

Lemma lookup_fv Γ x T: Γ !! x = Some T → nclosed (tv (var_vl x)) (length Γ).
Proof. rewrite /nclosed /nclosed_vl => * /=; f_equiv; eauto using lookup_success. Qed.

(** Not yet used. *)
Lemma eq_n_s_mon {n s1 s2}: eq_n_s s1 s2 (S n) → eq_n_s s1 s2 n.
Proof. rewrite /eq_n_s => HsEq x Hl; apply HsEq; omega. Qed.

(** The following ones are "direct" lemmas: deduce that an expression is closed
    by knowing that its subexpression are closed. *)

(** Needed by solve_fv_congruence when dealing with binders, such as in fv_vobj and fv_vabs. *)
Lemma eq_up s1 s2 n: eq_n_s s1 s2 n → eq_n_s (up s1) (up s2) (S n).
Proof.
  rewrite /up. move => Heq [|x] Hl //=. f_equiv. apply Heq. omega.
Qed.

(** Automated proof for such lemmas. *)
Ltac solve_fv_congruence := rewrite /nclosed /nclosed_vl => * /=; f_equiv; solve [(idtac + asimpl); auto using eq_up].

Implicit Types
         (L U: ty) (v: vl) (e: tm) (d: dm) (ds: dms)
         (Γ : ctx) (ρ : vls).

Lemma fv_tskip e n: nclosed e n → nclosed (tskip e) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_tproj e l n: nclosed e n → nclosed (tproj e l) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_tapp e1 e2 n: nclosed e1 n → nclosed e2 n → nclosed (tapp e1 e2) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_tv v n: nclosed_vl v n → nclosed (tv v) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_vobj ds n: nclosed ds (S n) → nclosed_vl (vobj ds) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_vabs e n: nclosed e (S n) → nclosed_vl (vabs e) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_dvl v n: nclosed_vl v n → nclosed (dvl v) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_dms_cons d ds: nclosed ds 0 → nclosed d 0 → nclosed (d :: ds) 0.
Proof. solve_fv_congruence. Qed.

(* Not needed right now, and doesn't work without a generic instance for HSubst X → HSubst (list X). *)
(* Lemma fv_cons `{Ids X} `{HSubst vl X} `{HSubst vl (list X)} {hsla: HSubstLemmas vl X} (x: X) xs: nclosed xs 0 → nclosed x 0 → nclosed (x :: xs) 0. *)
(* Proof. *)
(*   rewrite /nclosed /nclosed_vl => * /=. f_equiv. solve [(idtac + asimpl); auto using eq_up]. *)
(* Qed. *)

(** The following ones are "inverse" lemmas: by knowing that an expression is closed,
    deduce that one of its subexpressions is closed *)

(** Dealing with binders in fv "inverse" lemmas requires more infrastructure. See fv_vabs_inv_manual for an explanation. *)

Definition stail s := ren (+1) >> s.
Definition shead (s: var → vl) := s 0.

Lemma eq_n_s_tails {n s1 s2}: eq_n_s s1 s2 (S n) → eq_n_s (stail s1) (stail s2) n.
Proof. rewrite /stail => /= HsEq x Hl. apply HsEq. omega. Qed.
Lemma eq_n_s_heads {n s1 s2}: eq_n_s s1 s2 n → n > 0 → shead s1 = shead s2.
Proof. rewrite /shead => /= HsEq. apply HsEq. Qed.

Lemma decomp_s `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) s:
  a.|[s] = a.|[up (stail s)].|[shead s/].
Proof. by rewrite /stail /shead; asimpl. Qed.

Lemma decomp_s_vl v s:
  v.[s] = v.[up (stail s)].[shead s/].
Proof. by rewrite /stail /shead; asimpl. Qed.

(** Rewrite thesis with equalities learned from injection, if possible *)
Ltac rewritePremises := let H := fresh "H" in repeat (move => H; rewrite ?H {H}).

(** Here is a manual proof of a lemma, with explanations. *)
Lemma fv_vabs_inv_manual e n: nclosed_vl (vabs e) n → nclosed e (S n).
Proof.
  rewrite /nclosed_vl /nclosed => /= Hfv s1 s2 HsEq.

  (** From Hfv, we only learn that [e.|[up s1] = e.|[up s2]], for arbitrary [s1]
      and [s2], but substitutions in our thesis [e.|[s1] = e.|[s2]] are not of form [up ?].
      Hence, we rewrite it using [decomp_s] / [decomp_s_vl] to get a
      substitution of form [up ?], then rewrite with [e.|[up (stail s1)] =
      e.|[up (stail s2)]] (got from [Hfv]), and conclude.
      *)
  rewrite ?(decomp_s _ s1) ?(decomp_s _ s2) ?(decomp_s_vl _ s1) ?(decomp_s_vl _ s2) (eq_n_s_heads HsEq); last (by omega).
  injection (Hfv _ _ (eq_n_s_tails HsEq)); rewritePremises; reflexivity.
Qed.

(** Finally, a heuristic solver [solve_inv_fv_congruence] to be able to prove
    such lemmas easily, both here and elsewhere.
    Its internals are used directly in AAsynToSem. *)

Ltac solve_inv_fv_congruence_up_body Hfv s1 s2 HsEq :=
  rewrite ?(decomp_s _ s1) ?(decomp_s _ s2) ?(decomp_s_vl _ s1) ?(decomp_s_vl _ s2) (eq_n_s_heads HsEq); last (by omega);
  injection (Hfv _ _ (eq_n_s_tails HsEq)); by rewritePremises.

(* asimpl is expensive, but sometimes needed when simplification does mistakes.
   It must also be done after injection because it might not rewrite under Hfv's
   binders. *)
Ltac solve_inv_fv_congruence_body Hfv s1 s2 HsEq :=
  by [ injection (Hfv s1 s2); trivial; by (idtac + asimpl; rewritePremises; reflexivity) | solve_inv_fv_congruence_up_body Hfv s1 s2 HsEq ].

Ltac solve_inv_fv_congruence :=
  let s1 := fresh "s1" in
  let s2 := fresh "s2" in
  let HsEq := fresh "HsEq" in
  let Hfv := fresh "Hfv" in
  rewrite /nclosed_vl /nclosed /= => Hfv s1 s2 HsEq; solve_inv_fv_congruence_body Hfv s1 s2 HsEq.

(* The proof of this lemma needs asimpl and hence is expensive. *)
Lemma fv_vobj_ds_inv d ds n: nclosed_vl (vobj (d :: ds)) n → nclosed_vl (vobj ds) n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_tv_inv v n: nclosed (tv v) n → nclosed_vl v n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_vabs_inv e n: nclosed_vl (vabs e) n → nclosed e (S n).
Proof. solve_inv_fv_congruence. Qed.
Lemma fv_TAll_inv_2 n T1 T2: nclosed (TAll T1 T2) n → nclosed T2 (S n).
Proof. solve_inv_fv_congruence. Qed.
Lemma fv_TAll_inv_1 n T1 T2: nclosed (TAll T1 T2) n → nclosed T1 n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_idsσ n: nclosed (idsσ n) n.
Proof.
  elim: n => //=.
  rewrite /push_var /nclosed /eq_n_s //=; intros * IHn * Heq; asimpl.
  f_equiv; [| apply IHn; intros]; apply Heq => /=; lia.
Qed.

Lemma fv_dtysem ρ γ l: nclosed ρ l → nclosed (dtysem ρ γ) l.
Proof. solve_fv_congruence. Qed.

Lemma fv_vls_cons v vs: nclosed vs 0 → nclosed_vl v 0 → nclosed (v :: vs) 0.
Proof. solve_fv_congruence. Qed.

Lemma cl_ρ_fv ρ : cl_ρ ρ → nclosed ρ 0.
  induction ρ => // Hcl.
  inverse Hcl. apply fv_vls_cons => //. apply IHρ => //.
Qed.
