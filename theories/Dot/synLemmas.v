(**
Lemmas on SynFuncs.v needed for proofs on the operational semantics.
To reduce compile times, unary_lr should not depend on this file.
This file should load as little Iris code as possible, to reduce compile times.
 *)
From D Require Import tactics.
From D.Dot Require Import dotsyn.

(* Auxiliary lemma for [length_idsσ]. *)
Lemma length_idsσr n r: length (idsσ n).|[ren r] = n.
Proof.
  elim : n r => [r | n IHn r] => //.
  asimpl. by rewrite IHn.
Qed.

Lemma length_idsσ n: length (idsσ n) = n.
Proof. pose proof (length_idsσr n (+0)) as Hr. asimpl in Hr. exact Hr. Qed.

Lemma subst_sigma_idsσ ρ n : length ρ = n →
                (subst_sigma (idsσ n) ρ) = ρ.
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

Lemma closed_subst_id `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) σ: nclosed a 0 → a.|[σ] = a.
Proof.
  intro Hcl. rewrite (Hcl σ ids) /=; first by asimpl.
  intros; omega.
Qed.

Lemma closed_to_subst ρ x: cl_ρ ρ → x < length ρ → nclosed_vl (to_subst ρ x) 0.
Proof.
  elim: ρ x => /= [|v ρ IHρ] [|x] Hcl Hl; asimpl; try omega; inverse Hcl; try by [].
  by apply IHρ; try omega.
Qed.

(** Let's prove that [nclosed a n → a.|[to_subst (idsσ n)] = a], and ditto for values. *)
Section to_subst_idsσ_is_id.
  Lemma to_subst_map_commute_aux f n x r: x < n → to_subst (map f (idsσ n).|[ren r]) x = f (to_subst (idsσ n).|[ren r] x).
  Proof.
    elim: n r x => [|n IHn] r x Hle; first omega.
    destruct x; first done; asimpl.
    apply IHn; omega.
  Qed.

  Lemma to_subst_map_commute f n x: x < n → to_subst (map f (idsσ n)) x = f (to_subst (idsσ n) x).
  Proof. pose proof (to_subst_map_commute_aux f n x (+0)) as H. asimpl in H. exact H. Qed.

  Lemma idsσ_eq_ids n: eq_n_s (to_subst (idsσ n)) ids n.
  Proof.
    induction n => x Hle. by rewrite to_subst_nil.
    destruct x => //=.
    assert (x < n) as Hle' by auto using lt_S_n.
    rewrite to_subst_cons /= to_subst_map_commute // IHn //.
  Qed.

  Lemma closed_subst_idsρ `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) n :
    nclosed a n → a.|[to_subst (idsσ n)] = a.
  Proof.
    intro Hcl. rewrite (Hcl _ ids); first by asimpl. by apply idsσ_eq_ids.
  Qed.

  Lemma closed_subst_vl_idsρ v n:
    nclosed_vl v n → v.[to_subst (idsσ n)] = v.
  Proof.
    intro Hcl. rewrite (Hcl _ ids); first by asimpl. by apply idsσ_eq_ids.
  Qed.
End to_subst_idsσ_is_id.

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

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms)
         (Γ : ctx) (ρ : vls).

Lemma lookup_success Γ x T: Γ !! x = Some T → x < length Γ.
Proof. apply lookup_lt_Some. Qed.

Lemma lookup_fv Γ x T: Γ !! x = Some T → nclosed (tv (var_vl x)) (length Γ).
Proof. rewrite /nclosed /nclosed_vl => * /=; f_equiv; eauto using lookup_success. Qed.

(** Not yet used. *)
Lemma eq_n_s_mon {n s1 s2}: eq_n_s s1 s2 (S n) → eq_n_s s1 s2 n.
Proof. rewrite /eq_n_s => HsEq x Hl; apply HsEq; omega. Qed.

(** The following ones are "direct" lemmas: deduce that an expression is closed
    by knowing that its subexpression are closed. *)

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

Lemma fv_dtysem ρ γ l: nclosed ρ l → nclosed (dtysem ρ γ) l.
Proof. solve_fv_congruence. Qed.

Definition fv_dms_cons : ∀ d ds, nclosed ds 0 → nclosed d 0 → nclosed (d :: ds) 0 := fv_cons.

Lemma fv_vls_cons : ∀ v vs, nclosed vs 0 → nclosed_vl v 0 → nclosed (v :: vs) 0.
Proof. solve_fv_congruence. Qed.

Lemma fv_idsσ n: nclosed (idsσ n) n.
Proof.
  elim: n => //=.
  rewrite /push_var /nclosed /eq_n_s //=; intros * IHn * Heq; asimpl.
  f_equiv; [| apply IHn; intros]; apply Heq => /=; lia.
Qed.

Lemma cl_ρ_fv ρ : cl_ρ ρ → nclosed ρ 0.
Proof.
  induction ρ => // Hcl.
  inverse Hcl. apply fv_vls_cons => //. by apply IHρ.
Qed.

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
  rewrite ?(decomp_s _ s1) ?(decomp_s _ s2) ?(decomp_s_vl _ s1) ?(decomp_s_vl _ s2) (eq_n_s_heads HsEq); last omega.
  injection (Hfv _ _ (eq_n_s_tails HsEq)); rewritePremises; reflexivity.
Qed.

(** Finally, a heuristic solver [solve_inv_fv_congruence] to be able to prove
    such lemmas easily, both here and elsewhere. *)

Ltac solve_inv_fv_congruence :=
  let s1 := fresh "s1" in
  let s2 := fresh "s2" in
  let HsEq := fresh "HsEq" in
  let Hfv := fresh "Hfv" in
  rewrite /nclosed_vl /nclosed /= => Hfv s1 s2 HsEq;
(* asimpl is expensive, but sometimes needed when simplification does mistakes.
   It must also be done after injection because it might not rewrite under Hfv's
   binders. *)
  by [ injection (Hfv s1 s2); trivial; by (idtac + asimpl; rewritePremises; reflexivity) |
       rewrite ?(decomp_s _ s1) ?(decomp_s _ s2) ?(decomp_s_vl _ s1) ?(decomp_s_vl _ s2) (eq_n_s_heads HsEq); last omega;
       injection (Hfv _ _ (eq_n_s_tails HsEq)); by rewritePremises ].

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
