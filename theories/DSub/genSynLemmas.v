(**
Syntax/binding lemmas shared between DSub and Dot. They should be abstracted ideally, if Coq let us.
 *)
From D Require Import tactics.
From D.DSub Require Import syn.

Implicit Types (v: vl) (ρ : vls).
(* Auxiliary lemma for [length_idsσ]. *)
Lemma length_idsσr n r: length (idsσ n).|[ren r] = n.
Proof.
  elim: n r => [r | n IHn r] => //.
  asimpl. by rewrite IHn.
Qed.

Lemma length_idsσ n: length (idsσ n) = n.
Proof. move: (length_idsσr n (+0)) => Hgoal. by asimpl in Hgoal. Qed.
Hint Resolve length_idsσ.

Lemma subst_sigma_idsσ ρ n : length ρ = n →
                (subst_sigma (idsσ n) ρ) = ρ.
Proof.
  rewrite /subst_sigma. move :n.
  induction ρ => *; subst => //; asimpl.
  f_equal. by apply IHρ.
Qed.

Lemma to_subst_app_is_lookup ρ i: i < length ρ → ρ !! i = Some (to_subst ρ i).
Proof.
  elim: ρ i => [|v ρ IHρ] [|i] //= Hl; try lia.
  rewrite to_subst_cons /=.
  apply IHρ; lia.
Qed.

Lemma rename_to_subst ρ1 ρ2 : (+length ρ1) >>> to_subst (ρ1 ++ ρ2) = to_subst ρ2.
Proof. induction ρ1; by asimpl. Qed.

Lemma undo_to_subst ρ : (+length ρ) >>> to_subst ρ = ids.
Proof.
  move: (rename_to_subst ρ []) => Hgoal. by do [rewrite app_nil_r; asimpl] in Hgoal.
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
  intros; lia.
Qed.

Lemma closed_subst_id `{Ids X} `{HSubst vl X} {hsla: HSubstLemmas vl X} (x: X) σ: nclosed x 0 → x.|[σ] = x.
Proof.
  intro Hcl. rewrite (Hcl σ ids) /=; first by asimpl.
  intros; lia.
Qed.

Lemma closed_to_subst ρ i n: nclosed_σ ρ n → i < length ρ → nclosed_vl (to_subst ρ i) n.
Proof.
  elim: ρ i => /= [|v ρ IHρ] [|i] Hcl Hl; asimpl; try lia; inverse Hcl; try by [].
  by apply IHρ; try lia.
Qed.

(** Let's prove that [nclosed x n → x.|[to_subst (idsσ n)] = x], and ditto for values. *)
Section to_subst_idsσ_is_id.
  Lemma to_subst_map_commute_aux f n i r: i < n → to_subst (map f (idsσ n).|[ren r]) i = f (to_subst (idsσ n).|[ren r] i).
  Proof.
    elim: n r i => [|n IHn] r i Hle; first lia.
    destruct i; first done; asimpl.
    apply IHn; lia.
  Qed.

  Lemma to_subst_map_commute f n i: i < n → to_subst (map f (idsσ n)) i = f (to_subst (idsσ n) i).
  Proof. move: (to_subst_map_commute_aux f n i (+0)) => Hgoal. by asimpl in Hgoal. Qed.

  Lemma idsσ_eq_ids n: eq_n_s (to_subst (idsσ n)) ids n.
  Proof.
    induction n => i Hle. by rewrite to_subst_nil.
    destruct i => //=.
    assert (i < n) as Hle' by auto using lt_S_n.
    rewrite to_subst_cons /= to_subst_map_commute // IHn //.
  Qed.

  Lemma closed_subst_idsρ `{Ids X} `{HSubst vl X} {hsla: HSubstLemmas vl X} (x: X) n :
    nclosed x n → x.|[to_subst (idsσ n)] = x.
  Proof.
    intro Hcl. rewrite (Hcl _ ids); first by asimpl. by apply idsσ_eq_ids.
  Qed.

  Lemma closed_subst_vl_idsρ v n:
    nclosed_vl v n → v.[to_subst (idsσ n)] = v.
  Proof.
    intro Hcl. rewrite (Hcl _ ids); first by asimpl. by apply idsσ_eq_ids.
  Qed.
End to_subst_idsσ_is_id.

Lemma fv_to_subst `{Ids X} `{HSubst vl X} {hsla: HSubstLemmas vl X} (x: X) σ n:
  nclosed x (length σ) → nclosed_σ σ n →
  nclosed (x.|[to_subst σ]) n.
Proof.
  rewrite /nclosed /nclosed_vl => Hclx Hclρ s1 s2 Heqsn /=; asimpl.
  apply Hclx.
  intros i Hl; asimpl. by eapply (closed_to_subst σ i n).
Qed.

Lemma fv_to_subst_vl v σ n:
  nclosed_vl v (length σ) → nclosed_σ σ n →
  nclosed_vl (v.[to_subst σ]) n.
Proof.
  rewrite /nclosed /nclosed_vl => Hclv Hclσ s1 s2 Heqsn /=; asimpl.
  apply Hclv.
  intros i Hl; asimpl. by eapply (closed_to_subst σ i n).
Qed.

(** Variants of [fv_to_subst] and [fv_to_subst_vl] for more convenient application. *)
Lemma fv_to_subst' `{Ids X} `{HSubst vl X} {hsla: HSubstLemmas vl X} (x: X) x' σ n:
  nclosed x (length σ) → nclosed_σ σ n →
  x' = (x.|[to_subst σ]) →
  nclosed x' n.
Proof. intros; subst. by apply fv_to_subst. Qed.
Lemma fv_to_subst_vl' v σ v' n:
  nclosed_vl v (length σ) → nclosed_σ σ n →
  v' = (v.[to_subst σ]) →
  nclosed_vl v' n.
Proof. intros; subst. by apply fv_to_subst_vl. Qed.

Lemma nclosed_var_lt i n: nclosed_vl (ids i) n -> i < n.
Proof.
  rewrite /nclosed_vl /= => Heq.
  set s0 := fun c m => if (decide (m < n)) then ids 0 else ids c: vl.
  set s1 := s0 1; set s2 := s0 2. subst s0.
  have Heqs: eq_n_s s1 s2 n. by subst s1 s2; move=> ??; case_decide.
  specialize (Heq s1 s2 Heqs); move: Heq {Heqs}; subst s1 s2 => /=. by case_decide.
Qed.

Lemma nclosed_vl_ids_0 n: n > 0 → nclosed_vl (ids 0) n.
Proof. move => Hi s1 s2 /= Heqs. by apply Heqs. Qed.

Lemma nclosed_vl_ids_S i j: nclosed_vl (ids i) j → nclosed_vl (ids (S i)) (S j).
Proof.
  move => /= Hij s1 s2 Heqs. apply: Heqs.
  suff: i < j by lia. by apply nclosed_var_lt.
Qed.

Lemma nclosed_vl_ids i j: i < j → nclosed_vl (ids i) j.
Proof. move => ???? /=; eauto. Qed.

Hint Resolve nclosed_var_lt nclosed_vl_ids_0 nclosed_vl_ids_S nclosed_vl_ids.

Lemma nclosed_vl_ids_equiv i j: nclosed_vl (ids i) j <-> i < j.
Proof. split; eauto. Qed.

Lemma nclosed_ids_rev i j k:
  nclosed_vl (ids i).[ren (+j)] (j + k) → nclosed_vl (ids i) k.
Proof. rewrite /= !nclosed_vl_ids_equiv; lia. Qed.

Lemma lookup_ids_fv {X} {Γ : list X} {i} {T: X}: Γ !! i = Some T → nclosed_vl (ids i) (length Γ).
Proof. move=> ????/=. eauto using lookup_lt_Some. Qed.

(** Not yet used. *)
Lemma eq_n_s_mon n m {s1 s2}: eq_n_s s1 s2 m → n < m → eq_n_s s1 s2 n.
Proof. rewrite /eq_n_s => HsEq Hnm i Hl. apply HsEq; lia. Qed.

Lemma nclosed_mono {X} `{Ids X} `{HSubst vl X} {hsla: HSubstLemmas vl X} (x: X) n m:
  nclosed x n → n < m → nclosed x m.
Proof. move => Hcl Hle s1 s2 Hseq. by eapply Hcl, eq_n_s_mon. Qed.

Lemma fv_vls_cons v vs n: nclosed vs n → nclosed_vl v n → nclosed (v :: vs) n.
Proof. solve_fv_congruence. Qed.

Lemma nclosed_ids i n: nclosed_vl (ids i) (S (i + n)).
Proof. move => /= s1 s2 Heq. apply Heq. lia. Qed.

Lemma nclosed_idsσr n i: nclosed_σ (idsσ n).|[ren (+i)] (i + n).
Proof.
  elim: n i => [|n IHn] i //=.
  constructor; asimpl; [apply nclosed_ids | apply (IHn (S i)) ].
Qed.

Lemma nclosed_idsσ n: nclosed_σ (idsσ n) n.
Proof. move: (nclosed_idsσr n 0) => Hgoal. by asimpl in Hgoal. Qed.
Hint Resolve nclosed_idsσ.

Lemma Forall_to_closed_vls n σ:
  nclosed_σ σ n → nclosed σ n.
Proof.
  elim: σ => [|v σ IHσ] Hcl //=.
  inverse Hcl; apply fv_vls_cons; by [ apply IHσ | ].
Qed.

Lemma closed_vls_to_Forall m σ:
  nclosed σ m -> nclosed_σ σ m.
Proof.
  elim: σ => [|v σ IHσ] Hcl //=.
  constructor. solve_inv_fv_congruence_h Hcl.
  apply IHσ. solve_inv_fv_congruence_h Hcl.
Qed.

Definition cl_ρ_fv: ∀ ρ, cl_ρ ρ → nclosed ρ 0 := Forall_to_closed_vls 0.

Lemma fv_idsσ n: nclosed (idsσ n) n.
Proof. apply Forall_to_closed_vls, nclosed_idsσ. Qed.

Lemma fv_idsσ_alt n: nclosed (idsσ n) n.
Proof.
  rewrite /nclosed. elim: n => [|n] //= IHn s1 s2 Heq. asimpl.
  f_equiv; [| apply IHn; intros]; apply Heq => /=; lia.
Qed.

Lemma to_subst_compose σ σ':
  eq_n_s (to_subst σ.|[σ']) (to_subst σ >> σ') (length σ).
Proof.
  elim: σ => /= [|v σ IHσ] i Hin; first lia; asimpl.
  case: i Hin => [|i] Hin //=.
  apply IHσ. lia.
Qed.

Lemma to_subst_compose_alt σ σ' n:
  n = length σ →
  eq_n_s (to_subst σ.|[σ']) (to_subst σ >> σ') n.
Proof. intros; subst. apply to_subst_compose. Qed.

Lemma subst_compose_x
      `{Ids X} `{HSubst vl X} {hsla: HSubstLemmas vl X} (x: X)
      σ ξ n1 n2 n3:
  nclosed x n1 →
  length σ = n1 → nclosed_σ σ n2 →
  length ξ = n2 → nclosed_σ ξ n3 →
  x.|[to_subst σ.|[to_subst ξ]] = x.|[to_subst σ].|[to_subst ξ].
Proof.
  intros Hclx Hlenσ Hclσ Hlenξ Hclξ. subst.
  asimpl. by apply Hclx, to_subst_compose.
Qed.
Hint Resolve @subst_compose_x.

Lemma subst_compose_idsσ_x
      `{Ids X} `{HSubst vl X} {hsla: HSubstLemmas vl X} (x: X)
      n m ξ:
  nclosed x n →
  nclosed_σ ξ m →
  length ξ = n →
  x.|[to_subst (idsσ n).|[to_subst ξ]] = x.|[to_subst (idsσ n)].|[to_subst ξ].
Proof. intros; eauto. Qed.
Hint Resolve @subst_compose_idsσ_x.



Lemma nclosed_subst `{Ids X} `{HSubst vl X} {hsla: HSubstLemmas vl X} (x: X) v n:
  nclosed x (S n) →
  nclosed_vl v n →
  nclosed x.|[v/] n.
Proof.
  move => Hclx Hclv ?? HsEq /=; asimpl.
  apply Hclx.
  move => [|i] Hin //=; auto with lia.
Qed.

Lemma nclosed_σ_to_subst ξ σ n:
  nclosed_σ ξ (length σ) → nclosed_σ σ n →
  nclosed_σ (ξ.|[to_subst σ]) n.
Proof.
  intros.
  apply closed_vls_to_Forall, fv_to_subst => //. by apply Forall_to_closed_vls.
Qed.
Hint Resolve nclosed_σ_to_subst.

(*
  TODO: part of this code implements a variant of lemmas above, but for
  arbitrary substitutions, not just the ones produced
  by to_subst. Reducing the overlap might be good.
 *)
Set Implicit Arguments.
Definition nclosed_sub n m s :=
  ∀ i, i < n → nclosed_vl (s i) m.
Definition nclosed_ren n m (r: var → var) := nclosed_sub n m (ren r).

Lemma compose_sub_closed s s1 s2 i j:
  nclosed_sub i j s → eq_n_s s1 s2 j → eq_n_s (s >> s1) (s >> s2) i.
Proof. move => /= Hs Heqs n Hxi. exact: Hs. Qed.

Lemma nclosed_ren_shift n m j:
  m >= j + n → nclosed_ren n m (+j).
Proof. move=>???/=; eauto with lia. Qed.
Hint Resolve nclosed_ren_shift.

Lemma nclosed_sub_vl v s i j:
  nclosed_sub i j s →
  nclosed_vl v i → nclosed_vl v.[s] j.
Proof. move => Hcls Hclv s1 s2 Heqs; asimpl. by eapply Hclv, compose_sub_closed. Qed.

Lemma nclosed_sub_x `{Ids X} `{HSubst vl X} {hsla: HSubstLemmas vl X} (x: X) s i j:
  nclosed_sub i j s →
  nclosed x i → nclosed x.|[s] j.
Proof. move => Hcls Hclx s1 s2 Heqs; asimpl. by eapply Hclx, compose_sub_closed. Qed.

Definition nclosed_sub_shift n m j:
  m >= j + n → nclosed_sub n m (ren (+j)).
Proof. exact: nclosed_ren_shift. Qed.
Hint Resolve nclosed_sub_shift.

Lemma nclosed_sub_up i j s:
  nclosed_sub i j s →
  nclosed_sub (S i) (S j) (up s).
Proof.
  move => //= Hs [|x] Hx; asimpl; by eauto using nclosed_sub_vl with lia.
Qed.
Hint Resolve nclosed_sub_up.

Lemma nclosed_ren_up n m r:
  nclosed_ren n m r →
  nclosed_ren (S n) (S m) (upren r).
Proof. move => //= Hr [|i] Hi; asimpl; eauto with lia. Qed.
Hint Resolve nclosed_ren_up.

Lemma nclosed_sub_inv_var n w i j k: j + k <= i →
  nclosed_vl (ids n).[upn j (w .: ids) >> ren (+k)] i →
  nclosed_vl (ids n) (S i).
Proof.
  rewrite /= !nclosed_vl_ids_equiv iter_up.
  case: (lt_dec n j) => [?|Hge]; first lia.
  case Hnj: (n - j) => [|nj]; first lia.
  rewrite nclosed_vl_ids_equiv /=. lia.
Qed.

Lemma nclosed_ren_rev_var i j k n:
  nclosed_vl (ids n).[upn k (ren (+j))] (i + j + k) → nclosed_vl (ids n) (i + k).
Proof.
  rewrite /= iter_up.
  case_match; rewrite /= !nclosed_vl_ids_equiv; omega.
Qed.
