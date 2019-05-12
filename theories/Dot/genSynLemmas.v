(**
Syntax/binding lemmas shared between DSub and Dot. They should be abstracted ideally, if Coq let us.
 *)
From D Require Import tactics.
From D.Dot Require Import syn.

Implicit Types (v: vl) (ρ : vls).
(* Auxiliary lemma for [length_idsσ]. *)
Lemma length_idsσr n r: length (idsσ n).|[ren r] = n.
Proof.
  elim : n r => [r | n IHn r] => //.
  asimpl. by rewrite IHn.
Qed.

Lemma length_idsσ n: length (idsσ n) = n.
Proof. pose proof (length_idsσr n (+0)) as Hr. asimpl in Hr. exact Hr. Qed.
Hint Resolve length_idsσ.

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
  intros; lia.
Qed.

Lemma closed_subst_id `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) σ: nclosed a 0 → a.|[σ] = a.
Proof.
  intro Hcl. rewrite (Hcl σ ids) /=; first by asimpl.
  intros; lia.
Qed.

Lemma closed_to_subst ρ x n: nclosed_σ ρ n → x < length ρ → nclosed_vl (to_subst ρ x) n.
Proof.
  elim: ρ x => /= [|v ρ IHρ] [|x] Hcl Hl; asimpl; try lia; inverse Hcl; try by [].
  by apply IHρ; try lia.
Qed.

(** Let's prove that [nclosed a n → a.|[to_subst (idsσ n)] = a], and ditto for values. *)
Section to_subst_idsσ_is_id.
  Lemma to_subst_map_commute_aux f n x r: x < n → to_subst (map f (idsσ n).|[ren r]) x = f (to_subst (idsσ n).|[ren r] x).
  Proof.
    elim: n r x => [|n IHn] r x Hle; first lia.
    destruct x; first done; asimpl.
    apply IHn; lia.
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

Lemma fv_to_subst `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) σ n:
  nclosed a (length σ) → nclosed_σ σ n →
  nclosed (a.|[to_subst σ]) n.
Proof.
  rewrite /nclosed /nclosed_vl => Hcla Hclρ s1 s2 Heqsn /=; asimpl.
  apply Hcla.
  intros x Hl; asimpl. by eapply (closed_to_subst σ x n).
Qed.

Lemma fv_to_subst_vl v σ n:
  nclosed_vl v (length σ) → nclosed_σ σ n →
  nclosed_vl (v.[to_subst σ]) n.
Proof.
  rewrite /nclosed /nclosed_vl => Hclv Hclσ s1 s2 Heqsn /=; asimpl.
  apply Hclv.
  intros x Hl; asimpl. by eapply (closed_to_subst σ x n).
Qed.

(** Variants of [fv_to_subst] and [fv_to_subst_vl] for more convenient application. *)
Lemma fv_to_subst' `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) σ a' n:
  nclosed a (length σ) → nclosed_σ σ n →
  a' = (a.|[to_subst σ]) →
  nclosed a' n.
Proof. intros; subst. by apply fv_to_subst. Qed.
Lemma fv_to_subst_vl' v σ v' n:
  nclosed_vl v (length σ) → nclosed_σ σ n →
  v' = (v.[to_subst σ]) →
  nclosed_vl v' n.
Proof. intros; subst. by apply fv_to_subst_vl. Qed.

Lemma nclosed_var_lt i n: nclosed_vl (ids i) n -> i < n.
Proof.
  rewrite /nclosed_vl /= => Heq.
  set s0 := fun k x => if (decide (x < n)) then ids 0 else ids k: vl.
  set s1 := s0 1; set s2 := s0 2. subst s0.
  have Heqs: eq_n_s s1 s2 n. by subst s1 s2; move=> ??; case_decide.
  specialize (Heq s1 s2 Heqs); move: Heq {Heqs}; subst s1 s2 => /=. by case_decide.
Qed.

Lemma nclosed_vl_ids_0 i: i > 0 → nclosed_vl (ids 0) i.
Proof. move => Hi s1 s2 /= Heqs. by apply Heqs. Qed.

Lemma nclosed_vl_ids_S i j: nclosed_vl (ids i) j → nclosed_vl (ids (S i)) (S j).
Proof.
  move => /= Hij s1 s2 Heqs. apply: Heqs.
  suff: i < j by lia. by apply nclosed_var_lt.
Qed.

Lemma nclosed_vl_ids i j: i < j → nclosed_vl (ids i) j.
Proof. move => ????/=; eauto. Qed.

Hint Resolve nclosed_var_lt nclosed_vl_ids_0 nclosed_vl_ids_S nclosed_vl_ids.

Lemma nclosed_vl_ids_equiv i j: nclosed_vl (ids i) j <-> i < j.
Proof. split; eauto. Qed.

Lemma nclosed_ids_rev i j x:
  nclosed_vl (ids x).[ren (+j)] (j + i) → nclosed_vl (ids x) i.
Proof. rewrite /= !nclosed_vl_ids_equiv; lia. Qed.

(** Not yet used. *)
Lemma eq_n_s_mon n m {s1 s2}: eq_n_s s1 s2 m → n < m → eq_n_s s1 s2 n.
Proof. rewrite /eq_n_s => HsEq Hnm x Hl. apply HsEq; lia. Qed.

Lemma nclosed_mono {A}  `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) n m:
  nclosed a n → n < m → nclosed a m.
Proof. move => Hcl Hle s1 s2 Hseq. by eapply Hcl, eq_n_s_mon. Qed.

Lemma fv_vls_cons v vs n: nclosed vs n → nclosed_vl v n → nclosed (v :: vs) n.
Proof. solve_fv_congruence. Qed.

Lemma nclosed_ids x n: nclosed_vl (ids x) (S (x + n)).
Proof. move => /= s1 s2 Heq. apply Heq. lia. Qed.

Lemma nclosed_idsσr n x: nclosed_σ (idsσ n).|[ren (+x)] (x + n).
Proof.
  elim: n x => [|n IHn] x //=.
  constructor; asimpl; [apply nclosed_ids | apply (IHn (S x)) ].
Qed.

Lemma nclosed_idsσ n: nclosed_σ (idsσ n) n.
Proof. pose proof nclosed_idsσr n 0 as H; asimpl in H; exact H. Qed.
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
  induction σ as [| v σ] => /= x Hxn; first lia; asimpl.
  destruct x => //=.
  (* elim: σ => /= [|v σ IHσ] x Hxn; first lia; asimpl. *)
  (* case: x Hxn => [|x] Hxn //=. *)
  apply IHσ. lia.
Qed.

Lemma to_subst_compose_alt σ σ' n:
  n = length σ →
  eq_n_s (to_subst σ.|[σ']) (to_subst σ >> σ') n.
Proof. intros; subst. apply to_subst_compose. Qed.

Lemma subst_compose_x
      `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A)
      σ ξ n1 n2 n3:
  nclosed a n1 →
  length σ = n1 → nclosed_σ σ n2 →
  length ξ = n2 → nclosed_σ ξ n3 →
  a.|[to_subst σ.|[to_subst ξ]] = a.|[to_subst σ].|[to_subst ξ].
Proof.
  intros HclA Hlenσ Hclσ Hlenξ Hclξ.
  asimpl. apply HclA. subst. by apply to_subst_compose.
Qed.
Hint Resolve @subst_compose_x.

Lemma subst_compose_idsσ_x
      `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A)
      n m ξ:
  nclosed a n →
  nclosed_σ ξ m →
  length ξ = n →
  a.|[to_subst (idsσ n).|[to_subst ξ]] = a.|[to_subst (idsσ n)].|[to_subst ξ].
Proof. intros; eauto. Qed.
Hint Resolve @subst_compose_idsσ_x.

Lemma nclosed_σ_to_subst ξ σ n:
  nclosed_σ ξ (length σ) → nclosed_σ σ n →
  nclosed_σ (ξ.|[to_subst σ]) n.
Proof.
  intros.
  apply closed_vls_to_Forall, fv_to_subst => //. by apply Forall_to_closed_vls.
Qed.
Hint Resolve nclosed_σ_to_subst.

Lemma lookup_ids_fv {X} {Γ: list X} {x} {T: X}: Γ !! x = Some T → nclosed_vl (ids x) (length Γ).
Proof. move=> ????/=; eauto using lookup_lt_Some. Qed.

Lemma nclosed_subst `{Ids A} `{HSubst vl A} {hsla: HSubstLemmas vl A} (a: A) v n:
  nclosed a (S n) →
  nclosed_vl v n →
  nclosed a.|[v/] n.
Proof.
  move => Hclt1 Hclv ?? HsEq /=; asimpl.
  apply Hclt1.
  move => [|x] Hxn //=; auto with lia.
Qed.
