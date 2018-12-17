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

Lemma closed_subst_vl_id v σ: fv_n_vl v 0 → v.[σ] = v.
Proof.
  intro Hcl. rewrite (Hcl σ ids); first by asimpl.
  intros; omega.
Qed.

Lemma closed_to_subst ρ x: cl_ρ ρ → x < length ρ → fv_n_vl (to_subst ρ x) 0.
  elim: ρ x => /= [|v ρ IHρ] [|x] Hcl Hl; asimpl; try omega; inverse Hcl; try by [].
  by apply IHρ; try omega.
Qed.

Lemma fv_to_subst `{ia: Ids A} `{ha: HSubst vl A} `{@HSubstLemmas vl A Ids_vl Subst_vl ia ha} (a: A) ρ:
  fv_n a (length ρ) → cl_ρ ρ →
  fv_n (a.|[to_subst ρ]) 0.
Proof.
  rewrite /fv_n /fv_n_vl => Hcla Hclρ s1 s2 _ /=; asimpl.
  apply Hcla.
  intros x Hl; asimpl; rewrite !(closed_subst_vl_id (to_subst ρ x)); auto using closed_to_subst.
Qed.

Lemma fv_to_subst_vl v ρ:
  fv_n_vl v (length ρ) → cl_ρ ρ →
  fv_n_vl (v.[to_subst ρ]) 0.
Proof.
  rewrite /fv_n /fv_n_vl => Hclv Hclρ s1 s2 _ /=; asimpl.
  apply Hclv.
  intros x Hl; asimpl; rewrite !(closed_subst_vl_id (to_subst ρ x)); auto using closed_to_subst.
Qed.

Lemma fv_tskip e n: fv_n e n → fv_n (tskip e) n.
Proof. rewrite /fv_n /fv_n_vl => * /=; f_equiv; auto. Qed.

Lemma fv_tproj e l n: fv_n e n → fv_n (tproj e l) n.
Proof. rewrite /fv_n /fv_n_vl => * /=; f_equiv; auto. Qed.

Lemma fv_tapp e1 e2 n: fv_n e1 n → fv_n e2 n → fv_n (tapp e1 e2) n.
Proof. rewrite /fv_n /fv_n_vl => * /=; f_equiv; auto. Qed.

Lemma fv_tv v n: fv_n_vl v n → fv_n (tv v) n.
Proof. rewrite /fv_n /fv_n_vl => * /=; f_equiv; auto. Qed.

Implicit Types (T: ty).
Lemma lookup_success Γ x T: Γ !! x = Some T → x < length Γ.
Proof. apply lookup_lt_Some. Qed.

Lemma lookup_fv Γ x T: Γ !! x = Some T → fv_n (tv (var_vl x)) (length Γ).
Proof. rewrite /fv_n /fv_n_vl => * /=; f_equiv; eauto using lookup_success. Qed.
