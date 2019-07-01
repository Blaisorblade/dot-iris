From D Require Import prelude asubst_intf.

Module Type SortsLemmas (Import V : Values) <: SortsIntf.

(** Here, it's important to import [V], not [values].
    When we include [SortsLemmas] in [syn], [V] maps to [syn],
    while [values] is a separate nested module.
    By importing [V], our definitions will mention [vl]
    rather than [values.vl]. *)
Module values := V.

Class Sort (s : Type)
  {inh_s : Inhabited s}
  {ids_s : Ids s} {ren_s : Rename s} {hsubst_vl_s : HSubst vl s}
  {hsubst_lemmas_vl_s : HSubstLemmas vl s} := {}.

Global Instance sort_vls : Sort vls := {}.
Global Instance sort_list `{Sort X} : Sort (list X) := {}.
Global Instance sort_pair_snd `{Sort X} `{Inhabited A} : Sort (A * X) := {}.
Global Instance sort_list_pair_snd `{Sort X} `{Inhabited A} : Sort (list (A * X)) := {}.

Implicit Types (v w : vl) (vs ρ : vls) (i j k n : nat) (r : nat → nat).

Definition eq_n_s (s1 s2 : var → vl) n := ∀ x, x < n → s1 x = s2 x.
Global Arguments eq_n_s /.

Fixpoint to_subst (ρ : vls) : var → vl :=
  match ρ with
  | [] => ids
  | v :: ρ => v .: to_subst ρ
  end.
Definition subst_sigma (σ : vls) (ρ : vls) := σ.|[to_subst ρ].

Lemma to_subst_nil : to_subst [] = ids.
Proof. trivial. Qed.

Lemma to_subst_cons v ρ : to_subst (v :: ρ) = v .: to_subst ρ.
Proof. trivial. Qed.

Definition push_var (σ : vls) : vls := ids 0 :: σ.|[ren (+1)].
Arguments push_var /.

(** Create an identity environment of the given length. *)
Fixpoint idsσ n : vls :=
  match n with
  | 0 => []
  | S n => push_var (idsσ n)
  end.

(** [n]-closedness defines when some AST has at most [n] free variables (from [0] to [n - 1]). *)
(** Here and elsewhere, we give one definition for values, using [subst], and
    another for other ASTs, using [hsubst]. *)
Definition nclosed_vl (v : vl) n :=
  ∀ s1 s2, eq_n_s s1 s2 n → v.[s1] = v.[s2].

Definition nclosed `{HSubst vl X} (x : X) n :=
  ∀ s1 s2, eq_n_s s1 s2 n → x.|[s1] = x.|[s2].

Notation nclosed_σ σ n := (Forall (λ v, nclosed_vl v n) σ).
Notation cl_ρ ρ := (nclosed_σ ρ 0).

(** Infrastructure to prove "direct" lemmas on nclosed{,_vl}: deduce that an expression is closed
    by knowing that its subexpression are closed. *)

(** Needed by solve_fv_congruence when dealing with binders, such as in fv_vobj and fv_vabs. *)
Lemma eq_up s1 s2 n : eq_n_s s1 s2 n → eq_n_s (up s1) (up s2) (S n).
Proof.
  rewrite /up. move => Heq [|x] Hl //=. f_equiv. apply Heq. lia.
Qed.

Global Ltac solve_fv_congruence :=
  rewrite /nclosed /nclosed_vl => * /=; repeat (f_equiv; try solve [(idtac + asimpl); auto using eq_up]).

(** Generic direct lemmas. *)
Lemma fv_cons `{Sort X} (x : X) xs n : nclosed xs n → nclosed x n → nclosed (x :: xs) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_pair `{Sort X} `{Inhabited A} (a : A) (x : X) n : nclosed x n → nclosed (a, x) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_pair_cons `{Sort X} `{!Inhabited A} (a : A) (x : X) xs n : nclosed xs n → nclosed x n → nclosed ((a, x) :: xs) n.
(* solve_fv_congruence would work, but this gives a smaller proof. *)
Proof. intros. by apply fv_cons, fv_pair. Qed.

(** Infrastructure for "inverse" lemmas on nclosed{,_vl}: by knowing that an expression is closed,
    deduce that one of its subexpressions is closed.
    Dealing with binders in nclosed "inverse" lemmas requires more infrastructure than for "direct" lemmas.
    See fv_vabs_inv_manual for an explanation. *)

Definition stail s := ren (+1) >> s.
Definition shead (s : var → vl) := s 0.

Lemma eq_n_s_tails {n s1 s2} : eq_n_s s1 s2 (S n) → eq_n_s (stail s1) (stail s2) n.
Proof.
  move => /= HsEq x Hl.
  rewrite /stail /= !id_subst.
  apply HsEq. lia.
Qed.

Lemma eq_n_s_heads {n s1 s2} : eq_n_s s1 s2 n → n > 0 → shead s1 = shead s2.
Proof. rewrite /shead => /= HsEq. exact: HsEq. Qed.

Lemma decomp_s_vl v s : v.[s] = v.[up (stail s)].[shead s/].
Proof. by rewrite /stail /shead; asimpl. Qed.

Section sort.
  Context `{Sort X}.

  Lemma decomp_s (x : X) s :
    x.|[s] = x.|[up (stail s)].|[shead s/].
  Proof. rewrite /stail /shead. by asimpl. Qed.
End sort.

(** Rewrite thesis with equalities learned from injection, if possible *)
Ltac rewritePremises := let H := fresh "H" in repeat (move => H; rewrite ?H {H}).

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
      rewrite ?(decomp_s _ s1) ?(decomp_s _ s2) ?(decomp_s_vl _ s1) ?(decomp_s_vl _ s2) (eq_n_s_heads HsEq); last lia;
      injection (Hfv _ _ (eq_n_s_tails HsEq)); by rewritePremises ].

Ltac solve_inv_fv_congruence_h Hcl :=
  move: Hcl; solve_inv_fv_congruence.

Ltac solve_inv_fv_congruence_auto :=
  match goal with
  | Hcl : nclosed ?x ?n |- nclosed _ _ => solve_inv_fv_congruence_h Hcl
  | Hcl : nclosed_vl ?v ?n |- nclosed _ _ => solve_inv_fv_congruence_h Hcl
  | Hcl : nclosed ?x ?n |- nclosed_vl _ _ => solve_inv_fv_congruence_h Hcl
  | Hcl : nclosed_vl ?v ?n |- nclosed_vl _ _ => solve_inv_fv_congruence_h Hcl
  end.

Hint Extern 10 => solve_inv_fv_congruence_auto : fv.

Section sort_lemmas.
Context `{_HsX: Sort X}.
Implicit Types (x : X) (Γ : list X).
Set Implicit Arguments.

Definition nclosed_sub n m s :=
  ∀ i, i < n → nclosed_vl (s i) m.
Definition nclosed_ren n m (r: var → var) := nclosed_sub n m (ren r).

Lemma compose_sub_closed s s1 s2 i j :
  nclosed_sub i j s → eq_n_s s1 s2 j → eq_n_s (s >> s1) (s >> s2) i.
Proof. move => /= Hs Heqs n Hxi. exact: Hs. Qed.

Lemma nclosed_sub_app_vl v s i j :
  nclosed_sub i j s →
  nclosed_vl v i → nclosed_vl v.[s] j.
Proof. move => Hcls Hclv s1 s2 Heqs; asimpl. by eapply Hclv, compose_sub_closed. Qed.

Lemma nclosed_sub_app x s i j :
  nclosed_sub i j s →
  nclosed x i → nclosed x.|[s] j.
Proof. move => Hcls Hclx s1 s2 Heqs; asimpl. by eapply Hclx, compose_sub_closed. Qed.

Lemma nclosed_vl_ids i j: i < j → nclosed_vl (ids i) j.
Proof. move => ????; rewrite !id_subst. eauto. Qed.
Hint Resolve nclosed_vl_ids.

Lemma nclosed_var_lt i n: nclosed_vl (ids i) n -> i < n.
Proof.
  move => Heq.
  set s0 := fun c m => if (decide (m < n)) then ids 0 else ids c: vl.
  set s1 := s0 1; set s2 := s0 2.
  have Heqs: eq_n_s s1 s2 n. by subst s0 s1 s2; move=> ??; case_decide.
  move: {Heq Heqs} (Heq s1 s2 Heqs); subst s0 s1 s2 => /=.
  rewrite !id_subst. by case_decide => // /inj_ids.
Qed.

Lemma nclosed_vl_ids_equiv i j: nclosed_vl (ids i) j ↔ i < j.
Proof. split; eauto using nclosed_var_lt. Qed.

Lemma nclosed_vl_ids_S i j: nclosed_vl (ids i) j → nclosed_vl (ids (S i)) (S j).
Proof. rewrite !nclosed_vl_ids_equiv. lia. Qed.
Hint Resolve nclosed_vl_ids_S.

Lemma nclosed_ren_shift n m j:
  m >= j + n → nclosed_ren n m (+j).
Proof. move=>???/=; eauto with lia. Qed.
Hint Resolve nclosed_ren_shift.

Definition nclosed_sub_shift n m j:
  m >= j + n → nclosed_sub n m (ren (+j)).
Proof. exact: nclosed_ren_shift. Qed.
Hint Resolve nclosed_sub_shift.

Lemma nclosed_sub_up i j s:
  nclosed_sub i j s →
  nclosed_sub (S i) (S j) (up s).
Proof.
  move => //= Hs [|x] Hx; asimpl; by eauto using nclosed_sub_app_vl with lia.
Qed.
Hint Resolve nclosed_sub_up.

Lemma nclosed_ren_up n m r:
  nclosed_ren n m r →
  nclosed_ren (S n) (S m) (upren r).
Proof. move => //= Hr [|i] Hi; asimpl; eauto with lia. Qed.
Hint Resolve nclosed_ren_up.

Lemma eq_n_s_total σ: eq_n_s σ ids 0.
Proof. move=>??. lia. Qed.

Lemma closed_subst_vl_id v σ: nclosed_vl v 0 → v.[σ] = v.
Proof. intro Hcl. rewrite (Hcl σ ids (eq_n_s_total σ)). by asimpl. Qed.

Lemma closed_subst_id x σ: nclosed x 0 → x.|[σ] = x.
Proof. intro Hcl. rewrite (Hcl σ ids (eq_n_s_total σ)). by asimpl. Qed.

Lemma nclosed_sub_to_subst j σ: nclosed_σ σ j →
  nclosed_sub (length σ) j (to_subst σ).
Proof.
  move => Hcl i Hle.
  elim: σ i Hcl Hle => /= [|v σ IHσ] [|i] Hcl Hl; asimpl; [lia..| |]; inverse Hcl; first by [].
  by apply IHσ; try lia.
Qed.

Lemma closed_to_subst σ i n: nclosed_σ σ n → i < length σ → nclosed_vl (to_subst σ i) n.
Proof. move =>???. exact: nclosed_sub_to_subst. Qed.

(* Auxiliary lemma for [length_idsσ]. *)
Lemma length_idsσr n r: length (idsσ n).|[ren r] = n.
Proof.
  elim: n r => [r | n IHn r] => //.
  asimpl. by rewrite IHn.
Qed.

Lemma length_idsσ n: length (idsσ n) = n.
Proof. move: (length_idsσr n (+0)) => Hgoal. by asimpl in Hgoal. Qed.
Hint Resolve length_idsσ.

Lemma rename_to_subst ρ1 ρ2 : (+length ρ1) >>> to_subst (ρ1 ++ ρ2) = to_subst ρ2.
Proof. induction ρ1; by asimpl. Qed.

Lemma undo_to_subst ρ : (+length ρ) >>> to_subst ρ = ids.
Proof.
  move: (rename_to_subst ρ []) => Hgoal. by do [rewrite app_nil_r; asimpl] in Hgoal.
Qed.

Lemma to_subst_weaken ρ1 ρ2 ρ3:
  upn (length ρ1) (ren (+length ρ2)) >> to_subst (ρ1 ++ ρ2 ++ ρ3) =
  to_subst (ρ1 ++ ρ3).
Proof. induction ρ1; asimpl; rewrite ?rename_to_subst ? IHρ1 //. Qed.

Lemma to_subst_up ρ1 ρ2 v:
  upn (length ρ1) (v.[ren (+length ρ2)] .: ids) >> to_subst (ρ1 ++ ρ2) =
  to_subst (ρ1 ++ v :: ρ2).
Proof. induction ρ1; asimpl; rewrite ?undo_to_subst ?subst_id ?IHρ1 //. Qed.

(** Let's prove that [nclosed x n → x.|[to_subst (idsσ n)] = x], and ditto for values. *)
Section to_subst_idsσ_is_id.
  Lemma to_subst_map_commute_aux f n i r: i < n →
    to_subst (map f (idsσ n).|[ren r]) i = f (to_subst (idsσ n).|[ren r] i).
  Proof.
    elim: n r i => [|n IHn] r [//|i] Hle; try lia. asimpl. apply: IHn. lia.
  Qed.

  Lemma to_subst_map_commute f n i: i < n → to_subst (map f (idsσ n)) i = f (to_subst (idsσ n) i).
  Proof. move: (@to_subst_map_commute_aux f n i (+0)) => Hgoal. by asimpl in Hgoal. Qed.

  Lemma idsσ_eq_ids n: eq_n_s (to_subst (idsσ n)) ids n.
  Proof.
    elim: n => [|n IHn] [|i] // /lt_S_n Hle.
    rewrite /= to_subst_map_commute // IHn // id_subst //.
  Qed.

  Lemma closed_subst_idsρ x n :
    nclosed x n → x.|[to_subst (idsσ n)] = x.
  Proof. intro Hcl. rewrite (Hcl _ ids (@idsσ_eq_ids n)). by asimpl. Qed.
End to_subst_idsσ_is_id.

Lemma fv_to_subst x σ n:
  nclosed x (length σ) → nclosed_σ σ n →
  nclosed (x.|[to_subst σ]) n.
Proof. eauto using nclosed_sub_app, nclosed_sub_to_subst. Qed.

Lemma fv_to_subst_vl v σ n:
  nclosed_vl v (length σ) → nclosed_σ σ n →
  nclosed_vl (v.[to_subst σ]) n.
Proof. eauto using nclosed_sub_app_vl, nclosed_sub_to_subst. Qed.

Lemma lookup_ids_fv {Γ : list X} {i} {T: X}: Γ !! i = Some T → nclosed_vl (ids i) (length Γ).
Proof. move => ????; rewrite /= !id_subst. eauto using lookup_lt_Some. Qed.

Lemma fv_vls_cons v vs n: nclosed vs n → nclosed_vl v n → nclosed (v :: vs) n.
Proof. solve_fv_congruence. Qed.

Lemma nclosed_idsσr n i: nclosed_σ (idsσ n).|[ren (+i)] (i + n).
Proof.
  elim: n i => [|n IHn] i //=.
  constructor; asimpl; [rewrite nclosed_vl_ids_equiv; lia | apply (IHn (S i)) ].
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

Definition cl_ρ_fv: ∀ ρ, cl_ρ ρ → nclosed ρ 0 := @Forall_to_closed_vls 0.

Lemma fv_cons_inv_head_v v vs n : nclosed (v :: vs) n → nclosed_vl v n.
Proof. solve_inv_fv_congruence. Qed.
Lemma fv_cons_inv_tail_v v vs n : nclosed (v :: vs) n → nclosed vs n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_cons_inv_head x xs n : nclosed (x :: xs) n → nclosed x n.
Proof. solve_inv_fv_congruence. Qed.
Lemma fv_cons_inv_tail x xs n : nclosed (x :: xs) n → nclosed xs n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_cons_inv_v v vs n : nclosed (v :: vs) n → nclosed_vl v n /\ nclosed vs n.
Proof. intros Hcl; split; solve_inv_fv_congruence_h Hcl. Qed.

Lemma fv_cons_inv x xs n : nclosed (x :: xs) n → nclosed x n /\ nclosed xs n.
Proof. intros Hcl; split; solve_inv_fv_congruence_h Hcl. Qed.

Lemma closed_vls_to_Forall m σ: nclosed σ m -> nclosed_σ σ m.
Proof. elim: σ => [//=|v σ IHσ] /fv_cons_inv_v [Hclv Hclσ]. auto. Qed.

Definition nclosed_xs xs n := (Forall (λ x, nclosed x n) xs).
Global Arguments nclosed_xs /.

Lemma Forall_to_closed_xs n xs: nclosed_xs xs n → nclosed xs n.
Proof.
  elim: xs => [|x xs IHds] Hcl //=.
  inverse Hcl; eapply (@fv_cons X); by [ apply IHds | ].
Qed.

Lemma closed_xs_to_Forall n xs: nclosed xs n → nclosed_xs xs n.
Proof. elim: xs => /= [//|x xs IHxs] /fv_cons_inv [Hclx Hclxs]. auto. Qed.

Lemma nclosed_xs_eq_nclosed n xs: nclosed_xs xs n ↔ nclosed xs n.
Proof. split; eauto using Forall_to_closed_xs, closed_xs_to_Forall. Qed.

Lemma to_subst_compose σ σ':
  eq_n_s (to_subst σ.|[σ']) (to_subst σ >> σ') (length σ).
Proof.
  elim: σ => /= [|v σ IHσ] i Hin; first lia; asimpl.
  case: i Hin => [//|i] /lt_S_n Hin /=. exact: IHσ.
Qed.

Lemma subst_compose x σ ξ n1 n2 n3:
  nclosed x n1 →
  length σ = n1 → nclosed_σ σ n2 →
  length ξ = n2 → nclosed_σ ξ n3 →
  x.|[to_subst σ.|[to_subst ξ]] = x.|[to_subst σ].|[to_subst ξ].
Proof.
  intros Hclx ? Hclσ ? Hclξ; subst; asimpl.
  apply Hclx, to_subst_compose.
Qed.
Hint Resolve subst_compose.

Lemma subst_compose_idsσ x n m ξ:
  nclosed x n →
  nclosed_σ ξ m →
  length ξ = n →
  x.|[to_subst (idsσ n).|[to_subst ξ]] = x.|[to_subst (idsσ n)].|[to_subst ξ].
Proof. intros; eauto. Qed.

End sort_lemmas.
Hint Resolve nclosed_vl_ids_S nclosed_vl_ids.
Hint Resolve nclosed_idsσ @subst_compose @subst_compose_idsσ.

Section sort_lemmas_2.
Context `{_HiA: Inhabited A} `{_HsX: Sort X}.
Implicit Types (a : A) (x : X) (Γ : list X) (axs : list (A * X)).

Lemma fv_pair_inv a x n : nclosed (a, x) n → nclosed x n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_cons_pair_inv_head a x xs n : nclosed ((a, x) :: xs) n → nclosed x n.
Proof. move /(@fv_cons_inv_head (A*X)). solve_inv_fv_congruence. Qed.

Lemma fv_cons_pair_inv_tail a x xs n: nclosed ((a, x) :: xs) n → nclosed xs n.
Proof. apply fv_cons_inv_tail. Qed.

Definition nclosed_axs axs n := (Forall (λ '(a, x), nclosed x n) axs).
Global Arguments nclosed_axs /.

Lemma nclosed_axs_to_nclosed_xs n axs: nclosed_axs axs n ↔ nclosed_xs axs n.
Proof. split => ?; decompose_Forall; case_match; [exact: fv_pair | exact: fv_pair_inv]. Qed.

Lemma nclosed_axs_to_nclosed n axs: nclosed_axs axs n ↔ nclosed axs n.
Proof. by rewrite nclosed_axs_to_nclosed_xs nclosed_xs_eq_nclosed. Qed.

Lemma nclosed_subst x v n:
  nclosed x (S n) →
  nclosed_vl v n →
  nclosed x.|[v/] n.
Proof.
  move => Hclx Hclv ?? HsEq. asimpl.
  apply /Hclx => -[|i] Hin //=; auto with lia.
Qed.

Lemma nclosed_σ_to_subst ξ σ n:
  nclosed_σ ξ (length σ) → nclosed_σ σ n →
  nclosed_σ (ξ.|[to_subst σ]) n.
Proof.
  intros.
  apply closed_vls_to_Forall, fv_to_subst => //. exact: Forall_to_closed_vls.
Qed.

Lemma nclosed_sub_inv_var n w i j k: j + k <= i →
  nclosed_vl (ids n).[upn j (w .: ids) >> ren (+k)] i →
  nclosed_vl (ids n) (S i).
Proof.
  rewrite !id_subst /= !nclosed_vl_ids_equiv iter_up.
  case: (lt_dec n j) => [?|Hge]; first lia.
  case Hnj: (n - j) => [|nj]; first lia. asimpl.
  rewrite nclosed_vl_ids_equiv; lia.
Qed.

Lemma nclosed_ren_rev_var i j k n:
  nclosed_vl (ids n).[upn k (ren (+j))] (i + j + k) → nclosed_vl (ids n) (i + k).
Proof.
  rewrite !id_subst iter_up !rename_subst id_subst /=.
  case_match; rewrite /= !nclosed_vl_ids_equiv; omega.
Qed.

End sort_lemmas_2.

Hint Resolve nclosed_σ_to_subst nclosed_ren_shift @nclosed_sub_shift nclosed_ren_up @nclosed_sub_up.

End SortsLemmas.
