From iris.program_logic Require Import language.
From D Require Import prelude asubst_intf.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

Module Type Sorts (Import V : ValuesSig) <: SortsSig V.
Include SortsSig V.
Export asubst_intf.

Lemma iterate_comp {X} (f : X → X) n m x :
  iterate f n (iterate f m x) = iterate f (n + m) x.
Proof.
  by elim: n m => [//|n IHn] m; rewrite iterate_Sr -iterate_S /= -plusnS.
Qed.

Lemma upn_comp n m f : upn n (upn m f) = upn (n + m) f.
Proof. apply iterate_comp. Qed.

Class Sort (s : Type)
  {inh_s : Inhabited s}
  {ids_s : Ids s} {ren_s : Rename s} {hsubst_vl_s : HSubst vl s}
  {hsubst_lemmas_vl_s : HSubstLemmas vl s} := {}.

Global Instance sort_tm : Sort tm := {}.
Global Instance sort_vls : Sort vls := {}.
Global Instance sort_list `{Sort X} : Sort (list X) := {}.
Global Instance sort_pair_snd `{Sort X} `{Inhabited A} : Sort (A * X) := {}.
Global Instance sort_list_pair_snd `{Sort X} `{Inhabited A} : Sort (list (A * X)) := {}.

Implicit Types (v w : vl) (vs σ : vls) (i j k n : nat)
  (r : nat → nat) (ρ : var → vl).

Definition subst_sigma σ vs := σ.|[∞ vs].

Definition eq_n_s ρ1 ρ2 n := ∀ x, x < n → ρ1 x = ρ2 x.
Global Arguments eq_n_s /.

Lemma eq_n_s_symm ρ1 ρ2 n : eq_n_s ρ1 ρ2 n → eq_n_s ρ2 ρ1 n.
Proof. move => Heqs x ?. symmetry. exact: Heqs. Qed.

Lemma eq_n_s_mon n m {s1 s2}: eq_n_s s1 s2 m → n <= m → eq_n_s s1 s2 n.
Proof. rewrite /eq_n_s => HsEq Hnm i Hl. apply HsEq; lia. Qed.

Definition push_var (σ : vls) : vls := ids 0 :: shift σ.
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
  ∀ ρ1 ρ2, eq_n_s ρ1 ρ2 n → v.[ρ1] = v.[ρ2].

Definition nclosed `{HSubst vl X} (x : X) n :=
  ∀ ρ1 ρ2, eq_n_s ρ1 ρ2 n → x.|[ρ1] = x.|[ρ2].

Notation nclosed_σ σ n := (Forall (λ v, nclosed_vl v n) σ).
Notation cl_ρ σ := (nclosed_σ σ 0).

(** Infrastructure to prove "direct" lemmas on nclosed{,_vl}: deduce that an expression is closed
    by knowing that its subexpression are closed. *)

(** Needed by solve_fv_congruence when dealing with binders, such as in fv_vobj and fv_vabs. *)
Lemma eq_up ρ1 ρ2 n : eq_n_s ρ1 ρ2 n → eq_n_s (up ρ1) (up ρ2) (S n).
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

Definition stail ρ := (+1) >>> ρ.
Definition shead ρ := ρ 0.

Lemma shead_eq v ρ: shead (v .: ρ) = v. Proof. done. Qed.
Lemma stail_eq v ρ: stail (v .: ρ) = ρ. Proof. done. Qed.

Lemma eq_n_s_tails {n ρ1 ρ2} : eq_n_s ρ1 ρ2 (S n) → eq_n_s (stail ρ1) (stail ρ2) n.
Proof.
  move => /= HsEq x Hl.
  rewrite /stail /=.
  apply HsEq. lia.
Qed.

Lemma eq_n_s_heads {n ρ1 ρ2} : eq_n_s ρ1 ρ2 n → n > 0 → shead ρ1 = shead ρ2.
Proof. rewrite /shead => /= HsEq. exact: HsEq. Qed.

(* Unused? *)
Lemma eq_cons v sb1 sb2 n : eq_n_s sb1 sb2 n → eq_n_s (v .: sb1) (v .: sb2) (S n).
Proof. move => Heqs [//|x] /lt_S_n /Heqs //. Qed.

(* Reverse-engineered from autosubst output for speed. *)
Lemma scons_up_swap a sb1 sb2 : a .: sb1 >> sb2 = up sb1 >> a .: sb2.
Proof.
  rewrite upX /ren /scomp scons_comp;
    fsimpl; rewrite subst_compX; by fsimpl; rewrite id_scompX id_subst.
Qed.

Lemma up_sub_compose_base ρ v : up ρ >> v .: ids = v .: ρ.
Proof. by rewrite -scons_up_swap /scomp subst_idX. Qed.

Lemma subst_swap_base v ρ : v.[ρ] .: ρ = (v .: ids) >> ρ.
Proof.
  rewrite /scomp scons_comp. (* Actual swap *)
  by rewrite id_scompX. (* Cleanup *)
Qed.

Lemma subst_swap_vl v ρ w : v.[up ρ].[w.[ρ]/] = v.[w/].[ρ].
Proof. by rewrite !subst_comp up_sub_compose_base subst_swap_base. Qed.

Lemma subst_swap `{Sort X} (x: X) ρ v : x.|[up ρ].|[v.[ρ]/] = x.|[v/].|[ρ].
Proof. by rewrite !hsubst_comp up_sub_compose_base subst_swap_base. Qed.

Lemma shift_sub `{Sort X} {x : X} v: (shift x).|[v/] = x.
Proof. autosubst. Qed.

Lemma up_sub_compose_vl ρ v w : v.[up ρ].[w/] = v.[w .: ρ].
Proof. by rewrite subst_comp up_sub_compose_base. Qed.

Lemma decomp_s_vl v s : v.[s] = v.[up (stail s)].[shead s/].
Proof. rewrite /stail /shead up_sub_compose_vl. by fsimpl. Qed.


Lemma up_sub_compose `{Sort X} (x : X) ρ v : x.|[up ρ].|[v/] = x.|[v .: ρ].
Proof. by rewrite hsubst_comp up_sub_compose_base. Qed.

Lemma decomp_s `{Sort X} (x : X) s :
  x.|[s] = x.|[up (stail s)].|[shead s/].
Proof. rewrite /stail /shead up_sub_compose. by fsimpl. Qed.

(** Rewrite thesis with equalities learned from injection, if possible *)
Ltac rewritePremises := let H := fresh "H" in repeat (move => H; rewrite ?H {H}).

(** Finally, a heuristic solver [solve_inv_fv_congruence] to be able to prove
    such lemmas easily, both here and elsewhere. *)

Ltac solve_inv_fv_congruence :=
  let ρ1 := fresh "ρ1" in
  let ρ2 := fresh "ρ2" in
  let HsEq := fresh "HsEq" in
  let Hfv := fresh "Hfv" in
  rewrite /nclosed_vl /nclosed /= => Hfv ρ1 ρ2 HsEq;
(* asimpl is expensive, but sometimes needed when simplification does mistakes.
  It must also be done after injection because it might not rewrite under Hfv's
  binders. *)
  by [ injection (Hfv ρ1 ρ2); trivial; by (idtac + asimpl; rewritePremises; reflexivity) |
      rewrite ?(decomp_s _ ρ1) ?(decomp_s _ ρ2) ?(decomp_s_vl _ ρ1) ?(decomp_s_vl _ ρ2) (eq_n_s_heads HsEq); last lia;
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

Set Implicit Arguments.

Definition nclosed_sub n m s :=
  ∀ i, i < n → nclosed_vl (s i) m.
Definition nclosed_ren n m (r: var → var) := nclosed_sub n m (ren r).

Lemma compose_sub_closed s ρ1 ρ2 i j :
  nclosed_sub i j s → eq_n_s ρ1 ρ2 j → eq_n_s (s >> ρ1) (s >> ρ2) i.
Proof. move => /= Hs Heqs n Hxi. exact: Hs. Qed.

Lemma nclosed_sub_app_vl v s i j :
  nclosed_sub i j s →
  nclosed_vl v i → nclosed_vl v.[s] j.
Proof. move => Hcls Hclv ρ1 ρ2 Heqs; asimpl. by eapply Hclv, compose_sub_closed. Qed.

Lemma nclosed_vl_ids i j: i < j → nclosed_vl (ids i) j.
Proof. move => ????; rewrite !id_subst. eauto. Qed.
Hint Resolve nclosed_vl_ids : core.

Lemma nclosed_var_lt i n: nclosed_vl (ids i) n → i < n.
Proof.
  move => Heq.
  set s0 := fun c m => if (decide (m < n)) then ids 0 else ids c: vl.
  set ρ1 := s0 1; set ρ2 := s0 2.
  have Heqs: eq_n_s ρ1 ρ2 n. by subst s0 ρ1 ρ2; move=> ??; case_decide.
  move: {Heq Heqs} (Heq ρ1 ρ2 Heqs); subst s0 ρ1 ρ2 => /=.
  rewrite !id_subst. by case_decide => // /inj_ids.
Qed.

Lemma nclosed_vl_ids_equiv i j: nclosed_vl (ids i) j ↔ i < j.
Proof. split; eauto using nclosed_var_lt. Qed.

Lemma nclosed_vl_ids_S i j: nclosed_vl (ids i) j → nclosed_vl (ids (S i)) (S j).
Proof. rewrite !nclosed_vl_ids_equiv. lia. Qed.
Hint Resolve nclosed_vl_ids_S : core.

Lemma nclosed_ren_shift n m j:
  m >= j + n → nclosed_ren n m (+j).
Proof. move=>???/=; eauto with lia. Qed.
Hint Resolve nclosed_ren_shift : core.

Definition nclosed_sub_shift n m j:
  m >= j + n → nclosed_sub n m (ren (+j)).
Proof. exact: nclosed_ren_shift. Qed.
Hint Resolve nclosed_sub_shift : core.

Lemma nclosed_sub_up i j s:
  nclosed_sub i j s →
  nclosed_sub (S i) (S j) (up s).
Proof.
  move => //= Hs [|x] Hx; asimpl; by eauto using nclosed_sub_app_vl with lia.
Qed.
Hint Resolve nclosed_sub_up : core.

Lemma nclosed_ren_up n m r:
  nclosed_ren n m r →
  nclosed_ren (S n) (S m) (upren r).
Proof. move => //= Hr [|i] Hi; asimpl; eauto with lia. Qed.
Hint Resolve nclosed_ren_up : core.

Lemma nclosed_sub_base i s : nclosed_sub 0 i s.
Proof. move => j /Nat.nlt_0_r []. Qed.
Hint Resolve nclosed_sub_base : core.

Lemma nclosed_sub_scons_inv i j v s:
  nclosed_sub (S i) j (v .: s) →
  nclosed_vl v j ∧ nclosed_sub i j s.
Proof.
  move => Hcl; split. by eapply (Hcl 0); lia.
  move => k Hle. eapply (Hcl (S k)), lt_n_S, Hle.
Qed.

Lemma nclosed_sub_stail i j v s:
  nclosed_sub (S i) j (v .: s) →
  nclosed_sub i j s.
Proof. move => /nclosed_sub_scons_inv [//]. Qed.

Lemma nclosed_σ_sub_equiv {σ i} : nclosed_σ σ i ↔ nclosed_sub (length σ) i (∞ σ).
Proof.
  split; elim: σ => [//| /= v σ IHσ] Hcl ; [|].
  - inverse Hcl. move => [//|j /lt_S_n] /=. exact: IHσ.
  - constructor. by apply (Hcl 0); lia.
    eapply IHσ, nclosed_sub_stail, Hcl.
Qed.
Hint Resolve -> nclosed_σ_sub_equiv : core.

Lemma eq_n_s_total ρ1 ρ2: eq_n_s ρ1 ρ2 0.
Proof. move => ? /Nat.nlt_0_r []. Qed.
Hint Resolve eq_n_s_total : core.

Lemma closed_subst_vl_id v ρ: nclosed_vl v 0 → v.[ρ] = v.
Proof. intro Hcl. rewrite (Hcl ρ ids) // subst_id //. Qed.

(* Auxiliary lemma for [length_idsσ]. *)
Lemma length_idsσr n r: length (idsσ n).|[ren r] = n.
Proof.
  elim: n r => [r | n IHn r] => //.
  asimpl. by rewrite IHn.
Qed.

Lemma length_idsσ n: length (idsσ n) = n.
Proof. move: (length_idsσr n (+0)) => Hgoal. by asimpl in Hgoal. Qed.
Hint Resolve length_idsσ : core.

Lemma rename_to_subst σ1 σ2 : (+length σ1) >>> ∞ (σ1 ++ σ2) = ∞ σ2.
Proof. induction σ1; by asimpl. Qed.

(* Dead. *)
Lemma undo_to_subst σ : (+length σ) >>> ∞ σ = ids.
Proof.
  move: (rename_to_subst σ []) => Hgoal. by do [rewrite app_nil_r; asimpl] in Hgoal.
Qed.

Lemma to_subst_weaken σ1 σ2 σ3:
  upn (length σ1) (ren (+length σ2)) >> ∞ (σ1 ++ σ2 ++ σ3) =
  ∞ (σ1 ++ σ3).
Proof. induction σ1; asimpl; rewrite ?rename_to_subst ? IHσ1 //. Qed.

(* Dead. *)
Lemma to_subst_up σ1 σ2 v:
  upn (length σ1) (v.[ren (+length σ2)] .: ids) >> ∞ (σ1 ++ σ2) =
  ∞ (σ1 ++ v :: σ2).
Proof. induction σ1; asimpl; rewrite ?undo_to_subst ?subst_id ?IHσ1 //. Qed.

Lemma fv_to_subst_vl v σ n:
  nclosed_vl v (length σ) → nclosed_σ σ n →
  nclosed_vl (v.[∞ σ]) n.
Proof. eauto using nclosed_sub_app_vl. Qed.

(** Let's prove that [nclosed x n → x.|[∞ (idsσ n)] = x], and ditto for values. *)
Section to_subst_idsσ_is_id.
  Lemma to_subst_map_commute_aux f n i r: i < n →
    (∞ (map f (idsσ n).|[ren r])) i = f ((∞ (idsσ n).|[ren r]) i).
  Proof.
    elim: n r i => [|n IHn] r [//|i] Hle; try lia. asimpl. apply: IHn. lia.
  Qed.

  Lemma to_subst_map_commute f n i: i < n → (∞ (map f (idsσ n))) i = f ((∞ (idsσ n)) i).
  Proof. move: (@to_subst_map_commute_aux f n i (+0)) => Hgoal. by asimpl in Hgoal. Qed.

  Lemma idsσ_eq_ids n: eq_n_s (∞ (idsσ n)) ids n.
  Proof.
    elim: n => [|n IHn] [|i] // /lt_S_n Hle.
    rewrite /= to_subst_map_commute // IHn // id_subst //.
  Qed.
End to_subst_idsσ_is_id.

Lemma fv_vls_cons v vs n: nclosed vs n → nclosed_vl v n → nclosed (v :: vs) n.
Proof. solve_fv_congruence. Qed.

Lemma nclosed_idsσr n i: nclosed_σ (shiftN i (idsσ n)) (i + n).
Proof.
  elim: n i => [|n IHn] i //=.
  constructor; asimpl; [rewrite nclosed_vl_ids_equiv; lia | apply (IHn (S i)) ].
Qed.

Lemma nclosed_idsσ n: nclosed_σ (idsσ n) n.
Proof. move: (nclosed_idsσr n 0) => Hgoal. by asimpl in Hgoal. Qed.
Hint Resolve nclosed_idsσ : core.

Lemma Forall_to_closed_vls n σ:
  nclosed_σ σ n → nclosed σ n.
Proof.
  elim: σ => [|v σ IHσ] Hcl //=.
  inverse Hcl; apply fv_vls_cons; by [ apply IHσ | ].
Qed.

Lemma lookup_ids_fv {X} {Γ : list X} {i} {T: X}: Γ !! i = Some T → nclosed_vl (ids i) (length Γ).
Proof. move => ????; rewrite /= !id_subst. eauto using lookup_lt_Some. Qed.

Definition cl_ρ_fv: ∀ σ, cl_ρ σ → nclosed σ 0 := @Forall_to_closed_vls 0.

Lemma to_subst_compose σ ρ:
  eq_n_s (∞ σ.|[ρ]) (∞ σ >> ρ) (length σ).
Proof.
  elim: σ => /= [|v σ IHσ] i Hin; first lia; asimpl.
  case: i Hin => [//|i] /lt_S_n Hin /=. exact: IHσ.
Qed.

Lemma fv_cons_inv_v v vs n : nclosed (v :: vs) n → nclosed_vl v n /\ nclosed vs n.
Proof. intros Hcl; split; solve_inv_fv_congruence_h Hcl. Qed.

Lemma closed_vls_to_Forall m σ: nclosed σ m → nclosed_σ σ m.
Proof. elim: σ => [//=|v σ IHσ] /fv_cons_inv_v [Hclv Hclσ]. auto. Qed.

Lemma iter_up (m x : nat) (f : var → vl) :
  upn m f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
Proof.
  elim: m x => [|m IH] [|x]; case_match => //; asimpl; rewrite // IH;
    case_match; (lia || autosubst).
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
  case_match; rewrite /= !nclosed_vl_ids_equiv; lia.
Qed.

(* Rewrite lemmas to be faster than asimpl: *)
Lemma renS_comp n : ren (+S n) = ren (+n) >> ren (+1).
Proof. rewrite /ren/scomp. fsimpl. by rewrite (id_scompX ((+1) >>> ids)). Qed.

Lemma scompA a b c : a >> b >> c = a >> (b >> c).
Proof. by rewrite /scomp/= -!subst_compX. Qed.

Lemma ren_ren_comp i j : ren (+i) >> ren (+j) = ren (+j + i).
Proof. autosubst. Qed.

Lemma ren_upn_gen i j k : ren (+i + j) >> upn i (ren (+k)) = ren (+i + j + k).
Proof.
  induction k. rewrite up_id_n; autosubst.
  replace (i + j + S k) with (S (i + j + k)) by lia.
  rewrite (renS_comp (i + j + k)) -IHk -ren_ren_comp.
  rewrite !(scompA _ _ (upn _ _)) !up_liftn.
  autosubst.
Qed.

Section sort_lemmas.
Context `{_HsX: Sort X}.
Implicit Types (x : X) (Γ : list X).

Lemma ren_upn i v : v.[ren (+i)].[upn i (ren (+1))] = v.[ren (+S i)].
Proof.
  move: (ren_upn_gen i 0 1). by rewrite plusnS !plusnO subst_comp =>->.
Qed.

Lemma hren_upn i x : x.|[ren (+i)].|[upn i (ren (+1))] = x.|[ren (+S i)].
Proof.
  move: (ren_upn_gen i 0 1). by rewrite plusnS !plusnO hsubst_comp =>->.
Qed.

Lemma hrenS x n : shiftN (S n) x = shift (shiftN n x).
Proof. rewrite hsubst_comp renS_comp. by []. Qed.

Lemma hren_upn_gen i j k x : x.|[ren (+i + j)].|[upn i (ren (+k))] = x.|[ren (+i + j + k)].
Proof. by rewrite !hsubst_comp ren_upn_gen. Qed.

Lemma cons_subst i x s (c : X → X)
  (Hsub: ∀ y, (c y).|[s] = c y.|[s]):
  (iterate c i x).|[s] = iterate c i x.|[s].
Proof. elim: i => [|i IHi]; by rewrite ?iterate_0 ?iterate_S //= Hsub IHi. Qed.

Lemma closed_subst_idsρ x n :
  nclosed x n → x.|[∞ (idsσ n)] = x.
Proof. intro Hcl. rewrite (Hcl _ ids (@idsσ_eq_ids n)). by asimpl. Qed.

Lemma nclosed_sub_app x s i j :
  nclosed_sub i j s →
  nclosed x i → nclosed x.|[s] j.
Proof. move => Hcls Hclx ρ1 ρ2 Heqs; asimpl. by eapply Hclx, compose_sub_closed. Qed.

Lemma closed_subst_id x ρ : nclosed x 0 → x.|[ρ] = x.
Proof. intro Hcl. rewrite (Hcl ρ ids) // hsubst_id //. Qed.

Lemma fv_to_subst x σ n:
  nclosed x (length σ) → nclosed_σ σ n →
  nclosed (x.|[∞ σ]) n.
Proof. eauto using nclosed_sub_app. Qed.

Lemma fv_cons_inv_head_v v vs n : nclosed (v :: vs) n → nclosed_vl v n.
Proof. solve_inv_fv_congruence. Qed.
Lemma fv_cons_inv_tail_v v vs n : nclosed (v :: vs) n → nclosed vs n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_cons_inv_head x xs n : nclosed (x :: xs) n → nclosed x n.
Proof. solve_inv_fv_congruence. Qed.
Lemma fv_cons_inv_tail x xs n : nclosed (x :: xs) n → nclosed xs n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_cons_inv x xs n : nclosed (x :: xs) n → nclosed x n /\ nclosed xs n.
Proof. intros Hcl; split; solve_inv_fv_congruence_h Hcl. Qed.


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

Lemma subst_compose x σ ξ n :
  nclosed x n → length σ = n →
  x.|[∞ σ.|[ξ]] = x.|[∞ σ].|[ξ].
Proof. intros Hclx <-; asimpl. apply Hclx, to_subst_compose. Qed.

Lemma nclosed_mono x n m:
  nclosed x n → n <= m → nclosed x m.
Proof. move => Hcl Hle s1 s2 Hseq. by eapply Hcl, eq_n_s_mon. Qed.

Lemma nclosed_vl_mono v n m:
  nclosed_vl v n → n <= m → nclosed_vl v m.
Proof. move => Hcl Hle s1 s2 Hseq. by eapply Hcl, eq_n_s_mon. Qed.

End sort_lemmas.

Lemma nclosed_σ_mono σ n m :
  nclosed_σ σ n → n <= m → nclosed_σ σ m.
Proof.
  intros; eapply closed_vls_to_Forall, nclosed_mono;
    by [ apply Forall_to_closed_vls |].
Qed.

Lemma nclosed_σ_compose ξ ρ m n:
  nclosed_σ ξ m → nclosed_sub m n ρ →
  nclosed_σ (ξ.|[ρ]) n.
Proof.
  move => Hclξ Hclρ. apply closed_vls_to_Forall, (nclosed_sub_app Hclρ).
  exact: Forall_to_closed_vls.
Qed.

Lemma nclosed_σ_to_subst ξ σ n:
  nclosed_σ ξ (length σ) → nclosed_σ σ n →
  nclosed_σ (ξ.|[∞ σ]) n.
Proof. intros. eapply nclosed_σ_compose; eauto. Qed.
Hint Resolve nclosed_σ_to_subst : core.

Section sort_lemmas_2.
Context `{_HiA: Inhabited A} `{_HsX: Sort X}.
Implicit Types (a : A) (x : X) (Γ : list X) (axs : list (A * X)).

Lemma fv_pair_inv a x n : nclosed (a, x) n → nclosed x n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_cons_pair_inv_head a x xs n : nclosed ((a, x) :: xs) n → nclosed x n.
Proof. move /(@fv_cons_inv_head (A * X)). solve_inv_fv_congruence. Qed.

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
End sort_lemmas_2.

Lemma fv_of_val v n: nclosed_vl v n → nclosed (of_val v) n.
Proof. intros Hclv ρ1 ρ2 Heqs. rewrite !hsubst_of_val. f_equiv. exact: Hclv. Qed.

Lemma fv_of_val_inv v n: nclosed (of_val v) n → nclosed_vl v n.
Proof. intros Hclt ρ1 ρ2 Heqs. apply (inj of_val). rewrite -!hsubst_of_val. exact: Hclt. Qed.

Lemma lookup_fv {X} {Γ : list X} {x} {T : X} : Γ !! x = Some T → nclosed (of_val (ids x : vl)) (length Γ).
Proof. move => /lookup_ids_fv /fv_of_val //. Qed.

Lemma ren_scons v ρ : ren (+1) >> v .: ρ = ρ.
Proof. rewrite /ren/scomp; fsimpl; by rewrite (id_scompX (v .: ρ)). Qed.
End Sorts.

Module Type VlSortsFullSig <: VlSortsSig := ValuesSig <+ Sorts.
