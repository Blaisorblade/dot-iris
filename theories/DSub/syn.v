From D.DSub Require Export dsub_syn.

(** After instantiating Autosubst, a few binding-related syntactic definitions
    that need not their own file. *)

Definition to_subst (ρ: vls) : var → vl := foldr (λ v s, v .: s) ids ρ.

Lemma to_subst_nil: to_subst [] = ids.
Proof. trivial. Qed.

Lemma to_subst_cons v ρ : to_subst (v :: ρ) = v .: to_subst ρ.
Proof. trivial. Qed.
Hint Rewrite to_subst_nil to_subst_cons : autosubst.

Global Typeclasses Opaque to_subst.
Global Opaque to_subst.

Definition subst_sigma (σ: vls) (ρ: vls) := σ.|[to_subst ρ].

Definition push_var (σ: vls) : vls := ids 0 :: σ.|[ren (+1)].
Arguments push_var /.

(** Create an identity environment of the given length. *)
Fixpoint idsσ n: vls :=
  match n with
  | 0 => []
  | S n => push_var (idsσ n)
  end.

(** When two substitutions are equivalent up to n. *)
Definition eq_n_s (s1 s2: var → vl) n := ∀ x, x < n → s1 x = s2 x.
Arguments eq_n_s /.

(** [n]-closedness defines when some AST has at most [n] free variables (from [0] to [n - 1]). *)
(** Here and elsewhere, we give one definition for values, using [subst], and
    another for other ASTs, using [hsubst]. *)
Definition nclosed_vl (v: vl) n :=
  ∀ s1 s2, eq_n_s s1 s2 n → v.[s1] = v.[s2].

Definition nclosed `{HSubst vl X} (t: X) n :=
  ∀ s1 s2, eq_n_s s1 s2 n → t.|[s1] = t.|[s2].

Definition nclosed_σ σ n := Forall (λ v, nclosed_vl v n) σ.
Arguments nclosed_σ /.

Notation cl_ρ ρ := (nclosed_σ ρ 0).

(** The following ones are "direct" lemmas: deduce that an expression is closed
    by knowing that its subexpression are closed. *)

(** Needed by solve_fv_congruence when dealing with binders, such as in fv_vobj and fv_vabs. *)
Lemma eq_up s1 s2 n: eq_n_s s1 s2 n → eq_n_s (up s1) (up s2) (S n).
Proof.
  rewrite /up. move => Heq [|x] Hl //=. f_equiv. apply Heq. lia.
Qed.

(** Automated proof for such lemmas. *)
Ltac solve_fv_congruence :=
  rewrite /nclosed /nclosed_vl => * /=; repeat (f_equiv; try solve [(idtac + asimpl); auto using eq_up]).

Lemma fv_cons `{Ids X} `{HSubst vl X} {hsla: HSubstLemmas vl X} (x: X) xs n: nclosed xs n → nclosed x n → nclosed (x :: xs) n.
Proof. solve_fv_congruence. Qed.

(** The following ones are "inverse" lemmas: by knowing that an expression is closed,
    deduce that one of its subexpressions is closed *)

(** Dealing with binders in fv "inverse" lemmas requires more infrastructure. See fv_vabs_inv_manual for an explanation. *)

Definition stail s := ren (+1) >> s.
Definition shead (s: var → vl) := s 0.

Lemma eq_n_s_tails {n s1 s2}: eq_n_s s1 s2 (S n) → eq_n_s (stail s1) (stail s2) n.
Proof. rewrite /stail => /= HsEq x Hl. apply HsEq. lia. Qed.
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
  rewrite ?(decomp_s _ s1) ?(decomp_s _ s2) ?(decomp_s_vl _ s1) ?(decomp_s_vl _ s2) (eq_n_s_heads HsEq); last lia.
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
       rewrite ?(decomp_s _ s1) ?(decomp_s _ s2) ?(decomp_s_vl _ s1) ?(decomp_s_vl _ s2) (eq_n_s_heads HsEq); last lia;
       injection (Hfv _ _ (eq_n_s_tails HsEq)); by rewritePremises ].

Ltac solve_inv_fv_congruence_h Hcl :=
  move: Hcl; solve_inv_fv_congruence.

Ltac solve_inv_fv_congruence_auto :=
  match goal with
  | Hcl: nclosed ?t ?n |- nclosed _ _ => solve_inv_fv_congruence_h Hcl
  | Hcl: nclosed_vl ?t ?n |- nclosed _ _ => solve_inv_fv_congruence_h Hcl
  | Hcl: nclosed ?t ?n |- nclosed_vl _ _ => solve_inv_fv_congruence_h Hcl
  | Hcl: nclosed_vl ?t ?n |- nclosed_vl _ _ => solve_inv_fv_congruence_h Hcl
  end.

Hint Extern 10 => solve_inv_fv_congruence_auto: fv.

Section syntax_mut_ind_closed.
  Variable Ptm : tm → nat → Prop.
  Variable Pvl : vl → nat → Prop.
  Variable Pty : ty → nat → Prop.

  Implicit Types (n: nat).

  Variable step_tv : ∀ n v1,
      nclosed_vl v1 n → nclosed (tv v1) n → Pvl v1 n → Ptm (tv v1) n.
  Variable step_tapp : ∀ n t1 t2,
      nclosed t1 n → nclosed t2 n → nclosed (tapp t1 t2) n →
      Ptm t1 n → Ptm t2 n → Ptm (tapp t1 t2) n.
  Variable step_tskip : ∀ n t1,
      nclosed t1 n → nclosed (tskip t1) n →
      Ptm t1 n → Ptm (tskip t1) n.
  Variable step_var_vl : ∀ n i,
      nclosed_vl (var_vl i) n → Pvl (var_vl i) n.
  Variable step_vnat : ∀ n m,
      nclosed_vl (vnat m) n → Pvl (vnat m) n.
  Variable step_vabs : ∀ n t1,
      nclosed t1 (S n) →
      nclosed_vl (vabs t1) n →
      Ptm t1 (S n) → Pvl (vabs t1) n.

  Variable step_vty : ∀ n T1,
      nclosed T1 n → nclosed_vl (vty T1) n →
      Pty T1 n → Pvl (vty T1) n.
  (** Beware here in Prop we use Forall, not ForallT! *)
  Variable step_vstamp : ∀ n vs s,
      nclosed vs n → nclosed_vl (vstamp vs s) n →
      Forall (flip Pvl n) vs → Pvl (vstamp vs s) n.
  Variable step_TTop : ∀ n,
      nclosed TTop n →
      Pty TTop n.
  Variable step_TBot : ∀ n,
      nclosed TBot n →
      Pty TBot n.
  Variable step_TLater : ∀ n T1,
      nclosed T1 n → nclosed (TLater T1) n →
      Pty T1 n → Pty (TLater T1) n.
  Variable step_TAll : ∀ n T1 T2,
      nclosed T1 n → nclosed T2 (S n) → nclosed (TAll T1 T2) n →
      Pty T1 n → Pty T2 (S n) → Pty (TAll T1 T2) n.
  Variable step_TTMem : ∀ n T1 T2,
      nclosed T1 n → nclosed T2 n → nclosed (TTMem T1 T2) n →
      Pty T1 n → Pty T2 n → Pty (TTMem T1 T2) n.
  Variable step_TSel : ∀ n v1,
      nclosed_vl v1 n → nclosed (TSel v1) n →
      Pvl v1 n → Pty (TSel v1) n.
  Variable step_TNat : ∀ n,
      nclosed TNat n →
      Pty TNat n.

  Fixpoint nclosed_tm_mut_ind n t: nclosed t n → Ptm t n
  with     nclosed_vl_mut_ind n v: nclosed_vl v n → Pvl v n
  with     nclosed_ty_mut_ind n T: nclosed T n → Pty T n.
  Proof.
    (* Automation risk producing circular proofs that call right away the lemma we're proving.
       Instead we want to apply one of the [case_] arguments to perform an
       inductive step, and only then call ourselves recursively. *)
    all: destruct 0; intro Hcl.
    all: let byEapply p := efeed p using (fun q => apply q) by (eauto 2; eauto 1 with fv)
    in
      match goal with
      (* Warning: add other arities as needed. *)
      | Hstep: context [?P (?c _ _ _) _] |- ?P (?c ?a1 ?a2 ?a3) _ => byEapply (Hstep n a1 a2 a3)
      | Hstep: context [?P (?c _ _) _] |- ?P (?c ?a1 ?a2) _ => byEapply (Hstep n a1 a2)
      | Hstep: context [?P (?c _) _] |- ?P (?c ?a1) _ => byEapply (Hstep n a1)
      | Hstep: context [?P (?c) _] |- ?P (?c) _ => byEapply (Hstep n)
      end.
    - induction l as [| a l]; constructor => /=; eauto 2 with fv.
  Qed.

  Lemma nclosed_syntax_mut_ind: (∀ t n, nclosed t n → Ptm t n) ∧ (∀ v n, nclosed_vl v n → Pvl v n) ∧ (∀ T n, nclosed T n → Pty T n).
  Proof.
    repeat split; intros.
    - exact: nclosed_tm_mut_ind.
    - exact: nclosed_vl_mut_ind.
    - exact: nclosed_ty_mut_ind.
  Qed.
End syntax_mut_ind_closed.
