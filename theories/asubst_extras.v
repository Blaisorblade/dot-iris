From D Require Import prelude.

Class ValueSort (vl: Type)
  {inh_vl: Inhabited vl}
  {ids_vl: Ids vl}
  {inj_ids: Inj (=) (=@{vl}) ids}
  {rename_vl: Rename vl}
  {subst_vl: Subst vl}
  {subst_lemmas_vl: SubstLemmas vl} := {}.

Section Sec.
  Context `{ValueSort vl}.

  Class Sort (s: Type) `{ValueSort vl}
    {inh_s: Inhabited s}
    {ids_s: Ids s} {ren_s: Rename s} {hsubst_vl_s: HSubst vl s}
    {hsubst_lemmas_vl_s: HSubstLemmas vl s} := {}.

  Global Instance sort_vls: Sort (list vl) := {}.
  Global Instance sort_list `{Sort X}: Sort (list X) := {}.
  Global Instance sort_pair_snd `{Sort X} `{Inhabited A}: Sort (A * X) := {}.
  Global Instance sort_list_pair_snd `{Sort X} `{Inhabited A}: Sort (list (A * X)) := {}.

(* Global Instance sort_vls: Sort vl vls := {}.
Global Instance sort_list `{Sort vl X}: Sort vl (list X) := {}.
Global Instance sort_pair_snd `{Sort vl X} `{Inhabited A}: Sort vl (A * X) := {}.
Global Instance sort_list_pair_snd `{Sort vl X} `{Inhabited A}: Sort vl (list (A * X)) := {}. *)
(* Context `{Sort vl X}. *)

End Sec.

Arguments Sort _ _ {_ _ _ _ _ _ _ _ _ _ _ _}.

(* Global Instance sort_vls `{ValueSort vl}: Sort vl (list vl) := {}. *)
(* Global Instance sort_list `{Sort vl X}: Sort vl (list X) := {}. *)
(* Global Instance sort_pair_snd `{Sort vl X} `{Inhabited A}: Sort vl (A * X) := {}.
Global Instance sort_list_pair_snd `{Sort vl X} `{Inhabited A}: Sort vl (list (A * X)) := {}. *)

(* Global Instance sort_list `{Sort X}: Sort (list X) := {}.
Global Instance sort_pair_snd `{Sort X} `{Inhabited A}: Sort (A * X) := {}.
Global Instance sort_list_pair_snd `{Sort X} `{Inhabited A}: Sort (list (A * X)) := {}. *)
(* Context `{Sort vl X}. *)

(** When two substitutions are equivalent up to n. *)
Definition eq_n_s `{ValueSort vl} (s1 s2: var → vl) n := ∀ x, x < n → s1 x = s2 x.
Global Arguments eq_n_s /.
(* Definition eq_n_s (s1 s2: var → vl) n := ∀ x, x < n → s1 x = s2 x.
Arguments eq_n_s /. *)



Section Sec2.
  Context `{ValueSort vl}.
  Notation vls := (list vl).

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

(** [n]-closedness defines when some AST has at most [n] free variables (from [0] to [n - 1]). *)
(** Here and elsewhere, we give one definition for values, using [subst], and
    another for other ASTs, using [hsubst]. *)
Definition nclosed_vl (v: vl) n :=
  ∀ s1 s2, eq_n_s s1 s2 n → v.[s1] = v.[s2].

Definition nclosed `{Sort vl X} (x: X) n :=
  ∀ s1 s2, eq_n_s s1 s2 n → x.|[s1] = x.|[s2].

Context `{Sort vl X}.

Definition nclosed_σ σ n := Forall (λ v, nclosed_vl v n) σ.
Arguments nclosed_σ /.

Notation cl_ρ ρ := (nclosed_σ ρ 0).

(** The following ones are "direct" lemmas: deduce that an expression is closed
    by knowing that its subexpression are closed. *)

(** Needed by solve_fv_congruence when dealing with binders, such as in fv_vobj and fv_vabs. *)
Lemma eq_up (s1 s2: var → vl) n: eq_n_s s1 s2 n → eq_n_s (up s1) (up s2) (S n).
Proof.
  rewrite /up. move => Heq [|x] Hl //=. f_equiv. apply Heq. lia.
Qed.

(** Automated proof for such lemmas. *)
Ltac solve_fv_congruence :=
  rewrite /nclosed /nclosed_vl => * /=; repeat (f_equiv; try solve [(idtac + asimpl); auto using eq_up]).

(** The following ones are "inverse" lemmas: by knowing that an expression is closed,
    deduce that one of its subexpressions is closed *)

(** Dealing with binders in fv "inverse" lemmas requires more infrastructure. See fv_vabs_inv_manual for an explanation. *)

Definition stail s := ren (+1) >> s.
Definition shead (s: var → vl) := s 0.

Lemma eq_n_s_tails {n s1 s2}: eq_n_s s1 s2 (S n) → eq_n_s (stail s1) (stail s2) n.
Proof. rewrite /stail /= => HsEq ??. rewrite !id_subst. apply HsEq. lia. Qed.
Lemma eq_n_s_heads {n s1 s2}: eq_n_s s1 s2 n → n > 0 → shead s1 = shead s2.
Proof. rewrite /shead => /= HsEq. apply HsEq. Qed.

Lemma decomp_s (x: X) (s: var → vl):
  x.|[s] = x.|[up (stail s)].|[shead s/].
Proof. by rewrite /stail /shead; asimpl. Qed.

Lemma decomp_s_vl v s:
  v.[s] = v.[up (stail s)].[shead s/].
Proof. by rewrite /stail /shead; asimpl. Qed.

(** Rewrite thesis with equalities learned from injection, if possible *)
Ltac rewritePremises := let Ht := fresh "H" in repeat (move => Ht; rewrite ?Ht {Ht}).

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

Lemma fv_cons (x: X) (xs: list X) n: nclosed xs n → nclosed x n → nclosed (x :: xs) n.
Proof. solve_fv_congruence. Qed.

Lemma fv_pair_cons `{Inhabited A} (a: A) (x: X) xs n: nclosed xs n → nclosed x n → nclosed ((a, x) :: xs) n.
Proof. solve_fv_congruence. Qed.

End Sec2.
