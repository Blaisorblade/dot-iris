From D Require Import prelude.

Module Type Values.
  Parameter vl: Type.
  Definition vls := list vl.
  Declare Instance inh_vl: Inhabited vl.
  Declare Instance ids_vl: Ids vl.
  Declare Instance inj_ids: Inj (=) (=@{vl}) ids.

  Declare Instance rename_vl: Rename vl.
  Declare Instance subst_vl: Subst vl.
  Declare Instance subst_lemmas_vl: SubstLemmas vl.
End Values.

Module Sorts (values: Values).
  Import values.
  Class Sort s := {
    inh_s: Inhabited s;
    ids_s: Ids s;
    ren_s: Rename s;
    hsubst_vl_s: HSubst vl s;
    hsubst_lemmas_vl_s: HSubstLemmas vl s;
  }.
  Global Existing Instances inh_s ids_s ren_s hsubst_vl_s hsubst_lemmas_vl_s.

  (*
    Arguments inh_s: simpl never.
    Arguments ids_s: simpl never.
    Arguments ren_s: simpl never.
    Arguments hsubst_vl_s: simpl never.
    Arguments hsubst_lemmas_vl_s: simpl never. *)

(*
  Class Sort (s: Type)
    {inh_s: Inhabited s}
    {ids_s: Ids s} {ren_s: Rename s} {hsubst_vl_s: HSubst vl s}
    {hsubst_lemmas_vl_s: HSubstLemmas vl s} := {}. *)

  Global Instance sort_vls: Sort vls := {}.
  Global Instance sort_list `{Sort X}: Sort (list X) := {}.
  Global Instance sort_pair_snd `{Sort X} `{Inhabited A}: Sort (A * X) := {}.
  Global Instance sort_list_pair_snd `{Sort X} `{Inhabited A}: Sort (list (A * X)) := {}.

  Implicit Types (v: vl) (vs: vls).

  Definition eq_n_s (s1 s2: var → vl) n := ∀ x, x < n → s1 x = s2 x.
  Global Arguments eq_n_s /.

  Definition to_subst (ρ: vls) : var → vl := foldr (λ v s, v .: s) ids ρ.
  Definition subst_sigma (σ: vls) (ρ: vls) := σ.|[to_subst ρ].

  Lemma to_subst_nil: to_subst [] = ids.
  Proof. trivial. Qed.

  Lemma to_subst_cons v ρ : to_subst (v :: ρ) = v .: to_subst ρ.
  Proof. trivial. Qed.
  Global Hint Rewrite to_subst_nil to_subst_cons : autosubst.

  Global Typeclasses Opaque to_subst.
  Global Opaque to_subst.

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

  Definition nclosed_σ σ n := Forall (λ v, nclosed_vl v n) σ.
  Global Arguments nclosed_σ /.

  (** Needed by solve_fv_congruence when dealing with binders, such as in fv_vobj and fv_vabs. *)
  Lemma eq_up s1 s2 n: eq_n_s s1 s2 n → eq_n_s (up s1) (up s2) (S n).
  Proof.
    rewrite /up. move => Heq [|x] Hl //=. f_equiv. apply Heq. lia.
  Qed.

  Definition stail s := ren (+1) >> s.
  Definition shead (s: var → vl) := s 0.

  Lemma eq_n_s_tails {n s1 s2}: eq_n_s s1 s2 (S n) → eq_n_s (stail s1) (stail s2) n.
  Proof. rewrite /stail => /= HsEq x Hl.
    (* XXX Not needed in syn.v, as id_subst equality holds there definitionally: *)
    (* asimpl. *) rewrite !id_subst.
    apply HsEq. lia. Qed.

  Lemma eq_n_s_heads {n s1 s2}: eq_n_s s1 s2 n → n > 0 → shead s1 = shead s2.
  Proof. rewrite /shead => /= HsEq. apply HsEq. Qed.

  Lemma decomp_s_vl v s:
    v.[s] = v.[up (stail s)].[shead s/].
  Proof. by rewrite /stail /shead; asimpl. Qed.

  Notation cl_ρ ρ := (nclosed_σ ρ 0).

  Section sort.
    Context `{Sort X}.

    Implicit Types (x: X).

    Definition nclosed x n :=
      ∀ s1 s2, eq_n_s s1 s2 n → x.|[s1] = x.|[s2].

    Lemma decomp_s x s:
      x.|[s] = x.|[up (stail s)].|[shead s/].
    Proof. rewrite /stail /shead. by asimpl. Qed.
  End sort.

  (* XXXX rewrite comment *)
  (** The following ones are "direct" lemmas: deduce that an expression is closed
      by knowing that its subexpression are closed. *)
  (** Automated proof for such lemmas. *)
  Global Ltac solve_fv_congruence :=
    rewrite /nclosed /nclosed_vl => * /=; repeat (f_equiv; try solve [(idtac + asimpl); auto using eq_up]).

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
    | Hcl: nclosed ?x ?n |- nclosed _ _ => solve_inv_fv_congruence_h Hcl
    | Hcl: nclosed_vl ?v ?n |- nclosed _ _ => solve_inv_fv_congruence_h Hcl
    | Hcl: nclosed ?x ?n |- nclosed_vl _ _ => solve_inv_fv_congruence_h Hcl
    | Hcl: nclosed_vl ?v ?n |- nclosed_vl _ _ => solve_inv_fv_congruence_h Hcl
    end.

  Hint Extern 10 => solve_inv_fv_congruence_auto: fv.

  Section sort_list.
    Context `{Sort X}.
    Implicit Types (x: X).

    Lemma fv_cons x xs n: nclosed xs n → nclosed x n → nclosed (x :: xs) n.
    Proof. solve_fv_congruence. Qed.

    Context `{Inhabited A}.
    Implicit Types (a: A).

    Lemma fv_pair (a: A) (x: X) n: nclosed x n → nclosed (a, x) n.
    Proof. solve_fv_congruence. Qed.
  End sort_list.

  Lemma fv_pair_cons `{!Inhabited A} `{Sort X} (a: A) (x: X) xs n: nclosed xs n → nclosed x n → nclosed ((a, x) :: xs) n.
  Proof.
    (* solve_fv_congruence. *) (* Works *)
    intros. by apply fv_cons, fv_pair.
  Qed.
  Arguments hsubst_vl_s: simpl never.
End Sorts.
