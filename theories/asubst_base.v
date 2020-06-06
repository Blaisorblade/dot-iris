(** * Substitution lemmas for languages implementing [ValuesSig]. *)
From iris.program_logic Require Import language.
From D Require Import prelude asubst_intf.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

(** The module type [Sorts] is a "mixin module" that is included directly in
each language implementing [ValuesSig],
*)
Module Type Sorts (Import V : ValuesSig) <: SortsSig V.
Include SortsSig V.

(** We export [ASubstLangDefUtils] even tho these mostly should be internals
to language definitions, as sometimes later proofs refer to
[ASubstLangDefUtils]'s contents. *)
Export ASubstLangDefUtils.

Lemma iterate_comp {X} (f : X → X) n m x :
  iterate f n (iterate f m x) = iterate f (n + m) x.
Proof.
  by elim: n m => [//|n IHn] m; rewrite iterate_Sr -iterate_S /= -plusnS.
Qed.

Lemma upn_comp n m f : upn n (upn m f) = upn (n + m) f.
Proof. apply iterate_comp. Qed.

Global Instance sort_tm : Sort tm := {}.
Global Instance sort_vls : Sort vls := {}.
Global Instance sort_list `{Sort X} : Sort (list X) := {}.
Global Instance sort_pair_snd `{Sort X} `{Inhabited A} : Sort (A * X) := {}.
Global Instance sort_list_pair_snd `{Sort X} `{Inhabited A} : Sort (list (A * X)) := {}.

Implicit Types (v w : vl) (vs σ : vls) (i j k n : nat)
  (r : nat → nat) (ρ : var → vl).

Definition subst_sigma σ vs := σ.|[∞ vs].

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

(** Infrastructure to prove "direct" lemmas on [nclosed{,_vl}]: deduce that an expression is closed
    by knowing that its subexpression are closed. *)

(** Needed by [solve_fv_congruence] when dealing with binders, such as in [fv_vobj] and [fv_vabs]. *)
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

(** Infrastructure for "inverse" lemmas on [nclosed{,_vl}]: by knowing that an expression is closed,
    deduce that one of its subexpressions is closed.
    Dealing with binders in nclosed "inverse" lemmas requires more infrastructure than for "direct" lemmas.
    See [fv_vabs_inv_manual] for an explanation. *)

Lemma eq_n_s_tails {n ρ1 ρ2} : eq_n_s ρ1 ρ2 (S n) → eq_n_s (stail ρ1) (stail ρ2) n.
Proof.
  move => /= HsEq x Hl.
  rewrite /stail /=.
  apply HsEq. lia.
Qed.

Lemma eq_n_s_heads {n ρ1 ρ2} : eq_n_s ρ1 ρ2 n → n > 0 → shead ρ1 = shead ρ2.
Proof. rewrite /shead => /= HsEq. exact: HsEq. Qed.

Lemma eq_cons v sb1 sb2 n : eq_n_s sb1 sb2 n → eq_n_s (v .: sb1) (v .: sb2) (S n).
Proof. move => Heqs [//|x] /lt_S_n /Heqs //. Qed.

Lemma up_sub_compose_base ρ v : up ρ >> v .: ids = v .: ρ.
Proof. by rewrite -scons_up_swap /scomp subst_idX. Qed.

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

Set Implicit Arguments.

Lemma nclosed_vl_ids i j: i < j → nclosed_vl (ids i) j.
Proof. move => ????; rewrite !id_subst. eauto. Qed.

Lemma nclosed_var_lt i n: nclosed_vl (ids i) n → i < n.
Proof.
  move => Heq.
  set s0 := fun c m => if (decide (m < n)) then ids 0 else ids c: vl.
  set ρ1 := s0 1; set ρ2 := s0 2.
  have Heqs: eq_n_s ρ1 ρ2 n. by subst s0 ρ1 ρ2; move=> ??; case_decide.
  move: {Heq Heqs} (Heq ρ1 ρ2 Heqs); subst s0 ρ1 ρ2 => /=.
  rewrite !id_subst. by case_decide => // /inj_ids.
Qed.

Lemma eq_n_s_total ρ1 ρ2: eq_n_s ρ1 ρ2 0.
Proof. move => ? /Nat.nlt_0_r []. Qed.

(* Auxiliary lemma for [length_idsσ]. *)
Lemma length_idsσr n r: length (idsσ n).|[ren r] = n.
Proof.
  elim: n r => [r | n IHn r] => //.
  asimpl. by rewrite IHn.
Qed.

Lemma length_idsσ n: length (idsσ n) = n.
Proof. move: (length_idsσr n (+0)) => Hgoal. by asimpl in Hgoal. Qed.

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

Lemma iter_up (m x : nat) (f : var → vl) :
  upn m f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
Proof.
  elim: m x => [|m IH] [|x]; case_match => //; asimpl; rewrite // IH;
    case_match; (lia || autosubst).
Qed.

(* Rewrite lemmas to be faster than asimpl: *)
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

Lemma subst_swap_vl v ρ w : v.[up ρ].[w.[ρ]/] = v.[w/].[ρ].
Proof. by rewrite !subst_comp up_sub_compose_base subst_swap_base. Qed.

Lemma subst_swap (x: X) ρ v : x.|[up ρ].|[v.[ρ]/] = x.|[v/].|[ρ].
Proof. by rewrite !hsubst_comp up_sub_compose_base subst_swap_base. Qed.

Lemma ren_upn i v : v.[ren (+i)].[upn i (ren (+1))] = v.[ren (+S i)].
Proof.
  move: (ren_upn_gen i 0 1). by rewrite plusnS !plusnO subst_comp =>->.
Qed.

Lemma hren_upn i x : x.|[ren (+i)].|[upn i (ren (+1))] = x.|[ren (+S i)].
Proof.
  move: (ren_upn_gen i 0 1). by rewrite plusnS !plusnO hsubst_comp =>->.
Qed.

Lemma hren_upn_gen i j k x : x.|[ren (+i + j)].|[upn i (ren (+k))] = x.|[ren (+i + j + k)].
Proof. by rewrite !hsubst_comp ren_upn_gen. Qed.

Lemma cons_subst i x s (c : X → X)
  (Hsub: ∀ y, (c y).|[s] = c y.|[s]):
  (iterate c i x).|[s] = iterate c i x.|[s].
Proof. elim: i => [|i IHi]; by rewrite ?iterate_0 ?iterate_S //= Hsub IHi. Qed.

Lemma closed_subst_idsρ x n :
  nclosed x n → x.|[∞ (idsσ n)] = x.
Proof. intro Hcl. rewrite (Hcl _ ids (@idsσ_eq_ids n)). by asimpl. Qed.

Lemma closed_subst_id x ρ : nclosed x 0 → x.|[ρ] = x.
Proof. intro Hcl. rewrite (Hcl ρ ids) ?hsubst_id //. exact: eq_n_s_total. Qed.

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

End sort_lemmas.

Section sort_lemmas_2.
Context `{_HiA: Inhabited A} `{_HsX: Sort X}.
Implicit Types (a : A) (x : X) (Γ : list X) (axs : list (A * X)).

Lemma fv_pair_inv a x n : nclosed (a, x) n → nclosed x n.
Proof. solve_inv_fv_congruence. Qed.

Definition nclosed_axs axs n := (Forall (λ '(a, x), nclosed x n) axs).
Global Arguments nclosed_axs /.

Lemma nclosed_axs_to_nclosed_xs n axs: nclosed_axs axs n ↔ nclosed_xs axs n.
Proof. split => ?; decompose_Forall; case_match; [exact: fv_pair | exact: fv_pair_inv]. Qed.

Lemma nclosed_axs_to_nclosed n axs: nclosed_axs axs n ↔ nclosed axs n.
Proof. by rewrite nclosed_axs_to_nclosed_xs nclosed_xs_eq_nclosed. Qed.

Lemma ren_scons v ρ : ren (+1) >> v .: ρ = ρ.
Proof. rewrite /ren/scomp; fsimpl; by rewrite (id_scompX (v .: ρ)). Qed.
End sort_lemmas_2.
End Sorts.

Module Type VlSortsFullSig <: VlSortsSig := ValuesSig <+ Sorts.
