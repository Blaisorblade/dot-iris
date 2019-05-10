(* So WIPPY I didn't even change the file name. *)
From stdpp Require Import strings.
From D Require Export prelude tactics.
(* Breaks inference of vl in some places... *)
(* Hint Mode HSubst - + : typeclass_instances. *)

Set Primitive Projections.
Class Values (vl: Type) := {
  inh_vl: Inhabited vl;
  ids_vl: Ids vl;
  rename_vl: Rename vl;
  subst_vl: Subst vl;
  subst_lemmas_vl: SubstLemmas vl;
  inj_ids: Inj (=) (=) ids;
}.
Existing Instances inh_vl ids_vl rename_vl subst_vl subst_lemmas_vl.

(* Structure valueT := { *)
(*   value :> Type; *)
(*   values_vl : Values value *)
(* }. *)
(* Existing Instance values_vl. *)

(* XXX This is really non-standard, and that shows in that you need to define these instances using Defined,
because they contain operational type classes!
Worse, these projections add a different way to refer to the same instance;
now Coq must find out that hsubst_vl_s (Sort ?foo) = foo_hsubst, and without canonical structures ?foo
will not be inferred.
*)
Class Sort `{Values vl} (s: Type) := {
  inh_s: Inhabited s;
  ids_s: Ids s;
  rename_s: Rename s;
  hsubst_vl_s: HSubst vl s;
  hsubst_lemmas_vl_s: HSubstLemmas vl s;
}.
Existing Instances inh_s ids_s rename_s hsubst_vl_s hsubst_lemmas_vl_s.

(* Class DLang (vl tm: Type) := { *)
(*   values_vl: Values vl; *)
(*   sort_tm: Sort tm; *)
(* }. *)

(* XXX was Ids_list *)
Instance list_ids {X}: Ids (list X) := λ _, inhabitant.
Instance list_rename `{Rename X} : Rename (list X) :=
  λ sb xs, map (rename sb) xs.

(* Force [vls] to depend on [Values vl]. *)
Definition vls `{Values vl} := list vl.

(** When two substitutions are equivalent up to n. *)
Definition eq_n_s `{Values vl} (s1 s2: var → vl) n := ∀ x, x < n → s1 x = s2 x.
Global Arguments eq_n_s /.

Section vls.
  (* Context {vl: valueT}. *)
  Context `{!Values vl}.
  Implicit Types (v: vl) (vs: vls).

  Global Instance Ids_vls : Ids vls := list_ids.

  Global Instance vls_hsubst : HSubst vl vls :=
    λ (sb : var → vl) (vs : vls), map (subst sb) vs.
  Definition vls_subst_fold (sb : var → vl) (vs : vls) : map (subst sb) vs = hsubst sb vs := eq_refl.
  (* Trying to make this global does not work. *)
  Hint Rewrite @vls_subst_fold : autosubst.

  Global Instance HSubstLemmas_vls : HSubstLemmas vl vls.
  Proof.
    split; trivial; intros; rewrite /hsubst;
      induction s; asimpl; by f_equal.
  Qed.

  (* Instance Sort_vls: Sort vl vls. *)
  Global Instance Sort_vls: Sort vls.
  Proof. esplit; apply _. Defined.

  Definition to_subst (ρ: vls) : var → vl := foldr (λ v s, v .: s) ids ρ.
  Definition subst_sigma (σ: vls) (ρ: vls) := σ.|[to_subst ρ].

  Lemma to_subst_nil: to_subst [] = ids.
  Proof. trivial. Qed.

  Lemma to_subst_cons v ρ : to_subst (v :: ρ) = v .: to_subst ρ.
  Proof. trivial. Qed.
  Hint Rewrite to_subst_nil to_subst_cons : autosubst.

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
End vls.

Print Rewrite HintDb autosubst. (* The hint has disappeared! *)
Global Hint Rewrite @vls_subst_fold : autosubst.
Global Hint Rewrite @to_subst_nil @to_subst_cons : autosubst.
(* (* Print Rewrite HintDb autosubst. *) *)
(* Section test. *)
(*   (* Context {vl: valueT}. *) *)
(*   Context `{!Values vl}. *)
(*   (* Goal True. *) *)
(*   (* Set Typeclasses Debug Verbosity 2. *) *)
(*   (* Set Printing All. *) *)
(*   (* About idsσ. *) *)
(*   (* About hsubst. *) *)
(*   (* About vls_hsubst. *) *)
(*   (* About vls. *) *)
(*   (* About vls_hsubst. *) *)
(* (* Lemma length_idsσr n r: length (@hsubst vl _ _ (ren r) (@idsσ vl _ n) ) = n. *) *)
(* Lemma length_idsσr n r: length (idsσ n).|[ren r] = n. *)
(* Proof. *)
(*   elim : n r => [r | n IHn r] => //. *)
(*   (* Print HintDb typeclass_instances. *) *)
(*   (* Set Typeclasses Debug Verbosity 2. *) *)
(*   asimpl. by rewrite IHn. *)
(* Qed. *)
(* (* Lemma length_idsσr n r: length (@hsubst vl _ _ (ren r) (@idsσ vl Values0 n) ) = n. *) *)
(* End test. *)

Notation cl_ρ ρ := (nclosed_σ ρ 0).

Section sort.
  Context `{!Values vl} `{!Sort X}.

  Implicit Types
         (v: vl) (vs: vls) (x: X).

  Definition nclosed x n :=
    ∀ s1 s2, eq_n_s s1 s2 n → x.|[s1] = x.|[s2].

  Lemma decomp_s x s:
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
  | Hcl: nclosed ?x ?n |- nclosed _ _ => solve_inv_fv_congruence_h Hcl
  | Hcl: nclosed_vl ?v ?n |- nclosed _ _ => solve_inv_fv_congruence_h Hcl
  | Hcl: nclosed ?x ?n |- nclosed_vl _ _ => solve_inv_fv_congruence_h Hcl
  | Hcl: nclosed_vl ?v ?n |- nclosed_vl _ _ => solve_inv_fv_congruence_h Hcl
  end.

Hint Extern 10 => solve_inv_fv_congruence_auto: fv.

(* XXXX rewrite comment *)
(** The following ones are "direct" lemmas: deduce that an expression is closed
    by knowing that its subexpression are closed. *)
(** Automated proof for such lemmas. *)
Ltac solve_fv_congruence :=
  rewrite /nclosed /nclosed_vl => * /=; repeat (f_equiv; try solve [(idtac + asimpl); auto using eq_up]).

(** [Sort X → Sort (list X)]. *)
Section sort_list.
  Context `{!Values vl} `{!Sort X}.
  Implicit Types (v: vl) (vs: vls) (x: X).

  Global Instance list_hsubst `{HSubst vl X}: HSubst vl (list X) := λ sb xs, map (hsubst sb) xs.
  Global Arguments list_hsubst /.

  Definition list_rename_fold `{Rename X} (sb : var → var) (xs : list X) : map (rename sb) xs = rename sb xs := eq_refl.
  Definition list_hsubst_fold sb (xs : list X) : map (hsubst sb) xs = hsubst sb xs := eq_refl.
  Hint Rewrite @list_rename_fold @list_hsubst_fold : autosubst.

  Global Instance HSubstLemmas_list: HSubstLemmas vl (list X).
  Proof.
    split; trivial; intros; rewrite /hsubst;
      induction s; asimpl; by f_equal.
  Qed.

  Global Instance Sort_list_sort: Sort (list X).
  Proof. esplit; apply _. Defined.

  Lemma fv_cons x xs n: nclosed xs n → nclosed x n → nclosed (x :: xs) n.
  Proof. solve_fv_congruence. Qed.
End sort_list.

Section sort_pair_snd.
  Context `{!Values vl} `{!Sort X} `{Inhabited A}.
  Implicit Types (v: vl) (vs: vls) (x: X) (a: A).

  (** [Sort X → Sort (A, X)] *)
  Definition mapsnd `(f: B → C) : A * B → A * C := λ '(a, b), (a, f b).
  Global Instance pair_rename: Rename (A * X) :=
    λ sb, mapsnd (rename sb).
  Global Instance pair_hsubst: HSubst vl (A * X) :=
    λ sb, mapsnd (hsubst sb).
  Global Instance pair_ids: Ids (A * X) := λ n, (inhabitant, ids n).
  Definition pair_rename_fold sb (ax: A * X): mapsnd (rename sb) ax = rename sb ax := eq_refl.
  Definition pair_hsubst_fold sb (ax: A * X) : mapsnd (hsubst sb) ax = hsubst sb ax := eq_refl.

  Global Instance HSubstLemmas_pair: HSubstLemmas vl (A * X).
  Proof.
    split; trivial; intros; rewrite /hsubst /pair_hsubst /mapsnd /=;
      repeat case_match; simplify_eq; asimpl; by [].
  Qed.
  Global Instance Sort_pair_snd: Sort (A * X).
  Proof. esplit; apply _. Defined.

  Lemma fv_pair (a: A) (x: X) n: nclosed x n → nclosed (a, x) n.
  Proof. solve_fv_congruence. Qed.
End sort_pair_snd.
Global Hint Rewrite @pair_rename_fold @pair_hsubst_fold : autosubst.
Global Hint Rewrite @list_rename_fold @list_hsubst_fold : autosubst.
Definition list_rename_fold2 `{!Inhabited A} `{Sort vl X} (sb : var → var) (xs : list X) : map (rename sb) xs = rename sb xs := eq_refl.
Definition list_hsubst_fold2 `{!Inhabited A} `{Sort vl X} sb (xs : list X) : map (hsubst sb) xs = hsubst sb xs := eq_refl.
Global Hint Rewrite @list_rename_fold2 @list_hsubst_fold2 : autosubst.

Print Rewrite HintDb autosubst.
About Sort.
(* Global Instance Sort_list_pair_snd `{!Inhabited A} `{Sort vl X}: Sort (list (A * X)). apply _. Defined. *)
Lemma fv_pair_cons `{!Inhabited A} `{Sort vl X} (a: A) (x: X) xs n: nclosed xs n → nclosed x n → nclosed ((a, x) :: xs) n.
Proof.
(* solve_fv_congruence. *)
(* intros. move=>s1 s2 ?/=. f_equal; asimpl. f_equal. auto.
change (map (hsubst s1) xs) with (hsubst s1 xs).
change (map (hsubst s2) xs) with (hsubst s2 xs).
rewrite (list_hsubst_fold2 s1 xs).
About list_hsubst_fold.
rewrite (list_hsubst_fold s1 xs). eapply H1. f_equal. auto. try by [idtac+asimpl; auto]. Print solve_fv_congruence. Qed. *)
intros. by apply fv_cons, fv_pair. Qed.

(* Print Sort_list_pair_snd. *)
Section sort_list_pair_snd.
  Context `{!Values vl} `{!Sort X} `{Inhabited A}.
  Definition list_pair_rename_fold sb (xs: list (A * X)): map (mapsnd (rename sb)) xs = rename sb xs := eq_refl.
  Definition list_pair_hsubst_fold sb (xs: list (A * X)) : map (mapsnd (hsubst sb)) xs = hsubst sb xs := eq_refl.
  Global Hint Rewrite @list_pair_rename_fold @list_pair_hsubst_fold : autosubst.
  (* Lemma fv_pair_cons2 (a: A) (x: X) xs n: nclosed xs n → nclosed x n → nclosed ((a, x) :: xs) n.
Proof.
solve_fv_congruence. *)


(*
  Global Arguments list_pair_hsubst /.

  Global Instance HSubstLemmas_list_pair: HSubstLemmas vl (list (A * X)).
  Proof.
    split; trivial; intros; rewrite /hsubst /list_pair_hsubst;
      elim: s => [|[l d] xs IHds] //;
      rewrite /= IHds; asimpl; by [].
  Qed. *)
End sort_list_pair_snd.

Arguments vls_hsubst /.

(* TODO Next: provide instances, and move synLemmas in here. *)
Section sort_lemmas.
  Context `{!Values vl} `{!Sort X}.
(*   About idsσ. *)
(*   About ren. *)
(*   Set Typeclasses Debug. *)
(*   (* Check fun n r => length (idsσ n).|[ren r]. = n. *) *)

(* (* Auxiliary lemma for [length_idsσ]. *) *)
(* Instance foo: HSubst vl vls := _. *)
(* Print foo. *)
(* About vls_hsubst. *)
Lemma length_idsσr n r: length (idsσ n).|[ren r] = n.
Proof.
  elim : n r => [r | n IHn r] => //.
  asimpl. by rewrite IHn.
Qed.

Lemma length_idsσ n: length (idsσ n) = n.
Proof. pose proof (length_idsσr n (+0)) as H. asimpl in H. exact H. Qed.
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
  pose proof (rename_to_subst ρ []) as Hr. rewrite app_nil_r in Hr. asimpl in Hr. exact Hr.
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

Lemma closed_subst_id x σ: nclosed x 0 → x.|[σ] = x.
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
  Proof. pose proof (to_subst_map_commute_aux f n x (+0)) as Hr. asimpl in Hr. exact Hr. Qed.

  Lemma idsσ_eq_ids n: eq_n_s (to_subst (idsσ n)) ids n.
  Proof.
    induction n => x Hle. by rewrite to_subst_nil.
    destruct x => //=.
    assert (x < n) as Hle' by auto using lt_S_n.
    by rewrite to_subst_cons /= to_subst_map_commute // IHn // id_subst.
  Qed.

  Lemma closed_subst_idsρ x n :
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

Lemma fv_to_subst x σ n:
  nclosed x (length σ) → nclosed_σ σ n →
  nclosed (x.|[to_subst σ]) n.
Proof.
  rewrite /nclosed /nclosed_vl => Hcla Hclρ s1 s2 Heqsn /=; asimpl.
  apply Hcla.
  intros i Hl; asimpl. by eapply (closed_to_subst σ i n).
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
Lemma fv_to_subst' x σ x' n:
  nclosed x (length σ) → nclosed_σ σ n →
  x' = (x.|[to_subst σ]) →
  nclosed x' n.
Proof. intros; subst. by apply fv_to_subst. Qed.
Lemma fv_to_subst_vl' v σ v' n:
  nclosed_vl v (length σ) → nclosed_σ σ n →
  v' = (v.[to_subst σ]) →
  nclosed_vl v' n.
Proof. intros; subst. by apply fv_to_subst_vl. Qed.

Implicit Types
         (Γ : list X) (ρ : vls).

Lemma lookup_success Γ x T: Γ !! x = Some T → x < length Γ.
Proof. apply lookup_lt_Some. Qed.

(* Lemma lookup_fv Γ x T: Γ !! x = Some T → nclosed (tv (var_vl x)) (length Γ). *)
(* Proof. rewrite /nclosed /nclosed_vl => * /=; f_equiv; eauto using lookup_success. Qed. *)

Lemma lookup_var Γ x T: Γ !! x = Some T → nclosed_vl (ids x) (length Γ).
Proof. rewrite /nclosed /nclosed_vl => *; rewrite !id_subst. eauto using lookup_success. Qed.

Lemma nclosed_var_lt i n: nclosed_vl (ids i) n -> i < n.
Proof.
  rewrite /nclosed_vl /= => Heq.
  set s0 := fun k x => (if (decide (x < n)) then ids 0 else ids k): vl.
  set s1 := s0 1; set s2 := s0 2. subst s0.
  have Heqs: eq_n_s s1 s2 n. by subst s1 s2; move=> ??; case_decide.
  specialize (Heq s1 s2 Heqs); move: Heq {Heqs}; subst s1 s2 => /=.
  rewrite !id_subst. by case_decide => // /inj_ids.
Qed.

Lemma nclosed_vl_ids_0 i: i > 0 → nclosed_vl (ids 0) i.
Proof. move => Hi s1 s2 /= Heqs. rewrite !id_subst. by apply Heqs. Qed.

Lemma nclosed_vl_ids_S i j: nclosed_vl (ids i) j → nclosed_vl (ids (S i)) (S j).
Proof.
  move => /= Hij s1 s2 Heqs. rewrite !id_subst. apply: Heqs.
  suff: i < j by lia. by apply nclosed_var_lt.
Qed.

Lemma nclosed_vl_ids i j: i < j → nclosed_vl (ids i) j.
Proof. move => ????; rewrite !id_subst. eauto. Qed.

Hint Resolve nclosed_var_lt nclosed_vl_ids_0 nclosed_vl_ids_S nclosed_vl_ids.

Lemma nclosed_vl_ids_equiv i j: nclosed_vl (ids i) j <-> i < j.
Proof. split; eauto. Qed.

Lemma nclosed_ids_rev i j x:
  nclosed_vl (ids x).[ren (+j)] (j + i) → nclosed_vl (ids x) i.
Proof. asimpl. rewrite !nclosed_vl_ids_equiv. lia. Qed.

(** Not yet used. *)
Lemma eq_n_s_mon n m {s1 s2}: eq_n_s s1 s2 m → n < m → eq_n_s s1 s2 n.
Proof. rewrite /eq_n_s => HsEq Hnm x Hl. apply HsEq; lia. Qed.

Lemma nclosed_mono x n m: nclosed x n → n < m → nclosed x m.
Proof. move => Hcl Hle s1 s2 Hseq. by eapply Hcl, eq_n_s_mon. Qed.

(* Definition fv_dms_cons : ∀ l d ds n, nclosed ds n → nclosed d n → nclosed ((l, d) :: ds) n := fv_pair_cons. *)

Lemma fv_vls_cons (v:vl) (vs:vls) n: nclosed vs n → nclosed_vl v n → nclosed (v :: vs) n.
Proof. solve_fv_congruence. Qed.

Lemma nclosed_ids x n: nclosed_vl (ids x) (S (x + n)).
Proof. move => /= s1 s2 Heq. rewrite !id_subst. apply Heq. lia. Qed.

Lemma nclosed_idsσr n x: nclosed_σ (idsσ n).|[ren (+x)] (x + n).
Proof.
  elim: n x => [|n IHn] x //=.
  constructor; asimpl; [apply nclosed_ids | apply (IHn (S x)) ].
Qed.

Lemma nclosed_idsσ n: nclosed_σ (idsσ n) n.
Proof. pose proof nclosed_idsσr n 0 as Hr; asimpl in Hr; exact Hr. Qed.
Hint Resolve nclosed_idsσ.

(* Definition nclosed_ds ds n := Forall (λ '(l, d), nclosed d n) ds. *)
(* Global Arguments nclosed_ds /. *)

(* Lemma Forall_to_closed_dms n ds: *)
(*   nclosed_ds ds n → nclosed ds n. *)
(* Proof. *)
(*   elim: ds => [|[l d] ds IHds] Hcl //=. *)
(*   inverse Hcl; apply fv_dms_cons; by [ apply IHds | ]. *)
(* Qed. *)
(* Lemma closed_dms_to_Forall n ds: *)
(*   nclosed ds n → nclosed_ds ds n. *)
(* Proof. *)
(*   elim: ds => [|[l d] ds IHds] Hcl //=. *)
(*   constructor. solve_inv_fv_congruence_h Hcl. *)
(*   apply IHds. solve_inv_fv_congruence_h Hcl. *)
(* Qed. *)

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

Lemma subst_compose_x x σ ξ n1 n2 n3:
  nclosed x n1 →
  length σ = n1 → nclosed_σ σ n2 →
  length ξ = n2 → nclosed_σ ξ n3 →
  x.|[to_subst σ.|[to_subst ξ]] = x.|[to_subst σ].|[to_subst ξ].
Proof.
  intros HclA Hlenσ Hclσ Hlenξ Hclξ.
  asimpl. apply HclA. subst. by apply to_subst_compose.
Qed.
Hint Resolve subst_compose_x.

Lemma subst_compose_idsσ_x x n m ξ:
  nclosed x n →
  nclosed_σ ξ m →
  length ξ = n →
  x.|[to_subst (idsσ n).|[to_subst ξ]] = x.|[to_subst (idsσ n)].|[to_subst ξ].
Proof. intros; eauto. Qed.

(* Lemma nclosed_tskip_i e n i: *)
(*   nclosed e n → *)
(*   nclosed (iterate tskip i e) n. *)
(* Proof. *)
(*   move => Hcl; elim: i => [|i IHi]; rewrite ?iterate_0 ?iterate_S //; solve_fv_congruence. *)
(* Qed. *)

(* Lemma tskip_subst i e s: (iterate tskip i e).|[s] = iterate tskip i e.|[s]. *)
(* Proof. elim: i => [|i IHi]; by rewrite ?iterate_0 ?iterate_S //= IHi. Qed. *)
End sort_lemmas.
Hint Resolve nclosed_var_lt nclosed_vl_ids_0 nclosed_vl_ids_S nclosed_vl_ids.
Hint Resolve nclosed_idsσ @subst_compose_x @subst_compose_idsσ_x.

Section sort_lemmas_2.
  Context `{!Values vl} `{!Sort X}.
  Implicit Types (v: vl) (vs: vls) (x: X).

  Lemma nclosed_σ_to_subst ξ σ n:
    nclosed_σ ξ (length σ) → nclosed_σ σ n →
    nclosed_σ (ξ.|[to_subst σ]) n.
  Proof.
    intros.
    apply closed_vls_to_Forall, fv_to_subst => //. by apply Forall_to_closed_vls.
  Qed.

  Definition nclosed_sub n m s :=
    ∀ i, i < n → nclosed_vl (s i) m.
  Definition nclosed_ren n m (r: var → var) := nclosed_sub n m (ren r).

  Lemma compose_sub_closed s s1 s2 i j:
    nclosed_sub i j s → eq_n_s s1 s2 j → eq_n_s (s >> s1) (s >> s2) i.
  Proof. move => /= Hs Heqs x Hxi. exact: Hs. Qed.

  Lemma nclosed_ren_shift n m j:
    m >= j + n → nclosed_ren n m (+j).
  Proof. move=>???/=; eauto with lia. Qed.
  Hint Resolve nclosed_ren_shift.

  Lemma nclosed_sub_vl v s i j:
    nclosed_sub i j s →
    nclosed_vl v i → nclosed_vl v.[s] j.
  Proof. move => Hcls Hclv s1 s2 Heqs; asimpl. by eapply Hclv, compose_sub_closed. Qed.

  Lemma nclosed_sub_x (x: X) s i j:
    nclosed_sub i j s →
    nclosed x i → nclosed x.|[s] j.
  Proof. move => Hcls Hcla s1 s2 Heqs; asimpl. by eapply Hcla, compose_sub_closed. Qed.

  Lemma nclosed_ren_vl v r i j:
    nclosed_ren i j r →
    nclosed_vl v i → nclosed_vl (rename r v) j.
  Proof. (* asimpl. *)
  rewrite rename_subst. exact: nclosed_sub_vl. Qed.

  Lemma nclosed_sub_up i j s:
    nclosed_sub i j s →
    nclosed_sub (S i) (S j) (up s).
  Proof.
    move => //= Hs [|x] Hx; asimpl. eauto with lia.
    asimpl; rewrite -rename_subst.
    eapply nclosed_ren_vl; by eauto with lia.
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
    asimpl; rewrite /= !nclosed_vl_ids_equiv iter_up.
    case: (lt_dec n j) => [?|Hge]; first lia.
    case: (decide (n = j)) => [->|Hne]; first lia.
    case (n - j) as [|nj] eqn:Hnj; first lia.
    rewrite /= rename_subst !id_subst. (* asimpl loops *)
    rewrite nclosed_vl_ids_equiv /=. lia.
  Qed.

End sort_lemmas_2.
Hint Resolve nclosed_σ_to_subst.


(* (** The following ones are "direct" lemmas: deduce that an expression is closed *)
(*     by knowing that its subexpression are closed. *) *)

(* Lemma fv_tskip e n: nclosed e n → nclosed (tskip e) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_tproj e l n: nclosed e n → nclosed (tproj e l) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_tapp e1 e2 n: nclosed e1 n → nclosed e2 n → nclosed (tapp e1 e2) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_tv v n: nclosed_vl v n → nclosed (tv v) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_vobj ds n: nclosed ds (S n) → nclosed_vl (vobj ds) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_vabs e n: nclosed e (S n) → nclosed_vl (vabs e) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_dvl v n: nclosed_vl v n → nclosed (dvl v) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_dtysyn T n: nclosed T n → nclosed (dtysyn T) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_pv v n: nclosed_vl v n → nclosed (pv v) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_pself p l n: nclosed p n → nclosed (pself p l) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_TAnd T1 T2 n: nclosed T1 n → *)
(*                        nclosed T2 n → *)
(*                        nclosed (TAnd T1 T2) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_TOr T1 T2 n: nclosed T1 n → *)
(*                        nclosed T2 n → *)
(*                        nclosed (TOr T1 T2) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_TMu T1 n: nclosed T1 (S n) → nclosed (TMu T1) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_TLater T n: nclosed T n → nclosed (TLater T) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_TAll T1 T2 n: nclosed T1 n → *)
(*                        nclosed T2 (S n) → *)
(*                        nclosed (TAll T1 T2) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_TVMem l T1 n: nclosed T1 n → *)
(*                        nclosed (TVMem l T1) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_TTMem l T1 T2 n: nclosed T1 n → *)
(*                         nclosed T2 n → *)
(*                         nclosed (TTMem l T1 T2) n. *)
(* Proof. solve_fv_congruence. Qed. *)

(* Lemma fv_TSel p l n: nclosed p n → nclosed (TSel p l) n. *)
(* Proof. solve_fv_congruence. Qed. *)


(* Lemma fv_dtysem σ s n: nclosed_σ σ n → nclosed (dtysem σ s) n. *)
(* Proof. move => /Forall_to_closed_vls. solve_fv_congruence. Qed. *)

(* Lemma fv_dtysem_inv σ s n: nclosed (dtysem σ s) n → nclosed_σ σ n. *)
(* Proof. intro. apply closed_vls_to_Forall. eauto with fv. Qed. *)


(* Lemma fv_tv_inv v n: nclosed (tv v) n → nclosed_vl v n. *)
(* Proof. solve_inv_fv_congruence. Qed. *)

(* Lemma fv_tapp_inv_1 n e1 e2: nclosed (tapp e1 e2) n → nclosed e1 n. *)
(* Proof. solve_inv_fv_congruence. Qed. *)

(* Lemma fv_tapp_inv_2 n e1 e2: nclosed (tapp e1 e2) n → nclosed e2 n. *)
(* Proof. solve_inv_fv_congruence. Qed. *)

(* Lemma fv_tskip_inv t n: nclosed (tskip t) n → nclosed t n. *)
(* Proof. solve_inv_fv_congruence. Qed. *)

(* Lemma fv_vabs_inv e n: nclosed_vl (vabs e) n → nclosed e (S n). *)
(* Proof. solve_inv_fv_congruence. Qed. *)

(* Lemma fv_vobj_inv ds n: nclosed_vl (vobj ds) n → nclosed_ds ds (S n). *)
(* Proof. intro. apply closed_dms_to_Forall. solve_inv_fv_congruence_h H. Qed. *)

(* Lemma fv_pv_inv v n: nclosed (pv v) n → nclosed_vl v n. *)
(* Proof. solve_inv_fv_congruence. Qed. *)

(* Lemma fv_TMu_inv T1 n: nclosed (TMu T1) n → nclosed T1 (S n). *)
(* Proof. solve_inv_fv_congruence. Qed. *)

(* Lemma fv_TAll_inv_1 n T1 T2: nclosed (TAll T1 T2) n → nclosed T1 n. *)
(* Proof. solve_inv_fv_congruence. Qed. *)

(* Lemma fv_TAll_inv_2 n T1 T2: nclosed (TAll T1 T2) n → nclosed T2 (S n). *)
(* Proof. solve_inv_fv_congruence. Qed. *)

(* Lemma fv_TTMem_inv_1 n l T1 T2: nclosed (TTMem l T1 T2) n → nclosed T1 n. *)
(* Proof. solve_inv_fv_congruence. Qed. *)

(* Lemma fv_TTMem_inv_2 n l T1 T2: nclosed (TTMem l T1 T2) n → nclosed T2 n. *)
(* Proof. solve_inv_fv_congruence. Qed. *)

(* Lemma fv_TSel_inv p l n: nclosed (TSel p l) n → nclosed p n. *)
(* Proof. solve_inv_fv_congruence. Qed. *)
