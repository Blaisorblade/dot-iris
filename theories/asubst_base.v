From D Require Import prelude tactics.
From iris.program_logic Require Import ectxi_language.

Module Type Values.
  Parameter Λ : ectxiLanguage.
  Definition vl : Type := val Λ.
  Definition vls := list vl.
  Declare Instance inh_vl : Inhabited vl.
  Declare Instance ids_vl : Ids vl.
  Declare Instance inj_ids : Inj (=) (=@{vl}) ids.

  Declare Instance rename_vl : Rename vl.
  Declare Instance subst_vl : Subst vl.
  Declare Instance subst_lemmas_vl : SubstLemmas vl.
End Values.

Module Type SortsIntf (values: Values).
  Import values.
  Class Sort (s : Type)
    {inh_s : Inhabited s}
    {ids_s : Ids s} {ren_s : Rename s} {hsubst_vl_s : HSubst vl s}
    {hsubst_lemmas_vl_s : HSubstLemmas vl s} := {}.

End SortsIntf.

Module Sorts (values : Values) <: SortsIntf values.
  Import values.

  Class Sort (s : Type)
    {inh_s : Inhabited s}
    {ids_s : Ids s} {ren_s : Rename s} {hsubst_vl_s : HSubst vl s}
    {hsubst_lemmas_vl_s : HSubstLemmas vl s} := {}.

  Global Instance sort_vls : Sort vls := {}.
  Global Instance sort_list `{Sort X} : Sort (list X) := {}.
  Global Instance sort_pair_snd `{Sort X} `{Inhabited A} : Sort (A * X) := {}.
  Global Instance sort_list_pair_snd `{Sort X} `{Inhabited A} : Sort (list (A * X)) := {}.

  Implicit Types (v : vl) (vs : vls).

  Definition eq_n_s (s1 s2 : var → vl) n := ∀ x, x < n → s1 x = s2 x.
  Global Arguments eq_n_s /.

  Definition to_subst (ρ : vls) : var → vl := foldr (λ v s, v .: s) ids ρ.
  Definition subst_sigma (σ : vls) (ρ : vls) := σ.|[to_subst ρ].

  Lemma to_subst_nil : to_subst [] = ids.
  Proof. trivial. Qed.

  Lemma to_subst_cons v ρ : to_subst (v :: ρ) = v .: to_subst ρ.
  Proof. trivial. Qed.
  Global Hint Rewrite to_subst_nil to_subst_cons : autosubst.

  Global Typeclasses Opaque to_subst.
  Global Opaque to_subst.

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

  Definition nclosed_σ σ n := Forall (λ v, nclosed_vl v n) σ.
  Global Arguments nclosed_σ /.

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

  Notation cl_ρ ρ := (nclosed_σ ρ 0).

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
End Sorts.

From D Require Import tactics locAsimpl swap_later_impl proofmode_extra.
(* From D.pure_program_logic Require Import lifting. *)
From iris.base_logic Require Import lib.iprop.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import language ectxi_language ectx_language.
From D.pure_program_logic Require Import lifting adequacy.
From D Require Export gen_iheap saved_interp.
Require Import Program.

Module LiftWp (values: Values) (sorts: SortsIntf values).
  Import values sorts.
  (* Module M := Sorts sorts.
  Export M. *)
  Implicit Types (v: vl) (ρ vs : vls).
  Implicit Types (Σ : gFunctors).

  Notation envD Σ := (vls -c> vl -c> iProp Σ).
  Instance Inhϕ: Inhabited (envD Σ).
  Proof. constructor. exact (λ _ _, False)%I. Qed.

  Class TyInterp ty Σ := TyInterpG {
    ty_interp: ty -> vls -> vl -> iProp Σ
  }.

  Module GenWp.
  Class dlangG Σ := DLangG {
    dlangG_savior :> savedInterpG Σ vls vl;
    dlangG_interpNames : gen_iheapG stamp gname Σ;
  }.

  Instance dlangG_irisG `{dlangG Σ} : irisG Λ Σ := {
    state_interp σ κs _ := True%I;
    fork_post _ := True%I;
  }.

  (* Defining this needs the above irisG instance in scope. *)
  Definition test_interp_expr `{dlangG Σ} :=
    λ (t: expr Λ), WP t {{ v, False }} %I.

  Notation "s ↦ γ" := (mapsto (hG := dlangG_interpNames) s γ)  (at level 20) : bi_scope.
  Notation "s ↝ φ" := (∃ γ, s ↦ γ ∗ γ ⤇ φ)%I  (at level 20) : bi_scope.

  Section mapsto.
    Context `{!dlangG Σ}.
    Global Instance: Persistent (s ↦ γ).
    Proof. apply _. Qed.
    Global Instance: Timeless (s ↦ γ).
    Proof. apply _. Qed.

    Definition allGs gs := (gen_iheap_ctx (hG := dlangG_interpNames) gs).
    Global Arguments allGs /.

    Lemma leadsto_agree s (φ1 φ2: envD Σ) ρ v: s ↝ φ1 -∗ s ↝ φ2 -∗ ▷ (φ1 ρ v ≡ φ2 ρ v).
    Proof.
      iIntros "/= #H1 #H2".
      iDestruct "H1" as (γ1) "[Hs1 Hg1]".
      iDestruct "H2" as (γ2) "[Hs2 Hg2]".
      iDestruct (mapsto_agree with "Hs1 Hs2") as %->.
      by iApply (saved_interp_agree _ φ1 φ2).
    Qed.
  End mapsto.

  Module dlang_adequacy.
    Class dlangPreG Σ := DLangPreG {
      dlangPreG_savior :> savedInterpG Σ vls vl;
      dlangPreG_interpNames : gen_iheapPreG stamp gname Σ;
    }.
    Definition dlangΣ := #[savedInterpΣ vls vl; gen_iheapΣ stamp gname].

    Instance subG_dlangΣ {Σ} : subG dlangΣ Σ → dlangPreG Σ.
    Proof. solve_inG. Qed.

    (* XXX WP here resolves the wrong way, so this theorem can't be used to actually prove adequacy :-(((. *)
    Theorem adequacy Σ `{Sort (expr Λ)} `{HdlangG: dlangPreG Σ} `{SwapProp (iPropSI Σ)} e e' thp σ σ' Φ:
      (forall `{dlangG Σ} `{SwapProp (iPropSI Σ)}, allGs ∅ ⊢ |==> □ WP e.|[ ids ] {{ Φ }} ) →
      rtc erased_step ([e], σ) (thp, σ') → e' ∈ thp →
      is_Some (to_val e') ∨ reducible e' σ'.
    Proof.
      intros Hlog ??. cut (adequate NotStuck e σ (λ _ _, True)); first (move => [] /= _ ?; by eauto).
      eapply (wp_adequacy Σ) => /=.
      iMod (gen_iheap_init (hG := dlangPreG_interpNames) ∅) as (g) "Hgs".
      set (DLangΣ := DLangG Σ _ g).
      iMod (Hlog DLangΣ with "Hgs") as "#Hlog".
      iIntros (?) "!>". iExists (λ _ _, True%I); iSplit=> //.
      rewrite hsubst_id.
      iApply wp_wand; by [iApply "Hlog" | auto].
    Qed.
    Instance CmraSwappable_dlang: CmraSwappable (iResUR dlangΣ).
    Proof.
      apply Swappable_iResUR.
      rewrite /gid; repeat (dependent destruction i; cbn; try apply _).
    Qed.
  End dlang_adequacy.
  End GenWp.
End LiftWp.

(** Syntax/binding lemmas shared between DSub and Dot. *)

Module SortsLemmas (values: Values).
Import values.
Module M := Sorts values.
Export M.
Module N := LiftWp values M.
Export N.

Implicit Types (v w : vl) (ρ : vls) (i j k n : nat) (r : nat → nat).

Section sort_lemmas.
Context `{_HsX: Sort X}.
Implicit Types (x : X) (Γ : list X).

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

Lemma closed_subst_id x σ: nclosed x 0 → x.|[σ] = x.
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
Lemma fv_to_subst' x x' σ n:
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
  specialize (Heq s1 s2 Heqs); move: Heq {Heqs}; subst s1 s2 => /=.
  rewrite !id_subst. by case_decide => // /inj_ids.
Qed.

Lemma nclosed_vl_ids_0 n: n > 0 → nclosed_vl (ids 0) n.
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

Lemma nclosed_ids_rev i j k:
  nclosed_vl (ids i).[ren (+j)] (j + k) → nclosed_vl (ids i) k.
Proof. rewrite !id_subst /ren /= !nclosed_vl_ids_equiv. lia. Qed.

Lemma lookup_ids_fv {Γ : list X} {i} {T: X}: Γ !! i = Some T → nclosed_vl (ids i) (length Γ).
Proof. move => ????; rewrite /= !id_subst. eauto using lookup_lt_Some. Qed.

(** Not yet used. *)
Lemma eq_n_s_mon n m {s1 s2}: eq_n_s s1 s2 m → n < m → eq_n_s s1 s2 n.
Proof. rewrite /eq_n_s => HsEq Hnm i Hl. apply HsEq; lia. Qed.

Lemma nclosed_mono x n m:
  nclosed x n → n < m → nclosed x m.
Proof. move => Hcl Hle s1 s2 Hseq. by eapply Hcl, eq_n_s_mon. Qed.

Lemma fv_vls_cons v vs n: nclosed vs n → nclosed_vl v n → nclosed (v :: vs) n.
Proof. solve_fv_congruence. Qed.

Lemma nclosed_ids i n: nclosed_vl (ids i) (S (i + n)).
Proof. move => /= s1 s2 Heq. rewrite !id_subst. apply Heq. lia. Qed.

Lemma nclosed_idsσr n i: nclosed_σ (idsσ n).|[ren (+i)] (i + n).
Proof.
  elim: n i => [|n IHn] i //=.
  constructor; asimpl; [apply nclosed_ids | apply (IHn (S i)) ].
Qed.

Lemma nclosed_idsσ n: nclosed_σ (idsσ n) n.
Proof. move: (nclosed_idsσr n 0) => Hgoal. by asimpl in Hgoal. Qed.
Hint Resolve nclosed_idsσ.

(* Definition fv_dms_cons : ∀ l d ds n, nclosed ds n → nclosed d n → nclosed ((l, d) :: ds) n := fv_pair_cons. *)

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
  elim: σ => /= [|v σ IHσ] i Hin; first lia; asimpl.
  case: i Hin => [|i] Hin //=.
  apply IHσ. lia.
Qed.

Lemma to_subst_compose_alt σ σ' n:
  n = length σ →
  eq_n_s (to_subst σ.|[σ']) (to_subst σ >> σ') n.
Proof. intros; subst. apply to_subst_compose. Qed.

Lemma subst_compose x σ ξ n1 n2 n3:
  nclosed x n1 →
  length σ = n1 → nclosed_σ σ n2 →
  length ξ = n2 → nclosed_σ ξ n3 →
  x.|[to_subst σ.|[to_subst ξ]] = x.|[to_subst σ].|[to_subst ξ].
Proof.
  intros Hclx Hlenσ Hclσ Hlenξ Hclξ. subst.
  asimpl. by apply Hclx, to_subst_compose.
Qed.
Hint Resolve subst_compose.

Lemma subst_compose_idsσ x n m ξ:
  nclosed x n →
  nclosed_σ ξ m →
  length ξ = n →
  x.|[to_subst (idsσ n).|[to_subst ξ]] = x.|[to_subst (idsσ n)].|[to_subst ξ].
Proof. intros; eauto. Qed.

End sort_lemmas.
Hint Resolve nclosed_var_lt nclosed_vl_ids_0 nclosed_vl_ids_S nclosed_vl_ids.
Hint Resolve nclosed_idsσ @subst_compose @subst_compose_idsσ.

Section sort_lemmas_2.
Context `{_HsX: Sort X}.
Implicit Types (x : X) (Γ : list X).

Lemma nclosed_subst x v n:
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

Lemma nclosed_sub_app_vl v s i j:
  nclosed_sub i j s →
  nclosed_vl v i → nclosed_vl v.[s] j.
Proof. move => Hcls Hclv s1 s2 Heqs; asimpl. by eapply Hclv, compose_sub_closed. Qed.

Lemma nclosed_sub_app x s i j:
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
  move => //= Hs [|x] Hx; asimpl; by eauto using nclosed_sub_app_vl with lia.
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
  rewrite !id_subst /= !nclosed_vl_ids_equiv iter_up.
  case: (lt_dec n j) => [?|Hge]; first lia.
  case Hnj: (n - j) => [|nj]; first lia.
  rewrite rename_subst !id_subst.
  rewrite nclosed_vl_ids_equiv /=. lia.
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
