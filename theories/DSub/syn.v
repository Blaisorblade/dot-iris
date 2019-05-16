From D Require Export prelude tactics.

Definition stamp := positive.

Inductive tm  : Type :=
  | tv : vl -> tm
  | tapp : tm -> tm -> tm
  | tskip : tm -> tm
 with vl  : Type :=
  | var_vl : var -> vl
  | vnat : nat -> vl
  | vabs : tm -> vl
  | vty : ty -> vl
  | vstamp: list vl -> stamp -> vl
 with ty  : Type :=
  | TTop :  ty
  | TBot :  ty
  (* | TAnd : ty -> ty -> ty *)
  (* | TOr : ty -> ty -> ty *)
  | TLater : ty -> ty
  | TAll : ty -> ty -> ty
  (* | TMu : ty -> ty *)
  | TTMem : ty -> ty -> ty
  | TSel : vl -> ty
  | TNat :  ty.

(** Induction principles for syntax. *)

(* Explore builtin induction principles to generate a good one. *)
(* Module Coq_IndPrinciples_Bad. *)
(*   Scheme vl_badmut := Induction for vl Sort Prop *)
(*   with   tm_badmut := Induction for tm Sort Prop *)
(*   with   ty_badmut := Induction for ty Sort Prop . *)
(*   Scheme vl_badmutt := Induction for vl Sort Type *)
(*   with   tm_badmutt := Induction for tm Sort Type *)
(*   with   ty_badmutt := Induction for ty Sort Type. *)
(*   Combined Scheme syntax_badmutind from vl_badmut, tm_badmut, ty_badmut. *)
(*   Combined Scheme syntax_badmutindt from vl_badmut, tm_badmutt, ty_badmut. *)
(* End Coq_IndPrinciples_Bad. *)

(* Using a Section is a trick taken from CPDT, but there bodies are hand-written.
   The rest is written by taking Coq's generated recursion principles and doing
   lots of regexp search-n-replace.
 *)

Section syntax_mut_rect.
  Variable Ptm : tm → Type.
  Variable Pvl : vl → Type.
  Variable Pty : ty → Type.

  Implicit Types (T: ty) (v: vl) (t: tm).

  Variable step_tv : ∀ v1, Pvl v1 → Ptm (tv v1).
  Variable step_tapp : ∀ t1 t2, Ptm t1 → Ptm t2 → Ptm (tapp t1 t2).
  Variable step_tskip : ∀ t1, Ptm t1 → Ptm (tskip t1).
  Variable step_var_vl : ∀ i, Pvl (var_vl i).
  Variable step_vnat : ∀ n, Pvl (vnat n).
  Variable step_vabs : ∀ t1, Ptm t1 → Pvl (vabs t1).
  Variable step_vty : ∀ T1, Pty T1 → Pvl (vty T1).
  Variable step_vstamp : ∀ vs s, ForallT Pvl vs → Pvl (vstamp vs s).
  Variable step_TTop : Pty TTop.
  Variable step_TBot : Pty TBot.
  Variable step_TLater : ∀ T1, Pty T1 → Pty (TLater T1).
  Variable step_TALl : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TAll T1 T2).
  Variable step_TTMem : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TTMem T1 T2).
  Variable step_TSel : ∀ v1, Pvl v1 → Pty (TSel v1).
  Variable step_TNat : Pty TNat.

  Fixpoint tm_mut_rect t: Ptm t
  with vl_mut_rect v: Pvl v
  with ty_mut_rect T: Pty T.
  Proof.
    (* Automation risk producing circular proofs that call right away the lemma we're proving.
       Instead we want to apply one of the [case_] arguments to perform an
       inductive step, and only then call ourselves recursively. *)
    all: destruct 0;
      match goal with
      (* Warning: add other arities as needed. *)
      | Hstep: context [?P (?c _ _ _)] |- ?P (?c _ _ _) => apply Hstep; trivial
      | Hstep: context [?P (?c _ _)] |- ?P (?c _ _) => apply Hstep; trivial
      | Hstep: context [?P (?c _)] |- ?P (?c _) => apply Hstep; trivial
      | Hstep: context [?P (?c)] |- ?P (?c) => apply Hstep; trivial
      end.
    induction l; auto.
  Qed.

  Lemma syntax_mut_rect: (∀ t, Ptm t) * (∀ v, Pvl v) * (∀ T, Pty T).
  Proof.
    repeat split; intros.
    - eapply tm_mut_rect.
    - eapply vl_mut_rect.
    - eapply ty_mut_rect.
  Qed.
End syntax_mut_rect.

Section syntax_mut_ind.
  Variable Ptm : tm → Prop.
  Variable Pvl : vl → Prop.
  Variable Pty : ty → Prop.

  Implicit Types (T: ty) (v: vl) (t: tm).

  Variable step_tv : ∀ v1, Pvl v1 → Ptm (tv v1).
  Variable step_tapp : ∀ t1 t2, Ptm t1 → Ptm t2 → Ptm (tapp t1 t2).
  Variable step_tskip : ∀ t1, Ptm t1 → Ptm (tskip t1).
  Variable step_var_vl : ∀ i, Pvl (var_vl i).
  Variable step_vnat : ∀ n, Pvl (vnat n).
  Variable step_vabs : ∀ t1, Ptm t1 → Pvl (vabs t1).
  Variable step_vty : ∀ T1, Pty T1 → Pvl (vty T1).
  (** Beware here in Prop we use Forall, not ForallT! *)
  Variable step_vstamp : ∀ vs s, Forall Pvl vs → Pvl (vstamp vs s).
  Variable step_TTop : Pty TTop.
  Variable step_TBot : Pty TBot.
  Variable step_TLater : ∀ T1, Pty T1 → Pty (TLater T1).
  Variable step_TALl : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TAll T1 T2).
  Variable step_TTMem : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TTMem T1 T2).
  Variable step_TSel : ∀ v1, Pvl v1 → Pty (TSel v1).
  Variable step_TNat : Pty TNat.

  Lemma syntax_mut_ind: (∀ t, Ptm t) ∧ (∀ v, Pvl v) ∧ (∀ T, Pty T).
  Proof.
    efeed pose proof syntax_mut_rect as H; try done.
    - intros vs g HvsT. apply step_vstamp, ForallT_Forall, HvsT.
    - ev; split_and! ; assumption.
  Qed.
End syntax_mut_ind.

Definition vls := list vl.
Definition ctx := list ty.

Implicit Types
         (L T U: ty) (v: vl) (e: tm)
         (Γ : ctx).

Instance Inh_ty : Inhabited ty := populate TNat.
Instance Inh_vl : Inhabited vl := populate (vnat 0).
Instance Inh_tm : Inhabited tm := populate (tv inhabitant).

Instance Ids_vl : Ids vl.
Proof. by constructor. Defined.

Instance Ids_tm : Ids tm := λ _, inhabitant.
Instance Ids_ty : Ids ty := λ _, inhabitant.
Instance Ids_list {A}: Ids (list A) := λ _, inhabitant.
Instance Ids_vls : Ids vls := _.
Instance Ids_ctx : Ids ctx := _.

Instance list_rename `{Rename X} : Rename (list X) :=
  λ (sb : var → var) xs, map (rename sb) xs.

Fixpoint tm_rename (sb : var → var) (e : tm) {struct e} : tm :=
  let a := tm_rename : Rename tm in
  let b := vl_rename : Rename vl in
  match e with
  | tv v => tv (rename sb v)
  | tapp t1 t2 => tapp (rename sb t1) (rename sb t2)
  | tskip t => tskip (rename sb t)
  end
with
vl_rename (sb : var → var) (v : vl) {struct v} : vl :=
  let a := tm_rename : Rename tm in
  let b := vl_rename : Rename vl in
  let c := ty_rename : Rename ty in
  match v with
  | var_vl x => var_vl (sb x)
  | vnat n => vnat n
  | vabs t => vabs (rename (upren sb) t)
  | vty T => vty (rename sb T)
  | vstamp vs s => vstamp (rename sb vs) s
  end
with
ty_rename (sb : var → var) (T : ty) {struct T}: ty :=
  let a := ty_rename : Rename ty in
  let b := vl_rename : Rename vl in
  match T with
  | TTop => TTop
  | TBot => TBot
  (* | TAnd T1 T2 => TAnd (rename sb T1) (rename sb T2) *)
  (* | TOr T1 T2 => TOr (rename sb T1) (rename sb T2) *)
  | TLater T => TLater (rename sb T)
  | TAll T1 T2 => TAll (rename sb T1) (rename (upren sb) T2)
  (* | TMu T => TMu (rename (upren sb) T) *)
  | TTMem T1 T2 => TTMem (rename sb T1) (rename sb T2)
  | TSel v => TSel (rename sb v)
  | TNat => TNat
  end.

Instance Rename_tm : Rename tm := tm_rename.
Instance Rename_vl : Rename vl := vl_rename.
Instance Rename_ty : Rename ty := ty_rename.

Definition list_rename_fold `{Rename X} (sb : var → var) (xs : list X) : map (rename sb) xs = rename sb xs := eq_refl.

Definition vls_rename_fold: ∀ sb vs, map (rename sb) vs = rename sb vs := list_rename_fold.

Hint Rewrite @list_rename_fold : autosubst.

Instance vls_hsubst `{Subst vl} : HSubst vl vls :=
  λ (sb : var → vl) (vs : vls), map (subst sb) vs.

Instance list_hsubst `{HSubst vl X}: HSubst vl (list X) := λ sb xs, map (hsubst sb) xs.

Fixpoint tm_hsubst (sb : var → vl) (e : tm) : tm :=
  let a := tm_hsubst : HSubst vl tm in
  let b := vl_subst : Subst vl in
  match e with
  | tv v => tv (subst sb v)
  | tapp t1 t2 => tapp (hsubst sb t1) (hsubst sb t2)
  | tskip t => tskip (hsubst sb t)
  end
with
vl_subst (sb : var → vl) (v : vl) : vl :=
  let a := tm_hsubst : HSubst vl tm in
  let b := vl_subst : Subst vl in
  let c := ty_hsubst : HSubst vl ty in
  match v with
  | var_vl x => sb x
  | vnat n => vnat n
  | vabs t => vabs (hsubst (up sb) t)
  | vty T => vty (hsubst sb T)
  | vstamp vs s => vstamp (hsubst sb vs) s
  end
with
ty_hsubst (sb : var → vl) (T : ty) : ty :=
  let a := ty_hsubst : HSubst vl ty in
  let b := vl_subst : Subst vl in
  match T with
  | TTop => TTop
  | TBot => TBot
  (* | TAnd T1 T2 => TAnd (hsubst sb T1) (hsubst sb T2) *)
  (* | TOr T1 T2 => TOr (hsubst sb T1) (hsubst sb T2) *)
  | TLater T => TLater (hsubst sb T)
  | TAll T1 T2 => TAll (hsubst sb T1) (hsubst (up sb) T2)
  (* | TMu T => TMu (hsubst (up sb) T) *)
  | TTMem T1 T2 => TTMem (hsubst sb T1) (hsubst sb T2)
  | TSel v => TSel (subst sb v)
  | TNat => TNat
  end.

Instance Subst_vl : Subst vl := vl_subst.
Instance HSubst_tm : HSubst vl tm := tm_hsubst.
Instance HSubst_ty : HSubst vl ty := ty_hsubst.

(* Now type inference solves HSubst vl ? by infering HSubst vl ty infers unspecified asts to be [ty]s. *)
(* Goal ∀ s x, x.|[s] = x. *)
(* Abort. *)
Hint Mode HSubst - + : typeclass_instances.
(* That Hint stops that. *)
(* Fail Goal ∀ s x, x.|[s] = x. *)
(* Goal ∀ s (x: ty) , x.|[s] = x. Abort. *)

Definition vls_subst_fold (sb : var → vl) (vs : vls) : map (subst sb) vs = hsubst sb vs := eq_refl.
Definition list_hsubst_fold `{HSubst vl X} sb (xs : list X) : map (hsubst sb) xs = hsubst sb xs := eq_refl.

Hint Rewrite vls_subst_fold @list_hsubst_fold : autosubst.

Arguments vls_hsubst /.
Arguments list_hsubst /.

Lemma vl_eq_dec (v1 v2 : vl) : Decision (v1 = v2)
with
tm_eq_dec (t1 t2 : tm) : Decision (t1 = t2)
with
ty_eq_dec (ty1 ty2 : ty) : Decision (ty1 = ty2).
Proof.
   all: rewrite /Decision; decide equality;
       try (apply vl_eq_dec || apply tm_eq_dec || apply ty_eq_dec ||
            apply @list_eq_dec ||
            apply nat_eq_dec || apply positive_eq_dec); auto.
Qed.

Instance vl_eq_dec' : EqDecision vl := vl_eq_dec.
Instance tm_eq_dec' : EqDecision tm := tm_eq_dec.
Instance ty_eq_dec' : EqDecision ty := ty_eq_dec.
Instance vls_eq_dec' : EqDecision vls := list_eq_dec.

Local Ltac finish_lists l x :=
  elim: l => [|x xs IHds] //=; by f_equal.

Lemma vl_rename_Lemma (ξ : var → var) (v : vl) : rename ξ v = v.[ren ξ]
with
tm_rename_Lemma (ξ : var → var) (t : tm) : rename ξ t = t.|[ren ξ]
with
ty_rename_Lemma (ξ : var → var) (T : ty) : rename ξ T = T.|[ren ξ].
Proof.
  all: destruct 0; rewrite /= ?up_upren_internal; f_equal => //; finish_lists l x.
Qed.

Lemma vl_ids_Lemma (v : vl) : v.[ids] = v
with
tm_ids_Lemma (t : tm) : t.|[ids] = t
with
ty_ids_Lemma (T : ty) : T.|[ids] = T.
Proof.
  all: destruct 0; rewrite /= ?up_id_internal; f_equal => //; finish_lists l x.
Qed.

Lemma vl_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (v : vl) :
  (rename ξ v).[σ] = v.[ξ >>> σ]
with
tm_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (t : tm) :
  (rename ξ t).|[σ] = t.|[ξ >>> σ]
with
ty_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (T : ty) :
  (rename ξ T).|[σ] = T.|[ξ >>> σ].
Proof.
  all: destruct 0; rewrite /= 1? up_comp_ren_subst; f_equal => //; finish_lists l x.
Qed.

Lemma vl_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (v : vl) :
  rename ξ v.[σ] = v.[σ >>> rename ξ]
with
tm_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (t : tm) :
  rename ξ t.|[σ] = t.|[σ >>> rename ξ]
with
ty_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (T : ty) :
  rename ξ T.|[σ] = T.|[σ >>> rename ξ].
Proof.
  all: destruct 0; rewrite /= ? up_comp_subst_ren_internal; f_equal => //;
    auto using vl_rename_Lemma, vl_comp_rename_Lemma; finish_lists l x.
Qed.

Lemma vl_comp_Lemma (σ τ : var → vl) (v : vl) : v.[σ].[τ] = v.[σ >> τ]
with
tm_comp_Lemma (σ τ : var → vl) (t : tm) : t.|[σ].|[τ] = t.|[σ >> τ]
with
ty_comp_Lemma (σ τ : var → vl) (T : ty) : T.|[σ].|[τ] = T.|[σ >> τ].
Proof.
  all: destruct 0; rewrite /= ? up_comp_internal; f_equal;
    auto using vl_rename_comp_Lemma, vl_comp_rename_Lemma; finish_lists l x.
Qed.

Instance SubstLemmas_vl : SubstLemmas vl.
Proof.
  split; auto using vl_rename_Lemma, vl_ids_Lemma, vl_comp_Lemma.
Qed.

Instance HSubstLemmas_tm : HSubstLemmas vl tm.
Proof.
  split; auto using tm_ids_Lemma, tm_comp_Lemma.
Qed.

Instance HSubstLemmas_ty : HSubstLemmas vl ty.
Proof.
  split; auto using ty_ids_Lemma, ty_comp_Lemma.
Qed.

Instance HSubstLemmas_vls : HSubstLemmas vl vls.
Proof.
  split; trivial; intros; rewrite /hsubst;
    induction s; asimpl; by f_equal.
Qed.

Instance HSubstLemmas_list `{Ids X} `{HSubst vl X} {hsl: HSubstLemmas vl X}: HSubstLemmas vl (list X).
Proof.
  split; trivial; intros; rewrite /hsubst;
    induction s; asimpl; by f_equal.
Qed.

Instance HSubstLemmas_ctx : HSubstLemmas vl ctx := _.

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
