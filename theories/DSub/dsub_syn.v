From D Require Export prelude tactics asubst_base.

Inductive tm : Type :=
  | tv : vl_ -> tm
  | tapp : tm -> tm -> tm
  | tskip : tm -> tm
 with vl_ : Type :=
  | var_vl : var -> vl_
  | vnat : nat -> vl_
  | vabs : tm -> vl_
  | vty : ty -> vl_
  | vstamp: list vl_ -> stamp -> vl_
 with ty : Type :=
  | TTop : ty
  | TBot : ty
  (* | TAnd : ty -> ty -> ty *)
  (* | TOr : ty -> ty -> ty *)
  | TLater : ty -> ty
  | TAll : ty -> ty -> ty
  (* | TMu : ty -> ty *)
  | TTMem : ty -> ty -> ty
  | TSel : vl_ -> ty
  | TNat : ty.

Definition vl := vl_.

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

Instance inh_ty : Inhabited ty := populate TNat.
Instance inh_vl : Inhabited vl := populate (vnat 0).
Instance inh_tm : Inhabited tm := populate (tv inhabitant).

Instance ids_vl : Ids vl := var_vl.

Instance inj_ids : Inj (=) (=@{vl}) ids.
Proof. by move=>??[]. Qed.

Instance ids_tm : Ids tm := inh_ids.
Instance ids_ty : Ids ty := inh_ids.
Instance ids_vls : Ids vls := _.
Instance ids_ctx : Ids ctx := _.

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

Instance rename_tm : Rename tm := tm_rename.
Instance rename_vl : Rename vl := vl_rename.
Instance rename_ty : Rename ty := ty_rename.

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

Instance subst_vl : Subst vl := vl_subst.
Instance hsubst_tm : HSubst vl tm := tm_hsubst.
Instance hsubst_ty : HSubst vl ty := ty_hsubst.

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

Instance subst_lemmas_vl : SubstLemmas vl.
Proof.
  split; auto using vl_rename_Lemma, vl_ids_Lemma, vl_comp_Lemma.
Qed.

Instance hsubst_lemmas_tm : HSubstLemmas vl tm.
Proof.
  split; auto using tm_ids_Lemma, tm_comp_Lemma.
Qed.

Instance hsubst_lemmas_ty : HSubstLemmas vl ty.
Proof.
  split; auto using ty_ids_Lemma, ty_comp_Lemma.
Qed.

Instance hsubst_lemmas_ctx : HSubstLemmas vl ctx := _.

Include Sorts.

Instance sort_tm: Sort tm := {}.
Instance sort_ty: Sort ty := {}.

Instance inh_ctx: Inhabited ctx := _.
Instance rename_ctx: Rename ctx := _.
Instance hsubst_vl_ctx: HSubst vl ctx := _.
Instance sort_ctx: Sort ctx := {}.
Instance lookup_ctx: Lookup var ty ctx := _.
Global Typeclasses Opaque ctx.
