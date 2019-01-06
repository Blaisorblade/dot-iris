From iris.base_logic.lib Require Import iprop.
From Dot Require Export prelude tactics.

Definition label := nat.

Inductive tm  : Type :=
  | tv : vl -> tm
  | tapp : tm -> tm -> tm
  | tproj : tm -> label -> tm
  | tskip : tm -> tm
 with vl  : Type :=
  | var_vl : var -> vl
  | vnat : nat -> vl
  | vabs : tm -> vl
  | vobj : (list dm) -> vl
 with dm  : Type :=
  | dtysyn : ty -> dm
  | dtysem : (list vl) -> gname -> dm
  | dvl : vl -> dm
 with path  : Type :=
  | pv : vl -> path
  | pself : path -> label -> path
 with ty  : Type :=
  | TTop :  ty
  | TBot :  ty
  | TAnd : ty -> ty -> ty
  | TOr : ty -> ty -> ty
  | TLater : ty -> ty
  | TAll : ty -> ty -> ty
  | TMu : ty -> ty
  | TVMem : label -> ty -> ty
  | TTMem : label -> ty -> ty -> ty
  | TSel : path -> label -> ty
  | TSelA : path -> label -> ty -> ty -> ty
  | TNat :  ty.

Definition vls := list vl.
Definition dms := list dm.
Definition ctx := list ty.

(* Module Coq_IndPrinciples_Bad. *)
(*   Scheme tm_bad_mut_ind := Induction for tm Sort Prop *)
(*   with   vl_bad_mut_ind := Induction for vl Sort Prop *)
(*   with   dm_bad_mut_ind := Induction for dm Sort Prop *)
(*   with   path_bad_mut_ind := Induction for path Sort Prop *)
(*   with   ty_bad_mut_ind := Induction for ty Sort Prop. *)

(*   Combined Scheme syntax_bad_mut_ind from tm_bad_mut_ind, vl_bad_mut_ind, dm_bad_mut_ind, path_bad_mut_ind, ty_bad_mut_ind. *)
(*   Check syntax_bad_mut_ind. *)

(*   Scheme tm_bad_mut_rect := Induction for tm Sort Type *)
(*   with   vl_bad_mut_rect := Induction for vl Sort Type *)
(*   with   dm_bad_mut_rect := Induction for dm Sort Type *)
(*   with   path_bad_mut_rect := Induction for path Sort Type *)
(*   with   ty_bad_mut_rect := Induction for ty Sort Type. *)

(*   Fail Combined Scheme syntax_bad_mut_rect from tm_bad_mut_rect, vl_bad_mut_rect, dm_bad_mut_rect, path_bad_mut_rect, ty_bad_mut_rect. *)
(*   Combined Scheme syntax_bad_mut_rect from tm_bad_mut_ind, vl_bad_mut_rect, dm_bad_mut_rect, path_bad_mut_rect, ty_bad_mut_rect. *)
(*   Check syntax_bad_mut_rect. *)
(* End Coq_IndPrinciples_Bad. *)

Section syntax_mut_rect.
  Variable Ptm : tm   → Type.
  Variable Pvl : vl   → Type.
  Variable Pdm : dm   → Type.
  Variable Ppt : path → Type.
  Variable Pty : ty   → Type.

  Variable step_tv: ∀ v, Pvl v → Ptm (tv v).
  Variable step_tapp: ∀ t, Ptm t → ∀ t0, Ptm t0 → Ptm (tapp t t0).
  Variable step_tproj: ∀ t, Ptm t → ∀ l, Ptm (tproj t l).
  Variable step_tskip: ∀ t, Ptm t → Ptm (tskip t).
  Variable step_var_vl: ∀ v, Pvl (var_vl v).
  Variable step_vnat: ∀ n, Pvl (vnat n).
  Variable step_vabs: ∀ t, Ptm t → Pvl (vabs t).
  Variable step_vobj: ∀ l, Pvl (vobj l).
  Variable step_dtysyn: ∀ t, Pty t → Pdm (dtysyn t).
  (* Original: *)
  (* Variable step_dtysem: ∀ vsl g, Pdm (dtysem vs g). *)
  Variable step_dtysem: ∀ vs g, ForallT Pvl vs → Pdm (dtysem vs g).
  Variable step_dvl: ∀ v, Pvl v → Pdm (dvl v).
  Variable step_pv: ∀ v, Pvl v → Ppt (pv v).
  Variable step_psefl: ∀ p, Ppt p → ∀ l, Ppt (pself p l).
  Variable step_TTop: Pty TTop.
  Variable step_TBot: Pty TBot.
  Variable step_TAnd: ∀ t, Pty t → ∀ t0, Pty t0 → Pty (TAnd t t0).
  Variable step_TOr: ∀ t, Pty t → ∀ t0, Pty t0 → Pty (TOr t t0).
  Variable step_TLater: ∀ t, Pty t → Pty (TLater t).
  Variable step_TAll: ∀ t, Pty t → ∀ t0 : ty, Pty t0 → Pty (TAll t t0).
  Variable step_TMu: ∀ t, Pty t → Pty (TMu t).
  Variable step_TVMem: ∀ l t, Pty t → Pty (TVMem l t).
  Variable step_TTMem: ∀ l t, Pty t → ∀ t0, Pty t0 → Pty (TTMem l t t0).
  Variable step_TSel: ∀ p, Ppt p → ∀ l : label, Pty (TSel p l).
  Variable step_TSElA: ∀ p, Ppt p → ∀ (l : label) (t : ty), Pty t → ∀ t0 : ty, Pty t0 → Pty (TSelA p l t t0).
  Variable step_TNat: Pty TNat.

  Fixpoint tm_mut_rect t: Ptm t
  with vl_mut_rect v: Pvl v
  with dm_mut_rect d: Pdm d
  with path_mut_rect p: Ppt p
  with ty_mut_rect T: Pty T.
  Proof.
    (* Automation risk producing circular proofs that call right away the lemma we're proving.
       Instead we want to apply one of the [case_] arguments to perform an
       inductive step, and only then call ourselves recursively. *)
    all: destruct 0;
      try match goal with
      (* Warning: add other arities as needed. *)
      | Hstep: context [?P (?c _ _ _ _)] |- ?P (?c _ _ _ _) => apply Hstep; trivial
      | Hstep: context [?P (?c _ _ _)] |- ?P (?c _ _ _) => apply Hstep; trivial
      | Hstep: context [?P (?c _ _)] |- ?P (?c _ _) => apply Hstep; trivial
      | Hstep: context [?P (?c _)] |- ?P (?c _) => apply Hstep; trivial
      | Hstep: context [?P (?c)] |- ?P (?c) => apply Hstep; trivial
      end.
    induction l; auto.
  Qed.

  Lemma syntax_mut_rect: (∀ t, Ptm t) * (∀ v, Pvl v) * (∀ d, Pdm d) * (∀ p, Ppt p) * (∀ t, Pty t).
  Proof.
    repeat split; intros.
    - eapply tm_mut_rect.
    - eapply vl_mut_rect.
    - eapply dm_mut_rect.
    - eapply path_mut_rect.
    - eapply ty_mut_rect.
  Qed.
End syntax_mut_rect.

Section syntax_mut_ind.
  Variable Ptm : tm   → Prop.
  Variable Pvl : vl   → Prop.
  Variable Pdm : dm   → Prop.
  Variable Ppt : path → Prop.
  Variable Pty : ty   → Prop.

  Variable step_tv: ∀ v, Pvl v → Ptm (tv v).
  Variable step_tapp: ∀ t, Ptm t → ∀ t0, Ptm t0 → Ptm (tapp t t0).
  Variable step_tproj: ∀ t, Ptm t → ∀ l, Ptm (tproj t l).
  Variable step_tskip: ∀ t, Ptm t → Ptm (tskip t).
  Variable step_var_vl: ∀ v, Pvl (var_vl v).
  Variable step_vnat: ∀ n, Pvl (vnat n).
  Variable step_vabs: ∀ t, Ptm t → Pvl (vabs t).
  Variable step_vobj: ∀ l, Pvl (vobj l).
  Variable step_dtysyn: ∀ t, Pty t → Pdm (dtysyn t).
  (* Original: *)
  (* Variable step_dtysem: ∀ vsl g, Pdm (dtysem vs g). *)
  Variable step_dtysem: ∀ vs g, Forall Pvl vs → Pdm (dtysem vs g).
  Variable step_dvl: ∀ v, Pvl v → Pdm (dvl v).
  Variable step_pv: ∀ v, Pvl v → Ppt (pv v).
  Variable step_psefl: ∀ p, Ppt p → ∀ l, Ppt (pself p l).
  Variable step_TTop: Pty TTop.
  Variable step_TBot: Pty TBot.
  Variable step_TAnd: ∀ t, Pty t → ∀ t0, Pty t0 → Pty (TAnd t t0).
  Variable step_TOr: ∀ t, Pty t → ∀ t0, Pty t0 → Pty (TOr t t0).
  Variable step_TLater: ∀ t, Pty t → Pty (TLater t).
  Variable step_TAll: ∀ t, Pty t → ∀ t0 : ty, Pty t0 → Pty (TAll t t0).
  Variable step_TMu: ∀ t, Pty t → Pty (TMu t).
  Variable step_TVMem: ∀ l t, Pty t → Pty (TVMem l t).
  Variable step_TTMem: ∀ l t, Pty t → ∀ t0, Pty t0 → Pty (TTMem l t t0).
  Variable step_TSel: ∀ p, Ppt p → ∀ l : label, Pty (TSel p l).
  Variable step_TSElA: ∀ p, Ppt p → ∀ (l : label) (t : ty), Pty t → ∀ t0 : ty, Pty t0 → Pty (TSelA p l t t0).
  Variable step_TNat: Pty TNat.

  Lemma syntax_mut_ind: (∀ t, Ptm t) ∧ (∀ v, Pvl v) ∧ (∀ d, Pdm d) ∧ (∀ p, Ppt p) ∧ (∀ t, Pty t).
  Proof.
    efeed pose proof syntax_mut_rect as H; try done.
    - intros vs g HvsT. apply step_dtysem, ForallT_Forall, HvsT.
    - ev; split_and! ; assumption.
  Qed.
End syntax_mut_ind.

Instance Inh_ty : Inhabited ty := populate TNat.
Instance Inh_vl : Inhabited vl := populate (vnat 0).
Instance Inh_dm : Inhabited dm := populate (dvl inhabitant).
Instance Inh_pth : Inhabited path := populate (pv inhabitant).
Instance Inh_tm : Inhabited tm := populate (tv inhabitant).

Instance Ids_vl : Ids vl.
Proof. by constructor. Defined.

Instance Ids_tm : Ids tm := λ _, inhabitant.
Instance Ids_dm : Ids dm := λ _, inhabitant.
Instance Ids_pth : Ids path := λ _, inhabitant.
Instance Ids_ty : Ids ty := λ _, inhabitant.
Instance Ids_list {A}: Ids (list A) := λ _, inhabitant.
Instance Ids_vls : Ids vls := _.
Instance Ids_dms : Ids dms := _.
Instance Ids_ctx : Ids ctx := _.

Instance list_rename `{Rename X} : Rename (list X) :=
  λ (sb : var → var) xs, map (rename sb) xs.

Fixpoint tm_rename (sb : var → var) (e : tm) {struct e} : tm :=
  let a := tm_rename : Rename tm in
  let b := vl_rename : Rename vl in
  match e with
  | tv v => tv (rename sb v)
  | tapp t1 t2 => tapp (rename sb t1) (rename sb t2)
  | tproj t l => (tproj (rename sb t) l)
  | tskip t => tskip (rename sb t)
  end
with
vl_rename (sb : var → var) (v : vl) {struct v} : vl :=
  let a := tm_rename : Rename tm in
  let b := vl_rename : Rename vl in
  let c := dm_rename : Rename dm in
  match v with
  | var_vl x => var_vl (sb x)
  | vnat n => vnat n
  | vabs t => vabs (rename (upren sb) t)
  | vobj d => vobj (rename (upren sb) d)
  end
with
dm_rename (sb : var → var) (d : dm) {struct d} : dm :=
  let a := vl_rename : Rename vl in
  let b := ty_rename : Rename ty in
  match d with
  | dtysyn ty => dtysyn (rename sb ty)
  | dtysem lv γ => dtysem (rename sb lv) γ
  | dvl v => dvl (rename sb v)
  end
with
ty_rename (sb : var → var) (T : ty) {struct T}: ty :=
  let a := ty_rename : Rename ty in
  let b := path_rename : Rename path in
  match T with
  | TTop => TTop
  | TBot => TBot
  | TAnd T1 T2 => TAnd (rename sb T1) (rename sb T2)
  | TOr T1 T2 => TOr (rename sb T1) (rename sb T2)
  | TLater T => TLater (rename sb T)
  | TAll T1 T2 => TAll (rename sb T1) (rename (upren sb) T2)
  | TMu T => TMu (rename (upren sb) T)
  | TVMem l T => TVMem l (rename sb T)
  | TTMem l T1 T2 => TTMem l (rename sb T1) (rename sb T2)
  | TSel pth l => TSel (rename sb pth) l
  | TSelA pth l T1 T2 => TSelA (rename sb pth) l (rename sb T1) (rename sb T2)
  | TNat => TNat
  end
with
path_rename (sb : var → var) (pth : path) {struct pth} : path :=
  let a := vl_rename : Rename vl in
  let b := path_rename : Rename path in
  match pth with
  | pv v => pv (rename sb v)
  | pself pth l => pself (rename sb pth) l
  end.

Instance Rename_tm : Rename tm := tm_rename.
Instance Rename_vl : Rename vl := vl_rename.
Instance Rename_ty : Rename ty := ty_rename.
Instance Rename_dm : Rename dm := dm_rename.
Instance Rename_pth : Rename path := path_rename.

Lemma list_rename_fold `{Rename X} (sb : var → var) (xs : list X) : map (rename sb) xs = rename sb xs.
Proof. trivial. Qed.

Definition vls_rename_fold: ∀ sb vs, map (rename sb) vs = rename sb vs := list_rename_fold.
Definition dms_rename_fold: ∀ sb ds, map (rename sb) ds = rename sb ds := list_rename_fold.
Definition ctx_rename_fold: ∀ sb Γ, map (rename sb) Γ = rename sb Γ := list_rename_fold.

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
  | tproj t l => (tproj (hsubst sb t) l)
  | tskip t => tskip (hsubst sb t)
  end
with
vl_subst (sb : var → vl) (v : vl) : vl :=
  let a := tm_hsubst : HSubst vl tm in
  let b := dm_hsubst : HSubst vl dm in
  match v with
  | var_vl x => sb x
  | vnat n => vnat n
  | vabs t => vabs (hsubst (up sb) t)
  | vobj d => vobj (hsubst (up sb) d)
  end
with
dm_hsubst (sb : var → vl) (d : dm) : dm :=
  let a := vl_subst : Subst vl in
  let b := ty_hsubst : HSubst vl ty in
  match d with
  | dtysyn ty => dtysyn (hsubst sb ty)
  | dtysem lv γ => dtysem (hsubst sb lv) γ
  | dvl v => dvl (subst sb v)
  end
with
ty_hsubst (sb : var → vl) (T : ty) : ty :=
  let a := ty_hsubst : HSubst vl ty in
  let b := path_hsubst : HSubst vl path in
  match T with
  | TTop => TTop
  | TBot => TBot
  | TAnd T1 T2 => TAnd (hsubst sb T1) (hsubst sb T2)
  | TOr T1 T2 => TOr (hsubst sb T1) (hsubst sb T2)
  | TLater T => TLater (hsubst sb T)
  | TAll T1 T2 => TAll (hsubst sb T1) (hsubst (up sb) T2)
  | TMu T => TMu (hsubst (up sb) T)
  | TVMem l T => TVMem l (hsubst sb T)
  | TTMem l T1 T2 => TTMem l (hsubst sb T1) (hsubst sb T2)
  | TSel pth l => TSel (hsubst sb pth) l
  | TSelA pth l T1 T2 => TSelA (hsubst sb pth) l (hsubst sb T1) (hsubst sb T2)
  | TNat => TNat
  end
with
path_hsubst (sb : var → vl) (pth : path) : path :=
  let b := vl_subst : Subst vl in
  let b := path_hsubst : HSubst vl path in
  match pth with
  | pv v => pv (subst sb v)
  | pself pth l => pself (hsubst sb pth) l
  end.

Instance Subst_vl : Subst vl := vl_subst.
Instance HSubst_tm : HSubst vl tm := tm_hsubst.
Instance HSubst_ty : HSubst vl ty := ty_hsubst.
Instance HSubst_dm : HSubst vl dm := dm_hsubst.
Instance HSubst_pth : HSubst vl path := path_hsubst.

(* Now type inference solves HSubst vl ? by infering HSubst vl ty infers unspecified asts to be [path]s. *)
(* Goal ∀ s x, x.|[s] = x. *)
(* Abort. *)
Hint Mode HSubst - + : typeclass_instances.
(* That Hint stops that. *)
(* Fail Goal ∀ s x, x.|[s] = x. *)
(* Goal ∀ s (x: ty) , x.|[s] = x. Abort. *)

Lemma vls_subst_fold (sb : var → vl) (vs : vls) : map (subst sb) vs = hsubst sb vs.
Proof. trivial. Qed.

Lemma list_hsubst_fold `{HSubst vl X} sb (xs : list X) : map (hsubst sb) xs = hsubst sb xs.
Proof. trivial. Qed.

Hint Rewrite vls_subst_fold @list_hsubst_fold : autosubst.

Arguments vls_hsubst /.
Arguments list_hsubst /.

Lemma vl_eq_dec (v1 v2 : vl) : Decision (v1 = v2)
with
tm_eq_dec (t1 t2 : tm) : Decision (t1 = t2)
with
dm_eq_dec (d1 d2 : dm) : Decision (d1 = d2)
with
ty_eq_dec (ty1 ty2 : ty) : Decision (ty1 = ty2)
with
path_eq_dec (pth1 pth2 : path) : Decision (pth1 = pth2).
Proof.
   all: rewrite /Decision; decide equality;
       try (apply vl_eq_dec || apply tm_eq_dec || apply ty_eq_dec || apply path_eq_dec ||
            apply @list_eq_dec ||
            apply nat_eq_dec || apply positive_eq_dec); auto.
Qed.

Instance vl_eq_dec' : EqDecision vl := vl_eq_dec.
Instance tm_eq_dec' : EqDecision tm := tm_eq_dec.
Instance dm_eq_dec' : EqDecision dm := dm_eq_dec.
Instance ty_eq_dec' : EqDecision ty := ty_eq_dec.
Instance path_eq_dec' : EqDecision path := path_eq_dec.
Instance vls_eq_dec' : EqDecision vls := list_eq_dec.
Instance dms_eq_dec' : EqDecision dms := list_eq_dec.

Lemma vl_rename_Lemma (ξ : var → var) (v : vl) : rename ξ v = v.[ren ξ]
with
tm_rename_Lemma (ξ : var → var) (t : tm) : rename ξ t = t.|[ren ξ]
with
dm_rename_Lemma (ξ : var → var) (d : dm) : rename ξ d = d.|[ren ξ]
with
ty_rename_Lemma (ξ : var → var) (T : ty) : rename ξ T = T.|[ren ξ]
with
path_rename_Lemma (ξ : var → var) (pth : path) :
  rename ξ pth = pth.|[ren ξ].
Proof.
  all: (destruct v || destruct t || destruct d || destruct T || destruct pth);
    simpl;
      rewrite ?up_upren_internal; f_equal; trivial;
        elim l => * /=; f_equal; trivial.
Qed.

Lemma vl_ids_Lemma (v : vl) : v.[ids] = v
with
tm_ids_Lemma (t : tm) : t.|[ids] = t
with
dm_ids_Lemma (d : dm) : d.|[ids] = d
with
ty_ids_Lemma (T : ty) : T.|[ids] = T
with
path_ids_Lemma (pth : path) : pth.|[ids] = pth.
Proof.
  all: (destruct v || destruct t || destruct d || destruct T || destruct pth);
    simpl; f_equal; trivial;
      rewrite ?up_id_internal; trivial;
        elim l => * /=; f_equal; trivial.
Qed.

Lemma vl_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (v : vl) :
  (rename ξ v).[σ] = v.[ξ >>> σ]
with
tm_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (t : tm) :
  (rename ξ t).|[σ] = t.|[ξ >>> σ]
with
dm_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (d : dm) :
  (rename ξ d).|[σ] = d.|[ξ >>> σ]
with
ty_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (T : ty) :
  (rename ξ T).|[σ] = T.|[ξ >>> σ]
with
path_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (pth : path) :
  (rename ξ pth).|[σ] = pth.|[ξ >>> σ].
Proof.
  all: (destruct v || destruct t || destruct d || destruct T || destruct pth);
    simpl; f_equal; trivial;
      rewrite 1? up_comp_ren_subst; trivial;
        elim l => * /=; by f_equal.
Qed.

Lemma vl_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (v : vl) :
  rename ξ v.[σ] = v.[σ >>> rename ξ]
with
tm_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (t : tm) :
  rename ξ t.|[σ] = t.|[σ >>> rename ξ]
with
dm_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (d : dm) :
  rename ξ d.|[σ] = d.|[σ >>> rename ξ]
with
ty_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (T : ty) :
  rename ξ T.|[σ] = T.|[σ >>> rename ξ]
with
path_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (pth : path) :
  rename ξ pth.|[σ] = pth.|[σ >>> rename ξ].
Proof.
  all: (destruct v || destruct t || destruct d || destruct T || destruct pth);
    simpl; f_equal; trivial;
      rewrite 1? up_comp_subst_ren_internal;
      auto using vl_rename_Lemma, vl_comp_rename_Lemma;
      elim l => * /=; by f_equal.
Qed.

Lemma vl_comp_Lemma (σ τ : var → vl) (v : vl) : v.[σ].[τ] = v.[σ >> τ]
with
tm_comp_Lemma (σ τ : var → vl) (t : tm) : t.|[σ].|[τ] = t.|[σ >> τ]
with
dm_comp_Lemma (σ τ : var → vl) (d : dm) : d.|[σ].|[τ] = d.|[σ >> τ]
with
ty_comp_Lemma (σ τ : var → vl) (T : ty) : T.|[σ].|[τ] = T.|[σ >> τ]
with
path_comp_Lemma (σ τ : var → vl) (pth : path) : pth.|[σ].|[τ] = pth.|[σ >> τ].
Proof.
  all: (destruct v || destruct t || destruct d || destruct T || destruct pth);
    simpl; f_equal; trivial;
      rewrite 1? up_comp_internal; auto using vl_rename_comp_Lemma, vl_comp_rename_Lemma;
        auto using vl_rename_comp_Lemma, vl_comp_rename_Lemma;
        elim l => * /=; by f_equal.
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

Instance HSubstLemmas_dm : HSubstLemmas vl dm.
Proof.
  split; auto using dm_ids_Lemma, dm_comp_Lemma.
Qed.

Instance HSubstLemmas_pth : HSubstLemmas vl path.
Proof.
  split; auto using path_ids_Lemma, path_comp_Lemma.
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

Instance HSubstLemmas_dms : HSubstLemmas vl dms := _.
Instance HSubstLemmas_ctx : HSubstLemmas vl ctx := _.

(** After instantiating Autosubst, a few binding-related syntactic definitions
    that need not their own file. *)

Definition to_subst (ρ: list vl) : var → vl := foldr (λ v s, v .: s) ids ρ.

Lemma to_subst_nil: to_subst [] = ids.
Proof. trivial. Qed.

Lemma to_subst_cons v ρ : to_subst (v :: ρ) = v .: to_subst ρ.
Proof. trivial. Qed.
Hint Rewrite to_subst_nil to_subst_cons : autosubst.

Global Typeclasses Opaque to_subst.
Global Opaque to_subst.

Definition subst_sigma (σ: vls) (ρ: list vl) := σ.|[to_subst ρ].

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

Definition cl_ρ ρ := Forall (λ v, nclosed_vl v 0) ρ.
Arguments cl_ρ /.

(** The following ones are "direct" lemmas: deduce that an expression is closed
    by knowing that its subexpression are closed. *)

(** Needed by solve_fv_congruence when dealing with binders, such as in fv_vobj and fv_vabs. *)
Lemma eq_up s1 s2 n: eq_n_s s1 s2 n → eq_n_s (up s1) (up s2) (S n).
Proof.
  rewrite /up. move => Heq [|x] Hl //=. f_equiv. apply Heq. omega.
Qed.

(** Automated proof for such lemmas. *)
Ltac solve_fv_congruence := rewrite /nclosed /nclosed_vl => * /=; f_equiv; solve [(idtac + asimpl); auto using eq_up].

Lemma fv_cons `{Ids X} `{HSubst vl X} {hsla: HSubstLemmas vl X} (x: X) xs: nclosed xs 0 → nclosed x 0 → nclosed (x :: xs) 0.
Proof. solve_fv_congruence. Qed.
