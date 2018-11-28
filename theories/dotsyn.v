Require Import Logic.FunctionalExtensionality.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import invariants.
From Dot Require Export prelude.

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

Instance Ids_tm : Ids tm := λ _, tv (vnat 0).
Instance Ids_dm : Ids dm := λ _, dvl (vnat 0).
Instance Ids_pth : Ids path := λ _, pv (vnat 0).
Instance Ids_ty : Ids ty := λ _, TNat.
Instance Ids_vls : Ids vls := λ _, [].
Instance Ids_dms : Ids dms := λ _, [].
Instance Ids_ctx : Ids ctx := λ _, [].

Instance Ids_vl : Ids vl.
Proof. by constructor. Defined.

Instance vls_rename `{Rename vl} : Rename vls :=
λ (sb : var → var) (vs : vls), map (rename sb) vs.

Instance dms_rename `{Rename dm} : Rename dms :=
    λ (sb : var → var) (ds : dms), map (rename sb) ds.

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
Instance Rename_vls : Rename vls := vls_rename.
Instance Rename_dms : Rename dms := dms_rename.

Definition ctx_rename (sb : var → var) (Γ : ctx) := map (rename sb) Γ.
Instance Rename_ctx : Rename ctx := ctx_rename.

Lemma vls_rename_fold (sb : var → var) (vs : vls) :
  map (rename sb) vs = rename sb vs.
Proof. trivial. Qed.
Global Hint Rewrite vls_rename_fold : autosubst.

Lemma dms_rename_fold sb (ds : dms) : map (rename sb) ds = rename sb ds.
Proof. trivial. Qed.
Global Hint Rewrite dms_rename_fold : autosubst.

Lemma ctx_rename_fold sb (Γ : ctx) : map (rename sb) Γ = rename sb Γ.
Proof. trivial. Qed.
Global Hint Rewrite ctx_rename_fold : autosubst.

Instance vls_hsubst `{Subst vl} : HSubst vl vls :=
  λ (sb : var → vl) (vs : vls), map (subst sb) vs.

Instance dms_hsubst `{HSubst vl dm} : HSubst vl dms :=
  λ (sb : var → vl) (ds : dms), map (hsubst sb) ds.

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

Instance HSubst_tm : HSubst vl tm := tm_hsubst.
Instance Subst_vl : Subst vl := vl_subst.
Instance HSubst_ty : HSubst vl ty := ty_hsubst.
Instance HSubst_dm : HSubst vl dm := dm_hsubst.
Instance HSubst_pth : HSubst vl path := path_hsubst.

Definition ctx_hsubst (sb : var → vl) (Γ : ctx) := map (hsubst sb) Γ.
Instance HSubst_ctx : HSubst vl ctx := ctx_hsubst.

Lemma vls_hsubst_fold (sb : var → vl) (vs : vls) :
  map (subst sb) vs = hsubst sb vs.
Proof. trivial. Qed.
Global Hint Rewrite vls_hsubst_fold : autosubst.

Lemma dms_hsubst_fold sb (ds : dms) : map (hsubst sb) ds = hsubst sb ds.
Proof. trivial. Qed.
Global Hint Rewrite dms_hsubst_fold : autosubst.

Lemma ctx_hsubst_fold sb (Γ : ctx) : map (hsubst sb) Γ = hsubst sb Γ.
Proof. trivial. Qed.
Global Hint Rewrite ctx_hsubst_fold : autosubst.

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
  - rewrite /Decision; decide equality;
      try (apply tm_eq_dec || apply nat_eq_dec || apply @list_eq_dec); auto.
  - rewrite /Decision; decide equality; try (apply vl_eq_dec || apply nat_eq_dec).
  - rewrite /Decision; decide equality;
      try (apply ty_eq_dec || apply vl_eq_dec || apply @list_eq_dec ||
           apply positive_eq_dec); auto.
  - rewrite /Decision; decide equality;
      try (apply path_eq_dec || apply nat_eq_dec); auto.
  -  rewrite /Decision; decide equality;
       try (apply vl_eq_dec || apply nat_eq_dec); auto.
Qed.

Global Instance vl_eq_dec' : EqDecision vl.
Proof. by intros ? ?; apply vl_eq_dec. Qed.
Global Instance tm_eq_dec' : EqDecision tm.
Proof. by intros ? ?; apply tm_eq_dec. Qed.
Global Instance dm_eq_dec' : EqDecision dm.
Proof. by intros ? ?; apply dm_eq_dec. Qed.
Global Instance ty_eq_dec' : EqDecision ty.
Proof. by intros ? ?; apply ty_eq_dec. Qed.
Global Instance path_eq_dec' : EqDecision path.
Proof. by intros ? ?; apply path_eq_dec. Qed.
Global Instance vls_eq_dec' : EqDecision vls.
Proof. by intros ? ?; apply list_eq_dec. Qed.
Global Instance dms_eq_dec' : EqDecision dms.
Proof. by intros ? ?; apply list_eq_dec. Qed.

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
  - destruct v; simpl; auto.
    + by rewrite tm_rename_Lemma up_upren_internal.
    + rewrite /rename /dms_rename.
      f_equal; induction l; simpl; first trivial.
        by rewrite IHl dm_rename_Lemma up_upren_internal.
  - destruct t; simpl; auto;
      try (by rewrite ?vl_rename_Lemma ?tm_rename_Lemma).
  - destruct d; simpl.
    + by rewrite ty_rename_Lemma.
    + rewrite /rename /vls_rename.
      f_equal. induction l; simpl; first trivial.
        by rewrite IHl vl_rename_Lemma.
    + by rewrite vl_rename_Lemma.
  - destruct T; simpl; auto;
      by rewrite ?ty_rename_Lemma ?path_rename_Lemma ?up_upren_internal.
  - induction pth; simpl; auto; by rewrite ?vl_rename_Lemma ?path_rename_Lemma.
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
  - destruct v; simpl; auto.
    + by rewrite up_id_internal // tm_ids_Lemma.
    + rewrite /hsubst /dms_hsubst.
      f_equal; induction l; simpl; first trivial.
        by rewrite IHl up_id_internal // dm_ids_Lemma.
  - destruct t; simpl; auto; by rewrite ?vl_ids_Lemma ?tm_ids_Lemma.
  - destruct d; simpl.
    + by rewrite ty_ids_Lemma.
    + rewrite /hsubst /vls_hsubst.
      f_equal. induction l; simpl; first trivial.
        by rewrite IHl vl_ids_Lemma.
    + by rewrite vl_ids_Lemma.
  - destruct T; simpl; auto;
      by rewrite ?ty_ids_Lemma ?up_id_internal // ?ty_ids_Lemma ?path_ids_Lemma.
  - induction pth; simpl; auto; by rewrite ?vl_ids_Lemma ?path_ids_Lemma.
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
  - destruct v; simpl; auto.
    + by rewrite tm_comp_rename_Lemma up_comp_ren_subst.
    + rewrite /hsubst /dms_hsubst.
      f_equal; induction l; simpl; first trivial.
        by rewrite IHl dm_comp_rename_Lemma up_comp_ren_subst.
  - destruct t; simpl; auto;
      by rewrite ?vl_comp_rename_Lemma ?tm_comp_rename_Lemma.
  - destruct d; simpl.
    + by rewrite ty_comp_rename_Lemma.
    + rewrite /hsubst /vls_hsubst.
      f_equal. induction l; simpl; first trivial.
        by rewrite IHl vl_comp_rename_Lemma.
    + by rewrite vl_comp_rename_Lemma.
  - destruct T; simpl; auto;
      rewrite ?ty_comp_rename_Lemma ?path_comp_rename_Lemma;
        by try rewrite up_comp_ren_subst.
  - induction pth; simpl; auto;
      by rewrite ?vl_comp_rename_Lemma ?path_comp_rename_Lemma.
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
  - destruct v; simpl; auto.
    + by rewrite tm_rename_comp_Lemma up_comp_subst_ren_internal;
        auto using vl_rename_Lemma, vl_comp_rename_Lemma.
    + rewrite /hsubst /dms_hsubst /rename /dms_rename.
      f_equal; induction l; simpl; first trivial.
        by rewrite IHl dm_rename_comp_Lemma
                   up_comp_subst_ren_internal;
          auto using vl_rename_Lemma, vl_comp_rename_Lemma.
  - destruct t; simpl; auto;
      by rewrite ?vl_rename_comp_Lemma ?tm_rename_comp_Lemma.
  - destruct d; simpl.
    + by rewrite ty_rename_comp_Lemma.
    + rewrite /hsubst /vls_hsubst /rename /vls_rename.
      f_equal. induction l; simpl; first trivial.
        by rewrite IHl vl_rename_comp_Lemma.
    + by rewrite vl_rename_comp_Lemma.
  - destruct T; simpl; auto;
      rewrite ?ty_rename_comp_Lemma ?path_rename_comp_Lemma
              ?up_comp_subst_ren_internal;
      auto using vl_rename_Lemma, vl_comp_rename_Lemma.
  - induction pth; simpl; auto;
      by rewrite ?vl_rename_comp_Lemma ?path_rename_comp_Lemma.
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
  - destruct v; simpl; auto.
    + by rewrite tm_comp_Lemma up_comp_internal;
        auto using vl_rename_comp_Lemma, vl_comp_rename_Lemma.
    + rewrite /hsubst /dms_hsubst.
      f_equal; induction l; simpl; first trivial.
        by rewrite IHl dm_comp_Lemma up_comp_internal;
          auto using vl_rename_comp_Lemma, vl_comp_rename_Lemma.
  - destruct t; simpl; auto;
      by rewrite ?vl_comp_Lemma ?tm_comp_Lemma.
  - destruct d; simpl.
    + by rewrite ty_comp_Lemma.
    + rewrite /hsubst /vls_hsubst.
      f_equal. induction l; simpl; first trivial.
        by rewrite IHl vl_comp_Lemma.
    + by rewrite vl_comp_Lemma.
  - destruct T; simpl; auto;
      rewrite ?ty_comp_Lemma ?path_comp_Lemma
              ?up_comp_internal;
      auto using vl_rename_comp_Lemma, vl_comp_rename_Lemma.
  - induction pth; simpl; auto;
      by rewrite ?vl_comp_Lemma ?path_comp_Lemma.
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
  split; trivial.
  - intros vs. rewrite /hsubst /vls_hsubst.
    induction vs; simpl; first trivial.
    by rewrite IHvs vl_ids_Lemma.
  - intros θ η vs. rewrite /hsubst /vls_hsubst.
    induction vs; simpl; first trivial.
    by rewrite IHvs vl_comp_Lemma.
Qed.

Instance HSubstLemmas_dms : HSubstLemmas vl dms.
Proof.
  split; trivial.
  - intros ds. rewrite /hsubst /dms_hsubst.
    induction ds; simpl; first trivial.
    by rewrite IHds dm_ids_Lemma.
  - intros θ η ds. rewrite /hsubst /dms_hsubst.
    induction ds; simpl; first trivial.
    by rewrite IHds dm_comp_Lemma.
Qed.

Instance HSubstLemmas_ctx : HSubstLemmas vl ctx.
Proof.
  split; trivial.
  - intros Γ. rewrite /hsubst /HSubst_ctx /ctx_hsubst.
    induction Γ; simpl; first trivial.
    by rewrite IHΓ ty_ids_Lemma.
  - intros θ η Γ. rewrite /hsubst /HSubst_ctx /ctx_hsubst.
    induction Γ; simpl; first trivial.
    by rewrite IHΓ ty_comp_Lemma.
Qed.
