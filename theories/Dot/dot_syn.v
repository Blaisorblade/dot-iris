From stdpp Require Import strings.
From D Require Export prelude tactics.

Definition label := string.

Inductive tm : Type :=
  | tv : vl -> tm
  | tapp : tm -> tm -> tm
  | tproj : tm -> label -> tm
  | tskip : tm -> tm
 with vl : Type :=
  | var_vl : var -> vl
  | vnat : nat -> vl
  | vabs : tm -> vl
  | vobj : list (label * dm) -> vl
 with dm : Type :=
  | dtysyn : ty -> dm
  | dtysem : list vl -> stamp -> dm
  | dvl : vl -> dm
 with path : Type :=
  | pv : vl -> path
  | pself : path -> label -> path
 with ty : Type :=
  | TTop : ty
  | TBot : ty
  | TAnd : ty -> ty -> ty
  | TOr : ty -> ty -> ty
  | TLater : ty -> ty
  | TAll : ty -> ty -> ty
  | TMu : ty -> ty
  | TVMem : label -> ty -> ty
  | TTMem : label -> ty -> ty -> ty
  | TSel : path -> label -> ty
  | TNat : ty.

Definition vls := list vl.
Definition dms := list (label * dm).
Definition ctx := list ty.

Implicit Types
         (T: ty) (v: vl) (t e: tm) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx).

Definition label_of_ty (T: ty): option label :=
  match T with
  | TTMem l _ _ => Some l
  | TVMem l _ => Some l
  | _ => None
  end.

Fixpoint dms_lookup (l : label) (ds : dms): option dm :=
  match ds with
  | [] => None
  | (l', d) :: ds =>
    match (decide (l = l')) with
    | left Heq => Some d
    | right _ => dms_lookup l ds
    end
  end.

Definition dms_has ds l d := dms_lookup l ds = Some d.
Definition dms_hasnt ds l := dms_lookup l ds = None.

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

  Variable step_tv: ∀ v1, Pvl v1 → Ptm (tv v1).
  Variable step_tapp: ∀ t1 t2, Ptm t1 → Ptm t2 → Ptm (tapp t1 t2).
  Variable step_tproj: ∀ t1 l, Ptm t1 → Ptm (tproj t1 l).
  Variable step_tskip: ∀ t1, Ptm t1 → Ptm (tskip t1).
  Variable step_var_vl: ∀ i, Pvl (var_vl i).
  Variable step_vnat: ∀ n, Pvl (vnat n).
  Variable step_vabs: ∀ t1, Ptm t1 → Pvl (vabs t1).
  (* Original: *)
  (* Variable step_vobj: ∀ l, Pvl (vobj l). *)
  Variable step_vobj: ∀ ds, ForallT Pdm (map snd ds) → Pvl (vobj ds).
  Variable step_dtysyn: ∀ T1, Pty T1 → Pdm (dtysyn T1).
  (* Original: *)
  (* Variable step_dtysem: ∀ vsl g, Pdm (dtysem vs g). *)
  Variable step_dtysem: ∀ vs s, ForallT Pvl vs → Pdm (dtysem vs s).
  Variable step_dvl: ∀ v1, Pvl v1 → Pdm (dvl v1).
  Variable step_pv: ∀ v1, Pvl v1 → Ppt (pv v1).
  Variable step_psefl: ∀ p1 l, Ppt p1 → Ppt (pself p1 l).
  Variable step_TTop: Pty TTop.
  Variable step_TBot: Pty TBot.
  Variable step_TAnd: ∀ T1 T2, Pty T1 → Pty T2 → Pty (TAnd T1 T2).
  Variable step_TOr: ∀ T1 T2, Pty T1 → Pty T2 → Pty (TOr T1 T2).
  Variable step_TLater: ∀ T1, Pty T1 → Pty (TLater T1).
  Variable step_TAll: ∀ T1 T2, Pty T1 → Pty T2 → Pty (TAll T1 T2).
  Variable step_TMu: ∀ T1, Pty T1 → Pty (TMu T1).
  Variable step_TVMem: ∀ l T1, Pty T1 → Pty (TVMem l T1).
  Variable step_TTMem: ∀ l T1 T2, Pty T1 → Pty T2 → Pty (TTMem l T1 T2).
  Variable step_TSel: ∀ p1 l, Ppt p1 → Pty (TSel p1 l).
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
    - elim: l => [|[l d] ds IHds] //=; auto.
    - elim: l => [|v vs IHxs] //=; auto.
  Qed.

  Lemma syntax_mut_rect: (∀ t, Ptm t) * (∀ v, Pvl v) * (∀ d, Pdm d) * (∀ p, Ppt p) * (∀ T, Pty T).
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

  Variable step_tv: ∀ v1, Pvl v1 → Ptm (tv v1).
  Variable step_tapp: ∀ t1 t2, Ptm t1 → Ptm t2 → Ptm (tapp t1 t2).
  Variable step_tproj: ∀ t1 l, Ptm t1 → Ptm (tproj t1 l).
  Variable step_tskip: ∀ t1, Ptm t1 → Ptm (tskip t1).
  Variable step_var_vl: ∀ i, Pvl (var_vl i).
  Variable step_vnat: ∀ n, Pvl (vnat n).
  Variable step_vabs: ∀ t1, Ptm t1 → Pvl (vabs t1).
  (* Original: *)
  (* Variable step_vobj: ∀ l, Pvl (vobj l). *)
  Variable step_vobj: ∀ ds, Forall Pdm (map snd ds) → Pvl (vobj ds).
  Variable step_dtysyn: ∀ T1, Pty T1 → Pdm (dtysyn T1).
  (* Original: *)
  (* Variable step_dtysem: ∀ vsl g, Pdm (dtysem vs g). *)
  Variable step_dtysem: ∀ vs s, Forall Pvl vs → Pdm (dtysem vs s).
  Variable step_dvl: ∀ v1, Pvl v1 → Pdm (dvl v1).
  Variable step_pv: ∀ v1, Pvl v1 → Ppt (pv v1).
  Variable step_psefl: ∀ p1 l, Ppt p1 → Ppt (pself p1 l).
  Variable step_TTop: Pty TTop.
  Variable step_TBot: Pty TBot.
  Variable step_TAnd: ∀ T1 T2, Pty T1 → Pty T2 → Pty (TAnd T1 T2).
  Variable step_TOr: ∀ T1 T2, Pty T1 → Pty T2 → Pty (TOr T1 T2).
  Variable step_TLater: ∀ T1, Pty T1 → Pty (TLater T1).
  Variable step_TAll: ∀ T1 T2, Pty T1 → Pty T2 → Pty (TAll T1 T2).
  Variable step_TMu: ∀ T1, Pty T1 → Pty (TMu T1).
  Variable step_TVMem: ∀ l T1, Pty T1 → Pty (TVMem l T1).
  Variable step_TTMem: ∀ l T1 T2, Pty T1 → Pty T2 → Pty (TTMem l T1 T2).
  Variable step_TSel: ∀ p1 l, Ppt p1 → Pty (TSel p1 l).
  Variable step_TNat: Pty TNat.

  Lemma syntax_mut_ind: (∀ t, Ptm t) ∧ (∀ v, Pvl v) ∧ (∀ d, Pdm d) ∧ (∀ p, Ppt p) ∧ (∀ T, Pty T).
  Proof.
    efeed pose proof syntax_mut_rect as H; try done.
    - intros ds HdsT. apply step_vobj, ForallT_Forall, HdsT.
    - intros vs g HvsT. apply step_dtysem, ForallT_Forall, HvsT.
    - ev; split_and! ; assumption.
  Qed.
End syntax_mut_ind.

Instance inh_ty : Inhabited ty := populate TNat.
Instance inh_vl : Inhabited vl := populate (vnat 0).
Instance inh_dm : Inhabited dm := populate (dvl inhabitant).
Instance inh_pth : Inhabited path := populate (pv inhabitant).
Instance inh_tm : Inhabited tm := populate (tv inhabitant).

Instance ids_vl : Ids vl.
Proof. by constructor. Defined.

Instance ids_tm : Ids tm := inh_ids.
Instance ids_dm : Ids dm := inh_ids.
Instance ids_pth : Ids path := inh_ids.
Instance ids_ty : Ids ty := inh_ids.
Instance ids_vls : Ids vls := _.
Instance ids_dms : Ids dms := _.
Instance ids_ctx : Ids ctx := _.

Definition mapsnd {A} `(f: B → C) : A * B → A * C := λ '(a, b), (a, f b).

Instance list_rename `{Rename X} : Rename (list X) :=
  λ sb xs, map (rename sb) xs.
Instance list_pair_rename {A} `{Rename X}: Rename (list (A * X)) :=
  λ sb xs, map (mapsnd (rename sb)) xs.

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

Instance rename_tm : Rename tm := tm_rename.
Instance rename_vl : Rename vl := vl_rename.
Instance rename_ty : Rename ty := ty_rename.
Instance rename_dm : Rename dm := dm_rename.
Instance rename_pth : Rename path := path_rename.

Definition list_rename_fold `{Rename X} (sb : var → var) (xs : list X) : map (rename sb) xs = rename sb xs := eq_refl.
Definition list_pair_rename_fold {A} `{Rename X} sb (xs: list (A * X)): map (mapsnd (rename sb)) xs = rename sb xs := eq_refl.

Definition vls_rename_fold: ∀ sb vs, map (rename sb) vs = rename sb vs := list_rename_fold.

Hint Rewrite @list_rename_fold @list_pair_rename_fold : autosubst.

Instance vls_hsubst `{Subst vl} : HSubst vl vls :=
  λ (sb : var → vl) (vs : vls), map (subst sb) vs.

Instance list_hsubst `{HSubst vl X}: HSubst vl (list X) := λ sb xs, map (hsubst sb) xs.
Instance list_pair_hsubst {A} `{HSubst vl X}: HSubst vl (list (A * X)) := λ sb xs, map (mapsnd (hsubst sb)) xs.

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

Instance subst_vl : Subst vl := vl_subst.
Instance hsubst_tm : HSubst vl tm := tm_hsubst.
Instance hsubst_ty : HSubst vl ty := ty_hsubst.
Instance hsubst_dm : HSubst vl dm := dm_hsubst.
Instance hsubst_pth : HSubst vl path := path_hsubst.

Definition vls_subst_fold (sb : var → vl) (vs : vls) : map (subst sb) vs = hsubst sb vs := eq_refl.
Definition list_hsubst_fold `{HSubst vl X} sb (xs : list X) : map (hsubst sb) xs = hsubst sb xs := eq_refl.
Definition list_pair_hsubst_fold {A} `{HSubst vl X} sb (xs : list (A * X)) : map (mapsnd (hsubst sb)) xs = hsubst sb xs := eq_refl.

Hint Rewrite vls_subst_fold @list_hsubst_fold @list_pair_hsubst_fold : autosubst.

Arguments vls_hsubst /.
Arguments list_hsubst /.
Arguments list_pair_hsubst /.

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
       try repeat (apply vl_eq_dec || apply tm_eq_dec || apply ty_eq_dec || apply path_eq_dec ||
            apply @prod_eq_dec ||
            apply @list_eq_dec ||
            apply nat_eq_dec || apply positive_eq_dec || apply string_eq_dec); auto.
Qed.

Instance vl_eq_dec' : EqDecision vl := vl_eq_dec.
Instance tm_eq_dec' : EqDecision tm := tm_eq_dec.
Instance dm_eq_dec' : EqDecision dm := dm_eq_dec.
Instance ty_eq_dec' : EqDecision ty := ty_eq_dec.
Instance path_eq_dec' : EqDecision path := path_eq_dec.
Instance vls_eq_dec' : EqDecision vls := list_eq_dec.
Instance dms_eq_dec' : EqDecision dms := list_eq_dec.

Local Ltac finish_lists l x :=
  elim: l => [|x xs IHds] //=; idtac + elim: x => [l d] //=; f_equal => //; by f_equal.

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
  all: destruct 0; rewrite /= ?up_upren_internal; f_equal => //; finish_lists l x.
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
  all: destruct 0; rewrite /= ?up_id_internal; f_equal => //; finish_lists l x.
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
  all: destruct 0; rewrite /= 1? up_comp_ren_subst; f_equal => //; finish_lists l x.
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
  all: destruct 0; rewrite /= ? up_comp_subst_ren_internal; f_equal => //;
    auto using vl_rename_Lemma, vl_comp_rename_Lemma; finish_lists l x.
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

Instance hsubst_lemmas_dm : HSubstLemmas vl dm.
Proof.
  split; auto using dm_ids_Lemma, dm_comp_Lemma.
Qed.

Instance hsubst_lemmas_pth : HSubstLemmas vl path.
Proof.
  split; auto using path_ids_Lemma, path_comp_Lemma.
Qed.

Instance hsubst_lemmas_vls : HSubstLemmas vl vls.
Proof.
  split; trivial; intros; rewrite /hsubst;
    induction s; asimpl; by f_equal.
Qed.

Instance hsubst_lemmas_list `{Ids X} `{HSubst vl X} {hsl: HSubstLemmas vl X}: HSubstLemmas vl (list X).
Proof.
  split; trivial; intros; rewrite /hsubst;
    induction s; asimpl; by f_equal.
Qed.

Instance hsubst_lemmas_ctx : HSubstLemmas vl ctx := _.

Instance hsubst_lemmas_list_pair {A} `{Ids X} `{HSubst vl X} {hsl: HSubstLemmas vl X}: HSubstLemmas vl (list (A * X)).
Proof.
  split; trivial; intros; rewrite /hsubst /list_pair_hsubst;
    elim: s => [|[l d] xs IHds] //; asimpl; by f_equal.
Qed.
Instance hsubst_lemmas_dms : HSubstLemmas vl dms := _.
