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

 Instance Ids_tm : Ids tm := λ _, tv (vnat 0).

 Instance Ids_vl : Ids vl.
 Proof. by constructor. Defined.

 Fixpoint tm_rename (sb : var → var) (e : tm) : tm :=
   let a := tm_rename : Rename tm in
   let b := vl_rename : Rename vl in
   match e with
   | tv v => tv (rename sb v)
   | tapp t1 t2 => tapp (rename sb t1) (rename sb t2)
   | tproj t l => (tproj (rename sb t) l)
   | tskip t => tskip (rename sb t)
   end
 with
 vl_rename (sb : var → var) (v : vl) : vl :=
   let a := tm_rename : Rename tm in
   let b := vl_rename : Rename vl in
   match v with
   | var_vl x => var_vl (sb x)
   | vnat n => vnat n
   | vabs t => vabs (rename (upren sb) t)
   | vobj d => vobj (map (dm_rename (upren sb)) d)
   end
 with
 dm_rename (sb : var → var) (d : dm) : dm :=
   let a := vl_rename : Rename vl in
   match d with
   | dtysyn ty => dtysyn (ty_rename sb ty)
   | dtysem lv γ => dtysem (map (rename sb) lv) γ
   | dvl v => dvl (rename sb v)
   end
 with
 ty_rename (sb : var → var) (T : ty) : ty :=
   match T with
   | TTop => TTop
   | TBot => TBot
   | TAnd T1 T2 => TAnd (ty_rename sb T1) (ty_rename sb T2)
   | TOr T1 T2 => TOr (ty_rename sb T1) (ty_rename sb T2)
   | TLater T => TLater (ty_rename sb T)
   | TAll T1 T2 => TAll (ty_rename sb T1) (ty_rename (upren sb) T2)
   | TMu T => TMu (ty_rename (upren sb) T)
   | TVMem l T => TVMem l (ty_rename sb T)
   | TTMem l T1 T2 => TTMem l (ty_rename sb T1) (ty_rename sb T2)
   | TSel pth l => TSel (pth_rename sb pth) l
   | TSelA pth l T1 T2 => TSelA (pth_rename sb pth) l (ty_rename sb T1) (ty_rename sb T2)
   | TNat => TNat
   end
 with
 pth_rename (sb : var → var) (pth : path) : path :=
   let a := vl_rename : Rename vl in
   match pth with
   | pv v => pv (rename sb v)
   | pself pth l => pself (pth_rename sb pth) l
   end.

 Instance Rename_tm : Rename tm := tm_rename.
 Instance Rename_vl : Rename vl := vl_rename.

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
   let a := tm_rename : Rename tm in
   match v with
   | var_vl x => sb x
   | vnat n => vnat n
   | vabs t => vabs (hsubst (up sb) t)
   | vobj d => vobj (map (dm_subst (up sb)) d)
   end
 with
 dm_subst (sb : var → vl) (d : dm) : dm :=
   let b := vl_subst : Subst vl in
   match d with
   | dtysyn ty => dtysyn (ty_subst sb ty)
   | dtysem lv γ => dtysem (map (subst sb) lv) γ
   | dvl v => dvl (subst sb v)
   end
 with
 ty_subst (sb : var → vl) (T : ty) : ty :=
   match T with
   | TTop => TTop
   | TBot => TBot
   | TAnd T1 T2 => TAnd (ty_subst sb T1) (ty_subst sb T2)
   | TOr T1 T2 => TOr (ty_subst sb T1) (ty_subst sb T2)
   | TLater T => TLater (ty_subst sb T)
   | TAll T1 T2 => TAll (ty_subst sb T1) (ty_subst (up sb) T2)
   | TMu T => TMu (ty_subst (up sb) T)
   | TVMem l T => TVMem l (ty_subst sb T)
   | TTMem l T1 T2 => TTMem l (ty_subst sb T1) (ty_subst sb T2)
   | TSel pth l => TSel (pth_subst sb pth) l
   | TSelA pth l T1 T2 => TSelA (pth_subst sb pth) l (ty_subst sb T1) (ty_subst sb T2)
   | TNat => TNat
   end
 with
 pth_subst (sb : var → vl) (pth : path) : path :=
   let b := vl_subst : Subst vl in
   match pth with
   | pv v => pv (subst sb v)
   | pself pth l => pself (pth_subst sb pth) l
   end.

 Instance HSubst_tm : HSubst vl tm := tm_hsubst.
 Instance Subst_vl : Subst vl := vl_subst.

Lemma vl_eq_dec (v1 v2 : vl) : Decision (v1 = v2)
 with
 tm_eq_dec (t1 t2 : tm) : Decision (t1 = t2)
 with
 dm_eq_dec (d1 d2 : dm) : Decision (d1 = d2)
 with
 ty_eq_dec (ty1 ty2 : ty) : Decision (ty1 = ty2)
 with
 pth_eq_dec (pth1 pth2 : path) : Decision (pth1 = pth2).
 Proof.
   - rewrite /Decision; decide equality;
       try (apply tm_eq_dec || apply nat_eq_dec || apply @list_eq_dec); auto.
   - rewrite /Decision; decide equality; try (apply vl_eq_dec || apply nat_eq_dec).
   - rewrite /Decision; decide equality;
       try (apply ty_eq_dec || apply vl_eq_dec || apply @list_eq_dec ||
            apply positive_eq_dec); auto.
   - rewrite /Decision; decide equality;
       try (apply pth_eq_dec || apply nat_eq_dec); auto.
   -  rewrite /Decision; decide equality;
       try (apply vl_eq_dec || apply nat_eq_dec); auto.
 Qed.

 Lemma vl_rename_Lemma (ξ : var → var) (v : vl) : rename ξ v = v.[ren ξ]
 with
 tm_rename_Lemma (ξ : var → var) (t : tm) : rename ξ t = t.|[ren ξ]
 with
 dm_rename_Lemma (ξ : var → var) (d : dm) : dm_rename ξ d = dm_subst (ren ξ) d
 with
 ty_rename_Lemma (ξ : var → var) (T : ty) : ty_rename ξ T = ty_subst (ren ξ) T
 with
 pth_rename_Lemma (ξ : var → var) (pth : path) :
   pth_rename ξ pth = pth_subst (ren ξ) pth.
 Proof.
   - destruct v; simpl; auto.
     + by rewrite tm_rename_Lemma up_upren_internal.
     + f_equal; induction l; simpl; first trivial.
       by rewrite IHl dm_rename_Lemma up_upren_internal.
   - destruct t; simpl; auto;
       try (by rewrite ?vl_rename_Lemma ?tm_rename_Lemma).
   - destruct d; simpl.
     + by rewrite ty_rename_Lemma.
     + f_equal. induction l; simpl; first trivial.
       by rewrite IHl vl_rename_Lemma.
     + by rewrite vl_rename_Lemma.
   - destruct T; simpl; auto;
       by rewrite ?ty_rename_Lemma ?pth_rename_Lemma ?up_upren_internal.
   - induction pth; simpl; auto; by rewrite ?vl_rename_Lemma ?pth_rename_Lemma.
 Qed.

 Lemma vl_ids_Lemma (v : vl) : v.[ids] = v
 with
 tm_ids_Lemma (t : tm) : t.|[ids] = t
 with
 dm_ids_Lemma (d : dm) : dm_subst ids d = d
 with
 ty_ids_Lemma (T : ty) : ty_subst (ids) T = T
 with
 pth_ids_Lemma (pth : path) : pth_subst ids pth = pth.
 Proof.
   - destruct v; simpl; auto.
     + by rewrite up_id_internal // tm_ids_Lemma.
     + f_equal; induction l; simpl; first trivial.
       by rewrite IHl up_id_internal // dm_ids_Lemma.
   - destruct t; simpl; auto; by rewrite ?vl_ids_Lemma ?tm_ids_Lemma.
   - destruct d; simpl.
     + by rewrite ty_ids_Lemma.
     + f_equal. induction l; simpl; first trivial.
       by rewrite IHl vl_ids_Lemma.
     + by rewrite vl_ids_Lemma.
   - destruct T; simpl; auto;
       by rewrite ?ty_ids_Lemma ?up_id_internal // ?ty_ids_Lemma ?pth_ids_Lemma.
   - induction pth; simpl; auto; by rewrite ?vl_ids_Lemma ?pth_ids_Lemma.
 Qed.

 Lemma vl_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (v : vl) :
   (rename ξ v).[σ] = v.[ξ >>> σ]
 with
 tm_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (t : tm) :
   (rename ξ t).|[σ] = t.|[ξ >>> σ]
 with
 dm_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (d : dm) :
   dm_subst σ (dm_rename ξ d) = dm_subst (ξ >>> σ) d
 with
 ty_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (T : ty) :
   ty_subst σ (ty_rename ξ T) = ty_subst (ξ >>> σ) T
 with
 pth_comp_rename_Lemma (ξ : var → var) (σ : var → vl) (pth : path) :
   pth_subst σ (pth_rename ξ pth) = pth_subst (ξ >>> σ) pth.
 Proof.
   - destruct v; simpl; auto.
     + by rewrite tm_comp_rename_Lemma up_comp_ren_subst.
     + f_equal; induction l; simpl; first trivial.
       by rewrite IHl dm_comp_rename_Lemma up_comp_ren_subst.
   - destruct t; simpl; auto;
       by rewrite ?vl_comp_rename_Lemma ?tm_comp_rename_Lemma.
   - destruct d; simpl.
     + by rewrite ty_comp_rename_Lemma.
     + f_equal. induction l; simpl; first trivial.
       by rewrite IHl vl_comp_rename_Lemma.
     + by rewrite vl_comp_rename_Lemma.
   - destruct T; simpl; auto;
       rewrite ?ty_comp_rename_Lemma ?pth_comp_rename_Lemma;
         by try rewrite up_comp_ren_subst.
   - induction pth; simpl; auto;
       by rewrite ?vl_comp_rename_Lemma ?pth_comp_rename_Lemma.
 Qed.

 Lemma vl_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (v : vl) :
   rename ξ v.[σ] = v.[σ >>> rename ξ]
 with
 tm_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (t : tm) :
   rename ξ t.|[σ] = t.|[σ >>> rename ξ]
 with
 dm_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (d : dm) :
   dm_rename ξ (dm_subst σ d) = dm_subst (σ >>> rename ξ) d
 with
 ty_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (T : ty) :
  ty_rename ξ (ty_subst σ T) = ty_subst (σ >>> rename ξ) T
 with
 pth_rename_comp_Lemma (σ : var → vl) (ξ : var → var) (pth : path) :
   pth_rename ξ (pth_subst σ pth) = pth_subst (σ >>> rename ξ) pth.
 Proof.
   - destruct v; simpl; auto.
     + by rewrite tm_rename_comp_Lemma up_comp_subst_ren_internal;
         auto using vl_rename_Lemma, vl_comp_rename_Lemma.
     + f_equal; induction l; simpl; first trivial.
       by rewrite IHl dm_rename_comp_Lemma
                  up_comp_subst_ren_internal;
         auto using vl_rename_Lemma, vl_comp_rename_Lemma.
   - destruct t; simpl; auto;
       by rewrite ?vl_rename_comp_Lemma ?tm_rename_comp_Lemma.
   - destruct d; simpl.
     + by rewrite ty_rename_comp_Lemma.
     + f_equal. induction l; simpl; first trivial.
       by rewrite IHl vl_rename_comp_Lemma.
     + by rewrite vl_rename_comp_Lemma.
   - destruct T; simpl; auto;
       rewrite ?ty_rename_comp_Lemma ?pth_rename_comp_Lemma
               ?up_comp_subst_ren_internal;
       auto using vl_rename_Lemma, vl_comp_rename_Lemma.
   - induction pth; simpl; auto;
       by rewrite ?vl_rename_comp_Lemma ?pth_rename_comp_Lemma.
 Qed.

 Lemma vl_comp_Lemma (σ τ : var → vl) (v : vl) :
   v.[σ].[τ] = v.[σ >> τ]
 with
 tm_comp_Lemma (σ τ : var → vl) (t : tm) :
   t.|[σ].|[τ] = t.|[σ >> τ]
 with
 dm_comp_Lemma (σ τ : var → vl) (d : dm) :
   dm_subst τ (dm_subst σ d) = dm_subst (σ >> τ) d
 with
 ty_comp_Lemma (σ τ : var → vl) (T : ty) :
   ty_subst τ (ty_subst σ T) = ty_subst (σ >> τ) T
 with
 pth_comp_Lemma (σ τ : var → vl) (pth : path) :
   pth_subst τ (pth_subst σ pth) = pth_subst (σ >> τ) pth.
 Proof.
   - destruct v; simpl; auto.
     + by rewrite tm_comp_Lemma up_comp_internal;
         auto using vl_rename_comp_Lemma, vl_comp_rename_Lemma.
     + f_equal; induction l; simpl; first trivial.
       by rewrite IHl dm_comp_Lemma up_comp_internal;
         auto using vl_rename_comp_Lemma, vl_comp_rename_Lemma.
   - destruct t; simpl; auto;
       by rewrite ?vl_comp_Lemma ?tm_comp_Lemma.
   - destruct d; simpl.
     + by rewrite ty_comp_Lemma.
     + f_equal. induction l; simpl; first trivial.
       by rewrite IHl vl_comp_Lemma.
     + by rewrite vl_comp_Lemma.
   - destruct T; simpl; auto;
       rewrite ?ty_comp_Lemma ?pth_comp_Lemma
               ?up_comp_internal;
         auto using vl_rename_comp_Lemma, vl_comp_rename_Lemma.
   - induction pth; simpl; auto;
       by rewrite ?vl_comp_Lemma ?pth_comp_Lemma.
 Qed.

 Instance SubstLemmas_tm : SubstLemmas vl.
 Proof.
   split; auto using vl_rename_Lemma, vl_ids_Lemma, vl_comp_Lemma.
 Qed.

 Instance HSubstLemmas_tm : HSubstLemmas vl tm.
 Proof.
   split; auto using tm_ids_Lemma, tm_comp_Lemma.
 Qed.
