From D.Dot Require Import syn.

Set Primitive Projections.
Set Implicit Arguments.

Set Suggest Proof Using.
Set Default Proof Using "Type".

Implicit Types
         (S T U: ty) (v: vl) (e t: tm) (p: path) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx).

Module Trav1.
Record Traversal {travStateT: Type} :=
  {
    upS: travStateT → travStateT;
    underPathElimS: travStateT → travStateT;
    varP: travStateT → nat → Prop;
    dtysynP: travStateT → ty → Prop;
    dtysemP: travStateT → vls → stamp → ty → travStateT → Prop;
    pathRootP: travStateT → vl → Prop;
  }.

Global Arguments Traversal _: clear implicits.

Section fold.
  Context `(trav: Traversal travStateT).
  Implicit Types (ts: travStateT) (s: stamp).

  Inductive forall_traversal_vl: travStateT → vl → Prop :=
  | trav_var_vl ts i: trav.(varP) ts i → forall_traversal_vl ts (var_vl i)
  | trav_vabs ts t: forall_traversal_tm (trav.(upS) ts) t →
                    forall_traversal_vl ts (vabs t)
  | trav_vlit ts l: forall_traversal_vl ts (vlit l)
  | trav_vobj ts ds : Forall (forall_traversal_dm (trav.(upS) ts)) (map snd ds) →
                      forall_traversal_vl ts (vobj ds)
  with
  forall_traversal_tm: travStateT → tm → Prop :=
  | trav_tv ts v: forall_traversal_vl ts v → forall_traversal_tm ts (tv v)
  | trav_tapp ts t1 t2:
      forall_traversal_tm ts t1 →
      forall_traversal_tm ts t2 →
      forall_traversal_tm ts (tapp t1 t2)
  | trav_tproj ts t l:
      forall_traversal_tm ts t →
      forall_traversal_tm ts (tproj t l)
  | trav_tskip ts t:
      forall_traversal_tm ts t →
      forall_traversal_tm ts (tskip t)
  | trav_tun ts u t:
      forall_traversal_tm ts t →
      forall_traversal_tm ts (tun u t)
  | trav_tbin ts b t1 t2:
      forall_traversal_tm ts t1 →
      forall_traversal_tm ts t2 →
      forall_traversal_tm ts (tbin b t1 t2)
  | trav_tif ts t1 t2 t3:
      forall_traversal_tm ts t1 →
      forall_traversal_tm ts t2 →
      forall_traversal_tm ts t3 →
      forall_traversal_tm ts (tif t1 t2 t3)
  with
  forall_traversal_dm: travStateT → dm → Prop :=
  | trav_dpt ts p:
      forall_traversal_path ts p →
      forall_traversal_dm ts (dpt p)
  | trav_dtysyn ts T:
      forall_traversal_ty ts T →
      trav.(dtysynP) ts T →
      forall_traversal_dm ts (dtysyn T)
  | trav_dtysem ts vs s T' ts':
      trav.(dtysemP) ts vs s T' ts' →
      forall_traversal_ty ts' T' →
      Forall (forall_traversal_vl ts) vs →
      forall_traversal_dm ts (dtysem vs s)
  with
  forall_traversal_path: travStateT → path → Prop :=
  | trav_pv ts v:
    forall_traversal_vl ts v →
    trav.(pathRootP) ts v →
    forall_traversal_path ts (pv v)
  | trav_pself ts p l:
    forall_traversal_path (trav.(underPathElimS) ts) p →
    forall_traversal_path ts (pself p l)
  with
  forall_traversal_ty: travStateT → ty → Prop :=
  | trav_TTop ts: forall_traversal_ty ts TTop
  | trav_TBot ts: forall_traversal_ty ts TBot
  | trav_TAnd ts T1 T2:
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts T2 →
      forall_traversal_ty ts (TAnd T1 T2)
  | trav_TOr ts T1 T2:
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts T2 →
      forall_traversal_ty ts (TOr T1 T2)
  | trav_TLater ts T1:
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts (TLater T1)
  | trav_TAll ts T1 T2:
      forall_traversal_ty ts T1 →
      forall_traversal_ty (trav.(upS) ts) T2 →
      forall_traversal_ty ts (TAll T1 T2)
  | trav_TMu ts T1:
      forall_traversal_ty (trav.(upS) ts) T1 →
      forall_traversal_ty ts (TMu T1)
  | trav_TVMem ts l T1:
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts (TVMem l T1)
  | trav_TTMem ts l T1 T2:
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts T2 →
      forall_traversal_ty ts (TTMem l T1 T2)
  | trav_TSel ts p l:
      forall_traversal_path (trav.(underPathElimS) ts) p →
      forall_traversal_ty ts (TSel p l)
  | trav_TSing ts p:
      forall_traversal_path (trav.(underPathElimS) ts) p →
      forall_traversal_ty ts (TSing p)
  | trav_TPrim ts b: forall_traversal_ty ts (TPrim b)
    .
End fold.

Global Arguments upS /.
Global Arguments varP /.
Global Arguments dtysynP /.
Global Arguments dtysemP /.
Global Arguments pathRootP /.

Notation forall_traversal_dms trav ts ds := (Forall (forall_traversal_dm trav ts) (map snd ds)).
Global Hint Constructors forall_traversal_vl forall_traversal_tm forall_traversal_dm
     forall_traversal_path forall_traversal_ty : core.

(* No such Hint Extern for [upS] since it can't be the head of a goal. *)
Global Hint Extern 0 (varP _ _ _)      => progress cbn : core.
Global Hint Extern 0 (dtysynP _ _ _)   => progress cbn : core.
Global Hint Extern 0 (dtysemP _ _ _)   => progress cbn : core.
Global Hint Extern 0 (pathRootP _ _ _) => progress cbn : core.
End Trav1.

Definition tmemc: Type := ty + vls * stamp.
Definition tmemc2dm: tmemc → dm := λ tm,
  match tm with
  | inl T => dtysyn T
  | inr (vs, s) => dtysem vs s
  end.
Definition dm2tmemc: dm → option tmemc := λ d,
  match d with
  | dtysyn T => Some (inl T)
  | dtysem vs s => Some (inr (vs, s))
  | _ => None
  end.
Definition fold_tmemc: (ty → Prop) → (vls → Prop) → tmemc → Prop :=
  λ tyP vlsP tm,
  match tm with
  | inl T => tyP T
  | inr (vs, s) => vlsP vs
  end.
