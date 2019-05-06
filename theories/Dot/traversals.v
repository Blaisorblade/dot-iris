From stdpp Require Import list.
From D Require Import tactics.
From D.Dot Require Import syn operational.

Set Primitive Projections.
Set Implicit Arguments.

Implicit Types
         (S T U: ty) (v: vl) (e t u: tm) (p: path) (d: dm) (ds: dms) (vs: vls)
         (Γ : ctx) (n: nat).

Module Trav1.
Record Traversal {travStateT: Type} :=
  {
    upS: travStateT → travStateT;
    varP: travStateT → nat → Prop;
    dtysynP: travStateT → ty → Prop;
    dtysemP: travStateT → vls → stamp → Prop;
  }.

Global Arguments Traversal _: clear implicits.

Section fold.
  Context `(trav: Traversal travStateT).

  Inductive forall_traversal_vl: travStateT → vl → Prop :=
  | trav_var_vl ts i: trav.(varP) ts i → forall_traversal_vl ts (var_vl i)
  | trav_vabs ts t: forall_traversal_tm (trav.(upS) ts) t →
                    forall_traversal_vl ts (vabs t)
  | trav_vnat ts n: forall_traversal_vl ts (vnat n)
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
  with
  forall_traversal_dm: travStateT → dm → Prop :=
  | trav_dvl ts v:
      forall_traversal_vl ts v →
      forall_traversal_dm ts (dvl v)
  | trav_dtysyn ts T:
      forall_traversal_ty ts T →
      trav.(dtysynP) ts T →
      forall_traversal_dm ts (dtysyn T)
  | trav_dtysem ts vs s:
      trav.(dtysemP) ts vs s →
      Forall (forall_traversal_vl ts) vs →
      forall_traversal_dm ts (dtysem vs s)
  with
  forall_traversal_path: travStateT → path → Prop :=
  | trav_pv ts v:
    forall_traversal_vl ts v →
    forall_traversal_path ts (pv v)
  | trav_pself ts p l:
    forall_traversal_path ts p →
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
      forall_traversal_path ts p →
      forall_traversal_ty ts (TSel p l)
  | trav_TNat ts: forall_traversal_ty ts TNat
    .
End fold.

Global Arguments upS /.
Global Arguments varP /.
Global Arguments dtysynP /.
Global Arguments dtysemP /.

Global Hint Constructors forall_traversal_vl forall_traversal_tm forall_traversal_dm
     forall_traversal_path forall_traversal_ty.
End Trav1.
