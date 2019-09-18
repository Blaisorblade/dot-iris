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
    tselP: travStateT → path → Prop;
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
      trav.(tselP) ts p →
      forall_traversal_ty ts (TSel p l)
  | trav_TNat ts: forall_traversal_ty ts TNat
    .
End fold.

Global Arguments upS /.
Global Arguments varP /.
Global Arguments dtysynP /.
Global Arguments dtysemP /.
Global Arguments tselP /.

Global Hint Constructors forall_traversal_vl forall_traversal_tm forall_traversal_dm
     forall_traversal_path forall_traversal_ty.

Global Hint Extern 0 (tselP _ _ _) => cbn.
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

Module Traversal2.
Record Traversal {travStateT: Type} :=
  {
    upS: travStateT → travStateT;
    varP: travStateT → nat → nat → Prop;
    dtyP: travStateT → tmemc → tmemc → Prop;
  }.
Global Arguments Traversal _: clear implicits.
Global Arguments upS /.
Global Arguments varP /.
Global Arguments dtyP /.
End Traversal2.

Module Trav2.
Export Traversal2.

Section fold.
  Context `(trav: Traversal travStateT).

  Inductive forall_traversal_vl: travStateT → vl → vl → Prop :=
  | trav_var_vl ts i1 i2 :
      trav.(varP) ts i1 i2 →
      forall_traversal_vl ts (var_vl i1) (var_vl i2)
  | trav_vabs ts t1 t2:
      forall_traversal_tm (trav.(upS) ts) t1 t2 →
      forall_traversal_vl ts (vabs t1) (vabs t2)
  | trav_vnat ts n: forall_traversal_vl ts (vnat n) (vnat n)
  | trav_vobj ts ds1 ds2:
      Forall2 (=) (map fst ds1) (map fst ds2) →
      Forall2 (forall_traversal_dm (trav.(upS) ts)) (map snd ds1) (map snd ds2) →
      forall_traversal_vl ts (vobj ds1) (vobj ds2)
  with
  forall_traversal_tm: travStateT → tm → tm → Prop :=
  | trav_tv ts v1 v2:
      forall_traversal_vl ts v1 v2 →
      forall_traversal_tm ts (tv v1) (tv v2)
  | trav_tapp ts t1 t2 u1 u2:
      forall_traversal_tm ts t1 t2 →
      forall_traversal_tm ts u1 u2 →
      forall_traversal_tm ts (tapp t1 u1) (tapp t2 u2)
  | trav_tproj ts t1 t2 l:
      forall_traversal_tm ts t1 t2 →
      forall_traversal_tm ts (tproj t1 l) (tproj t2 l)
  | trav_tskip ts t1 t2:
      forall_traversal_tm ts t1 t2 →
      forall_traversal_tm ts (tskip t1) (tskip t2)
  with
  forall_traversal_dm: travStateT → dm → dm → Prop :=
  | trav_dvl ts v1 v2:
      forall_traversal_vl ts v1 v2 →
      forall_traversal_dm ts (dvl v1) (dvl v2)
  | trav_dty ts tm1 tm2:
      (* forall_traversal_ty ts T → *)
      trav.(dtyP) ts tm1 tm2 →
      forall_traversal_dm ts (tmemc2dm tm1) (tmemc2dm tm2)
  (* | trav_dtysem ts vs s:
      trav.(dtysemP) ts vs s →
      Forall (forall_traversal_vl ts) vs →
      forall_traversal_dm ts (dtysem vs s) *)
  with
  forall_traversal_path: travStateT → path → path → Prop :=
  | trav_pv ts v1 v2:
    forall_traversal_vl ts v1 v2 →
    forall_traversal_path ts (pv v1) (pv v2)
  | trav_pself ts p1 p2 l:
    forall_traversal_path ts p1 p2 →
    forall_traversal_path ts (pself p1 l) (pself p2 l)
  with
  forall_traversal_ty: travStateT → ty → ty → Prop :=
  | trav_TTop ts: forall_traversal_ty ts TTop TTop
  | trav_TBot ts: forall_traversal_ty ts TBot TBot
  | trav_TAnd ts T1 T2 U1 U2:
      forall_traversal_ty ts T1 T2 →
      forall_traversal_ty ts U1 U2 →
      forall_traversal_ty ts (TAnd T1 U1) (TAnd T2 U2)
  | trav_TOr ts T1 T2 U1 U2:
      forall_traversal_ty ts T1 T2 →
      forall_traversal_ty ts U1 U2 →
      forall_traversal_ty ts (TOr T1 U1) (TOr T2 U2)
  | trav_TLater ts T1 T2:
      forall_traversal_ty ts T1 T2 →
      forall_traversal_ty ts (TLater T1) (TLater T2)
  | trav_TAll ts T1 T2 U1 U2:
      forall_traversal_ty ts T1 T2 →
      forall_traversal_ty (trav.(upS) ts) U1 U2 →
      forall_traversal_ty ts (TAll T1 U1) (TAll T2 U2)
  | trav_TMu ts T1 T2:
      forall_traversal_ty (trav.(upS) ts) T1 T2 →
      forall_traversal_ty ts (TMu T1) (TMu T2)
  | trav_TVMem ts l T1 T2:
      forall_traversal_ty ts T1 T2 →
      forall_traversal_ty ts (TVMem l T1) (TVMem l T2)
  | trav_TTMem ts l T1 T2 U1 U2:
      forall_traversal_ty ts T1 T2 →
      forall_traversal_ty ts U1 U2 →
      forall_traversal_ty ts (TTMem l T1 U1) (TTMem l T2 U2)
  | trav_TSel ts p1 p2 l:
      forall_traversal_path ts p1 p2 →
      forall_traversal_ty ts (TSel p1 l) (TSel p2 l)
  | trav_TNat ts: forall_traversal_ty ts TNat TNat.

  Definition forall_traversal_dms: travStateT → dms → dms → Prop :=
    λ ts ds1 ds2,
    Forall2 (=) (map fst ds1) (map fst ds2) ∧
    Forall2 (forall_traversal_dm (trav.(upS) ts)) (map snd ds1) (map snd ds2).
End fold.

Global Hint Constructors forall_traversal_vl forall_traversal_tm forall_traversal_dm
     forall_traversal_path forall_traversal_ty.
End Trav2.

Module Trav2_recursive.
Export Traversal2.

Section fold.
  Context `(trav: Traversal travStateT).

  Fixpoint forall_traversal_tm (ts : travStateT) (t1 t2 : tm) {struct t1} : Prop :=
    match (t1, t2) with
    | (tv v1, tv v2) => forall_traversal_vl ts v1 v2
    | (tapp t11 t12, tapp t21 t22) =>
      forall_traversal_tm ts t11 t21 ∧ forall_traversal_tm ts t12 t22
    | (tproj t1 l1, tproj t2 l2) =>
      forall_traversal_tm ts t1 t2 ∧ l1 = l2
    | (tskip t1, tskip t2) =>
      forall_traversal_tm ts t1 t2
    | _ => False
    end
  with
  forall_traversal_vl (ts : travStateT) (v1 v2: vl) {struct v1} : Prop :=
    match (v1, v2) with
    | (var_vl i1, var_vl i2) => trav.(varP) ts i1 i2
    | (vabs t1, vabs t2) => forall_traversal_tm (trav.(upS) ts) t1 t2
    | (vobj ds1, vobj ds2) =>
      let fix forall_traversal_dms (ts : travStateT) (ds1 ds2: dms): Prop :=
          match (ds1, ds2) with
          | (nil, nil) => True
          | (cons (l1, d1) ds1, cons (l2, d2) ds2) =>
            l1 = l2 ∧ forall_traversal_dm ts d1 d2 ∧ forall_traversal_dms ts ds1 ds2
          | _ => False
          end
      in forall_traversal_dms (trav.(upS) ts) ds1 ds2
    | (vnat n1, vnat n2) => n1 = n2
    | _ => False
    end
  with
  forall_traversal_dm (ts : travStateT) (d1 d2: dm) {struct d1} : Prop :=
    match (d1, d2) with
    | (dvl v1, dvl v2) => forall_traversal_vl ts v1 v2
    | (dvl _, _) => False
    | (_, dvl _) => False
    | (_, _) =>
      default False (f ← trav.(dtyP) ts <$> (dm2tmemc d1); f <$> (dm2tmemc d2))
    end.
  Fixpoint forall_traversal_path (ts : travStateT) (p1 p2: path): Prop :=
    match (p1, p2) with
    | (pv v1, pv v2) => forall_traversal_vl ts v1 v2
    | (pself p1 l1, pself p2 l2) => forall_traversal_path ts p1 p2 ∧ l1 = l2
    | _ => False
    end.
  Fixpoint forall_traversal_ty (ts : travStateT) (T1 T2: ty): Prop :=
    match (T1, T2) with
    | (TTop, TTop) => True
    | (TBot, TBot) => True
    | (TAnd T11 T12, TAnd T21 T22) =>
      forall_traversal_ty ts T11 T21 ∧ forall_traversal_ty ts T12 T22
    | (TOr T11 T12, TOr T21 T22) =>
      forall_traversal_ty ts T11 T21 ∧ forall_traversal_ty ts T12 T22
    | (TLater T1, TLater T2) =>
      forall_traversal_ty ts T1 T2
    | (TAll T11 T12, TAll T21 T22) =>
      forall_traversal_ty ts T11 T21 ∧ forall_traversal_ty (trav.(upS) ts) T12 T22
    | (TMu T1, TMu T2) =>
      forall_traversal_ty (trav.(upS) ts) T1 T2
    | (TVMem l1 T1, TVMem l2 T2) => l1 = l2 ∧ forall_traversal_ty ts T1 T2
    | (TTMem l1 T11 T12, TTMem l2 T21 T22) =>
      l1 = l2 ∧ forall_traversal_ty ts T11 T21 ∧ forall_traversal_ty ts T12 T22
    | (TSel p1 l1, TSel p2 l2) => forall_traversal_path ts p1 p2 ∧ l1 = l2
    | (TNat, TNat) => True
    | _ => False
    end.
End fold.
End Trav2_recursive.
