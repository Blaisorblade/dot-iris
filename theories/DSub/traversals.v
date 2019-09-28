From stdpp Require Import list.
From D Require Import tactics.
From D.DSub Require Import syn.

Set Primitive Projections.
Set Implicit Arguments.

Implicit Types (T: ty) (v: vl) (e: tm) (Γ : ctx) (n: nat).

Module Trav1.
Record Traversal {travStateT: Type} :=
  {
    upS: travStateT → travStateT;
    varP: travStateT → nat → Prop;
    vtyP: travStateT → ty → Prop;
    vstampP: travStateT → vls → stamp → Prop;
    tselP: travStateT → vl → Prop;
  }.

Global Arguments Traversal _: clear implicits.

Section fold.
  Context `(trav: Traversal travStateT).

  Inductive forall_traversal_vl: travStateT → vl → Prop :=
  | trav_var_vl ts i: trav.(varP) ts i → forall_traversal_vl ts (var_vl i)
  | trav_vabs ts t: forall_traversal_tm (trav.(upS) ts) t →
                    forall_traversal_vl ts (vabs t)
  | trav_vnat ts n: forall_traversal_vl ts (vnat n)
  | trav_vty ts T:
      forall_traversal_ty ts T →
      trav.(vtyP) ts T →
      forall_traversal_vl ts (vty T)
  | trav_vstamp ts vs s:
      trav.(vstampP) ts vs s →
      Forall (forall_traversal_vl ts) vs →
      forall_traversal_vl ts (vstamp vs s)
  with
  forall_traversal_tm: travStateT → tm → Prop :=
  | trav_tv ts v: forall_traversal_vl ts v → forall_traversal_tm ts (tv v)
  | trav_tapp ts t1 t2:
      forall_traversal_tm ts t1 →
      forall_traversal_tm ts t2 →
      forall_traversal_tm ts (tapp t1 t2)
  | trav_tskip ts t:
      forall_traversal_tm ts t →
      forall_traversal_tm ts (tskip t)
  with
  forall_traversal_ty: travStateT → ty → Prop :=
  | trav_TTop ts: forall_traversal_ty ts TTop
  | trav_TBot ts: forall_traversal_ty ts TBot
  | trav_TLater ts T1:
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts (TLater T1)
  | trav_TAll ts T1 T2:
      forall_traversal_ty ts T1 →
      forall_traversal_ty (trav.(upS) ts) T2 →
      forall_traversal_ty ts (TAll T1 T2)
  | trav_TMem ts T1 T2:
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts T2 →
      forall_traversal_ty ts (TTMem T1 T2)
  | trav_TSel ts v:
      forall_traversal_vl ts v →
      trav.(tselP) ts v →
      forall_traversal_ty ts (TSel v)
  | trav_TNat ts: forall_traversal_ty ts TNat
    .
End fold.

Global Arguments upS /.
Global Arguments varP /.
Global Arguments vtyP /.
Global Arguments vstampP /.
Global Arguments tselP /.

Global Hint Constructors forall_traversal_vl forall_traversal_ty forall_traversal_tm.

Global Hint Extern 0 (varP _ _ _) => cbn.
Global Hint Extern 0 (vtyP _ _ _) => cbn.
Global Hint Extern 0 (vstampP _ _ _) => cbn.
Global Hint Extern 0 (tselP _ _ _) => cbn.
End Trav1.

Definition tmemc: Type := ty + vls * stamp.
Definition tmemc2vl: tmemc → vl := λ tm,
  match tm with
  | inl T => vty T
  | inr (vs, s) => vstamp vs s
  end.
Definition vl2tmemc: vl → option tmemc := λ d,
  match d with
  | vty T => Some (inl T)
  | vstamp vs s => Some (inr (vs, s))
  | _ => None
  end.
Definition fold_tmemc: (ty → Prop) → (vls → Prop) → tmemc → Prop :=
  λ tyP vlsP tm,
  match tm with
  | inl T => tyP T
  | inr (vs, s) => vlsP vs
  end.
