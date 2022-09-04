From D.Dot Require Import syn.

Set Primitive Projections.
Set Implicit Arguments.

Implicit Types
         (S T U : ty) (v : vl) (e t : tm) (p : path) (d : dm) (ds : dms) (vs : vls)
         (Γ : ctx).

Module Trav1.
Record Traversal {travStateT : Type} :=
  {
    upS : travStateT → travStateT;
    underPathElimS : travStateT → travStateT;
    varP : travStateT → nat → Prop;
    dtysynP : travStateT → ty → Prop;
    dtysemP : travStateT → vls → stamp → ty → travStateT → Prop;
    pathRootP : travStateT → vl → Prop;
  }.

#[global] Arguments Traversal _ : clear implicits.

Section fold.
  Context `(trav : Traversal travStateT).
  Implicit Types (ts : travStateT) (s : stamp).

  Inductive forall_traversal_vl : travStateT → vl → Prop :=
  | trav_vvar ts i : trav.(varP) ts i → forall_traversal_vl ts (vvar i)
  | trav_vabs ts t : forall_traversal_tm (trav.(upS) ts) t →
                    forall_traversal_vl ts (vabs t)
  | trav_vlit ts l : forall_traversal_vl ts (vlit l)
  | trav_vobj ts ds : Forall (forall_traversal_dm (trav.(upS) ts)) (map snd ds) →
                      forall_traversal_vl ts (vobj ds)
  with
  forall_traversal_tm : travStateT → tm → Prop :=
  | trav_tv ts v : forall_traversal_vl ts v → forall_traversal_tm ts (tv v)
  | trav_tapp ts t1 t2 :
      forall_traversal_tm ts t1 →
      forall_traversal_tm ts t2 →
      forall_traversal_tm ts (tapp t1 t2)
  | trav_tproj ts t l :
      forall_traversal_tm ts t →
      forall_traversal_tm ts (tproj t l)
  | trav_tskip ts t :
      forall_traversal_tm ts t →
      forall_traversal_tm ts (tskip t)
  | trav_tun ts u t :
      forall_traversal_tm ts t →
      forall_traversal_tm ts (tun u t)
  | trav_tbin ts b t1 t2 :
      forall_traversal_tm ts t1 →
      forall_traversal_tm ts t2 →
      forall_traversal_tm ts (tbin b t1 t2)
  | trav_tif ts t1 t2 t3 :
      forall_traversal_tm ts t1 →
      forall_traversal_tm ts t2 →
      forall_traversal_tm ts t3 →
      forall_traversal_tm ts (tif t1 t2 t3)
  with
  forall_traversal_dm : travStateT → dm → Prop :=
  | trav_dpt ts p :
      forall_traversal_path ts p →
      forall_traversal_dm ts (dpt p)
  | trav_dtysyn ts T :
      forall_traversal_ty ts T →
      trav.(dtysynP) ts T →
      forall_traversal_dm ts (dtysyn T)
  | trav_dtysem ts vs s T' ts' :
      trav.(dtysemP) ts vs s T' ts' →
      forall_traversal_ty ts' T' →
      Forall (forall_traversal_vl ts) vs →
      forall_traversal_dm ts (dtysem vs s)
  with
  forall_traversal_path : travStateT → path → Prop :=
  | trav_pv ts v :
    forall_traversal_vl ts v →
    trav.(pathRootP) ts v →
    forall_traversal_path ts (pv v)
  | trav_pself ts p l :
    forall_traversal_path (trav.(underPathElimS) ts) p →
    forall_traversal_path ts (pself p l)
  with
  forall_traversal_ty : travStateT → ty → Prop :=
  | trav_TTop ts : forall_traversal_ty ts TTop
  | trav_TBot ts : forall_traversal_ty ts TBot
  | trav_TAnd ts T1 T2 :
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts T2 →
      forall_traversal_ty ts (TAnd T1 T2)
  | trav_TOr ts T1 T2 :
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts T2 →
      forall_traversal_ty ts (TOr T1 T2)
  | trav_TLater ts T1 :
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts (TLater T1)
  | trav_TAll ts T1 T2 :
      forall_traversal_ty ts T1 →
      forall_traversal_ty (trav.(upS) ts) T2 →
      forall_traversal_ty ts (TAll T1 T2)
  | trav_TMu ts T1 :
      forall_traversal_ty (trav.(upS) ts) T1 →
      forall_traversal_ty ts (TMu T1)
  | trav_TVMem ts l T1 :
      forall_traversal_ty ts T1 →
      forall_traversal_ty ts (TVMem l T1)
  | trav_kTTMem ts l K :
      forall_traversal_kind ts K →
      forall_traversal_ty ts (kTTMem l K)
  | trav_kTSel ts n p l :
      forall_traversal_path (trav.(underPathElimS) ts) p →
      forall_traversal_ty ts (kTSel n p l)
  | trav_TPrim ts b : forall_traversal_ty ts (TPrim b)
  | trav_TSing ts p :
      forall_traversal_path (trav.(underPathElimS) ts) p →
      forall_traversal_ty ts (TSing p)
  with forall_traversal_kind : travStateT → kind → Prop :=
  | trav_kintv ts L U :
      forall_traversal_ty ts L →
      forall_traversal_ty ts U →
      forall_traversal_kind ts (kintv L U)
  | trav_kpi ts S K :
      forall_traversal_ty ts S →
      forall_traversal_kind (trav.(upS) ts) K →
      forall_traversal_kind ts (kpi S K)
    .
End fold.

#[global] Arguments upS /.
#[global] Arguments varP /.
#[global] Arguments dtysynP /.
#[global] Arguments dtysemP /.
#[global] Arguments pathRootP /.

Notation forall_traversal_dms trav ts ds := (Forall (forall_traversal_dm trav ts) (map snd ds)).
#[global] Hint Constructors forall_traversal_vl forall_traversal_tm forall_traversal_dm
     forall_traversal_path forall_traversal_ty forall_traversal_kind : core.

(* No such Hint Extern for [upS] since it can't be the head of a goal. *)
#[global] Hint Extern 0 (varP _ _ _)      => progress cbn : core.
#[global] Hint Extern 0 (dtysynP _ _ _)   => progress cbn : core.
#[global] Hint Extern 0 (dtysemP _ _ _)   => progress cbn : core.
#[global] Hint Extern 0 (pathRootP _ _ _) => progress cbn : core.

#[global] Hint Extern 0 (forall_traversal_tm _ _ _)   => progress cbn : core.
#[global] Hint Extern 0 (forall_traversal_vl _ _ _)   => progress cbn : core.
#[global] Hint Extern 0 (forall_traversal_dm _ _ _)   => progress cbn : core.
#[global] Hint Extern 0 (forall_traversal_path _ _ _) => progress cbn : core.
#[global] Hint Extern 0 (forall_traversal_ty _ _ _)   => progress cbn : core.
#[global] Hint Extern 0 (forall_traversal_kind _ _ _)   => progress cbn : core.

(** Tactics to invert uses of [forall_traversal_*]. *)

(** Use [inverse] on [H], but only if it produces at most one goal, and mark
[H] as used. *)
Ltac inverse_once H := nosplit (try_once_tac H (inverse H)).

(** Using cbn exposes further assumption of form is_{un,}stamped, allowing for
further inversions. *)
Ltac inverse_once_cbn H := nosplit (try_once_tac H (inverse H)); cbn in *.

(** Apply [tac] to _one_ hypothesis of shape [forall_traversal_* trav _ _]. *)
Ltac with_forall_traversal trav tac :=
  match goal with
    | H : forall_traversal_tm   trav _ _ |- _ => tac H
    | H : forall_traversal_vl   trav _ _ |- _ => tac H
    | H : forall_traversal_dm   trav _ _ |- _ => tac H
    | H : forall_traversal_path trav _ _ |- _ => tac H
    | H : forall_traversal_ty   trav _ _ |- _ => tac H
    | H : forall_traversal_kind trav _ _ |- _ => tac H
  end.
(** Invert once each hypothesis of shape [forall_traversal_* trav _ _], as
long as inversion only produces a single result. *)
Ltac inverse_forall_traversal trav :=
  (repeat with_forall_traversal trav inverse_once_cbn); un_usedLemma.

End Trav1.

Definition tmemc : Type := ty + vls * stamp.
Definition tmemc2dm : tmemc → dm := λ tm,
  match tm with
  | inl T => dtysyn T
  | inr (vs, s) => dtysem vs s
  end.
Definition dm2tmemc : dm → option tmemc := λ d,
  match d with
  | dtysyn T => Some (inl T)
  | dtysem vs s => Some (inr (vs, s))
  | _ => None
  end.
Definition fold_tmemc : (ty → Prop) → (vls → Prop) → tmemc → Prop :=
  λ tyP vlsP tm,
  match tm with
  | inl T => tyP T
  | inr (vs, s) => vlsP vs
  end.
