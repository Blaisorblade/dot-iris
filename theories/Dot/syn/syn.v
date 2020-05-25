(**
* gDOT syntax and operational semantics.
Follows Sec. 2; implemented using de Bruijn indexes and the Autosubst 1
infrastructure.
The operational semantics implements the Iris infrastructure for languages,
using contextual small-step operational semantics.
*)
From stdpp Require Export strings.
From D Require Export prelude.
From D Require Import asubst_intf asubst_base.
From iris.program_logic Require ectx_language ectxi_language.

Set Suggest Proof Using.
Set Default Proof Using "Type*".

(**
This module is included right away, but it asserts explicitly
that it implements our language interface [VlSortsFullSig].
*)
Module Export VlSorts <: VlSortsFullSig.
Import ASubstLangDefUtils.

(** Type of labels; we use a single type for both term labels [a] and type
labels [A]. *)
Definition label := string.

(** Syntax of primitive literals, operations and types. *)
Inductive base_lit : Set := lint (n : Z) | lbool (b : bool).
Inductive un_op : Set := unot.
Inductive bin_op : Set := bplus | bminus | btimes | bdiv | blt | ble | beq.
Inductive base_ty : Set := tint | tbool.

(** ** DOT syntax, with corresponding on-paper syntax in comments. *)
(** Expressions/terms [e ::= ]: *)
Inductive tm : Type :=
  | tv : vl_ → tm (* inject values into terms [v]; *)
  | tapp : tm → tm → tm (* application [e e]; *)
  | tproj : tm → label → tm (* projections [e.a]; *)
  | tskip : tm → tm (* coercions [coerce e]. *)
  (** Primitive terms. *)
  | tun : un_op → tm → tm (* unary operation; *)
  | tbin : bin_op → tm → tm → tm (* binary operation; *)
  | tif : tm → tm → tm → tm (* if conditional. *)
 (** Values [v ::=]: *)
 with vl_ : Type :=
  | var_vl : var → vl_ (* variables [x]. *)
  | vlit : base_lit → vl_ (* literals (not in paper) *)
  | vabs : tm → vl_ (* lambdas [λ x. t] *)
  | vobj : list (label * dm) → vl_ (* objects [ν x. t]. *)
 (** Definition bodies [d ::= ]: *)
 with dm : Type :=
  | dtysyn : ty → dm (* unstamped type definition [T]; *)
  | dtysem : list vl_ → stamp → dm (* stamped type definition [σ, s]; *)
  | dpt : path → dm (* path definition [p]. *)
 (** Paths [p ::= ] *)
 with path : Type :=
  | pv : vl_ → path (* values [v]; *)
  | pself : path → label → path (* path selection [p.a]. *)
 (** Types [L, S, T, U, V, W ::= ] *)
 with ty : Type :=
  | TTop : ty (* top type [⊤]; *)
  | TBot : ty (* bottom type [⊤]; *)
  | TAnd : ty → ty → ty (* intersection type [S ∧ T]; *)
  | TOr : ty → ty → ty (* union type [S ∨ T]; *)
  | TLater : ty → ty (* later type [▷ T]; *)
  | TAll : ty → ty → ty (* forall type [∀ x: S. T]; *)
  | TMu : ty → ty (* mu-types [μ x. T]; *)
  | TVMem : label → ty → ty (* value members [{a: T}];*)
  | TTMem : label → ty → ty → ty (* type members [{A :: L .. U}]; *)
  | TSel : path → label → ty (* type selections [p.A]; *)
  | TPrim : base_ty → ty (* primitive types *)
  | TSing : path → ty (* singleton types [p.type].*).

(* Workaround Coq bug with modules. *)
Definition vl := vl_.

(* Shortcuts. *)
Notation TInt := (TPrim tint).
Notation TBool := (TPrim tbool).
Notation vint n := (vlit $ lint n).
Notation vbool b := (vlit $ lbool b).
(* Adapter over TTMem. [L] stands for Later. *)
Definition TTMemL l L U := TTMem l (TLater L) (TLater U).

(** Definition lists [\overbar{d}]. *)
Definition dms := list (label * dm).
(** Typing contexts [Γ]. *)
Definition ctx := list ty.

Declare Scope dms_scope.
Declare Scope ty_scope.
Bind Scope dms_scope with dms.
Bind Scope ty_scope with ty.
Delimit Scope ty_scope with ty.
Delimit Scope dms_scope with dms.

(******************************************************************************)
(** Substitution. *)
(******************************************************************************)

Implicit Types
         (T : ty) (v : vl) (t : tm) (d : dm) (ds : dms) (p : path)
         (Γ : ctx) (l : label).

Instance inh_ty : Inhabited ty := populate TInt.
Instance inh_base_lit : Inhabited base_lit := populate (lint 0).
Instance inh_vl : Inhabited vl := populate (vlit inhabitant).
Instance inh_pth : Inhabited path := populate (pv inhabitant).
Instance inh_dm : Inhabited dm := populate (dpt inhabitant).
Instance inh_tm : Inhabited tm := populate (tv inhabitant).

Instance ids_vl : Ids vl := var_vl.

Instance inj_ids : Inj (=) (=@{vl}) ids.
Proof. by move=>??[]. Qed.

Instance ids_tm : Ids tm := inh_ids.
Instance ids_dm : Ids dm := inh_ids.
Instance ids_pth : Ids path := inh_ids.
Instance ids_ty : Ids ty := inh_ids.
Instance ids_dms : Ids dms := _.
Instance ids_ctx : Ids ctx := _.

Fixpoint tm_rename (sb : var → var) t : tm :=
  let a := tm_rename : Rename tm in
  let b := vl_rename : Rename vl in
  match t with
  | tv v => tv (rename sb v)
  | tapp t1 t2 => tapp (rename sb t1) (rename sb t2)
  | tproj t l => (tproj (rename sb t) l)
  | tskip t => tskip (rename sb t)
  | tun u t => tun u (rename sb t)
  | tbin b t1 t2 => tbin b (rename sb t1) (rename sb t2)
  | tif t1 t2 t3 => tif (rename sb t1) (rename sb t2) (rename sb t3)
  end
with
vl_rename (sb : var → var) v : vl :=
  let a := tm_rename : Rename tm in
  let b := vl_rename : Rename vl in
  let c := dm_rename : Rename dm in
  match v with
  | var_vl x => var_vl (sb x)
  | vlit _ => v
  | vabs t => vabs (rename (upren sb) t)
  | vobj d => vobj (rename (upren sb) d)
  end
with
dm_rename (sb : var → var) d : dm :=
  let a := vl_rename : Rename vl in
  let b := ty_rename : Rename ty in
  let c := path_rename : Rename path in
  match d with
  | dtysyn ty => dtysyn (rename sb ty)
  | dtysem lv γ => dtysem (rename sb lv) γ
  | dpt p => dpt (rename sb p)
  end
with
ty_rename (sb : var → var) T : ty :=
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
  | TSel p l => TSel (rename sb p) l
  | TPrim _ => T
  | TSing p => TSing (rename sb p)
  end
with
path_rename (sb : var → var) p : path :=
  let a := vl_rename : Rename vl in
  let b := path_rename : Rename path in
  match p with
  | pv v => pv (rename sb v)
  | pself p l => pself (rename sb p) l
  end.

Instance rename_tm : Rename tm := tm_rename.
Instance rename_vl : Rename vl := vl_rename.
Instance rename_ty : Rename ty := ty_rename.
Instance rename_dm : Rename dm := dm_rename.
Instance rename_pth : Rename path := path_rename.

Hint Rewrite @list_rename_fold @list_pair_rename_fold : autosubst.

Fixpoint tm_hsubst (sb : var → vl) t : tm :=
  let a := tm_hsubst : HSubst vl tm in
  let b := vl_subst : Subst vl in
  match t with
  | tv v => tv (subst sb v)
  | tapp t1 t2 => tapp (hsubst sb t1) (hsubst sb t2)
  | tproj t l => (tproj (hsubst sb t) l)
  | tskip t => tskip (hsubst sb t)
  | tun u t => tun u (hsubst sb t)
  | tbin b t1 t2 => tbin b (hsubst sb t1) (hsubst sb t2)
  | tif t1 t2 t3 => tif (hsubst sb t1) (hsubst sb t2) (hsubst sb t3)
  end
with
vl_subst (sb : var → vl) v : vl :=
  let a := tm_hsubst : HSubst vl tm in
  let b := dm_hsubst : HSubst vl dm in
  match v with
  | var_vl x => sb x
  | vlit _ => v
  | vabs t => vabs (hsubst (up sb) t)
  | vobj d => vobj (hsubst (up sb) d)
  end
with
dm_hsubst (sb : var → vl) d : dm :=
  let a := vl_subst : Subst vl in
  let b := ty_hsubst : HSubst vl ty in
  let c := path_hsubst : HSubst vl path in
  match d with
  | dtysyn ty => dtysyn (hsubst sb ty)
  | dtysem lv γ => dtysem (hsubst sb lv) γ
  | dpt p => dpt (hsubst sb p)
  end
with
ty_hsubst (sb : var → vl) T : ty :=
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
  | TSel p l => TSel (hsubst sb p) l
  | TSing p => TSing (hsubst sb p)
  | TPrim _ => T
  end
with
path_hsubst (sb : var → vl) p : path :=
  let b := vl_subst : Subst vl in
  let b := path_hsubst : HSubst vl path in
  match p with
  | pv v => pv (subst sb v)
  | pself p l => pself (hsubst sb p) l
  end.

Instance subst_vl : Subst vl := vl_subst.
Instance hsubst_tm : HSubst vl tm := tm_hsubst.
Instance hsubst_ty : HSubst vl ty := ty_hsubst.
Instance hsubst_dm : HSubst vl dm := dm_hsubst.
Instance hsubst_pth : HSubst vl path := path_hsubst.

Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.

Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.

Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.

Instance base_ty_eq_dec : EqDecision base_ty.
Proof. solve_decision. Defined.

Lemma vl_eq_dec v1 v2 : Decision (v1 = v2)
with
tm_eq_dec t1 t2 : Decision (t1 = t2)
with
dm_eq_dec d1 d2 : Decision (d1 = d2)
with
ty_eq_dec T1 T2 : Decision (T1 = T2)
with
path_eq_dec p1 p2 : Decision (p1 = p2).
Proof.
  all: have vl_eq_dec' : EqDecision vl := vl_eq_dec;
    have dm_eq_dec' : EqDecision dm := dm_eq_dec;
    rewrite /Decision; decide equality; solve_decision.
Defined.

Instance vl_eq_dec' : EqDecision vl := vl_eq_dec.
Instance tm_eq_dec' : EqDecision tm := tm_eq_dec.
Instance dm_eq_dec' : EqDecision dm := dm_eq_dec.
Instance ty_eq_dec' : EqDecision ty := ty_eq_dec.
Instance path_eq_dec' : EqDecision path := path_eq_dec.

Local Ltac finish_lists l x :=
  elim: l => [|x xs IHds] //=; idtac + elim: x => [l d] //=; f_equal => //; by f_equal.

Lemma up_upren_vl (ξ : var → var): up (ren ξ) =@{var → vl} ren (upren ξ).
Proof. exact: up_upren_internal. Qed.

Lemma vl_rename_Lemma (ξ : var → var) v : rename ξ v = v.[ren ξ]
with
tm_rename_Lemma (ξ : var → var) t : rename ξ t = t.|[ren ξ]
with
dm_rename_Lemma (ξ : var → var) d : rename ξ d = d.|[ren ξ]
with
ty_rename_Lemma (ξ : var → var) T : rename ξ T = T.|[ren ξ]
with
path_rename_Lemma (ξ : var → var) p :
  rename ξ p = p.|[ren ξ].
Proof.
  all: [> destruct v | destruct t | destruct d | destruct T | destruct p].
  all: rewrite /= ?up_upren_vl; f_equal => //; finish_lists l x.
Qed.

Lemma vl_ids_Lemma v : v.[ids] = v
with
tm_ids_Lemma t : t.|[ids] = t
with
dm_ids_Lemma d : d.|[ids] = d
with
ty_ids_Lemma T : T.|[ids] = T
with
path_ids_Lemma p : p.|[ids] = p.
Proof.
  all: [> destruct v | destruct t | destruct d | destruct T | destruct p].
  all: rewrite /= ?up_id_internal; f_equal => //; finish_lists l x.
Qed.

Lemma vl_comp_rename_Lemma (ξ : var → var) (σ : var → vl) v :
  (rename ξ v).[σ] = v.[ξ >>> σ]
with
tm_comp_rename_Lemma (ξ : var → var) (σ : var → vl) t :
  (rename ξ t).|[σ] = t.|[ξ >>> σ]
with
dm_comp_rename_Lemma (ξ : var → var) (σ : var → vl) d :
  (rename ξ d).|[σ] = d.|[ξ >>> σ]
with
ty_comp_rename_Lemma (ξ : var → var) (σ : var → vl) T :
  (rename ξ T).|[σ] = T.|[ξ >>> σ]
with
path_comp_rename_Lemma (ξ : var → var) (σ : var → vl) p :
  (rename ξ p).|[σ] = p.|[ξ >>> σ].
Proof.
  all: [> destruct v | destruct t | destruct d | destruct T | destruct p].
  all: rewrite /= 1? up_comp_ren_subst; f_equal => //; finish_lists l x.
Qed.

Lemma vl_rename_comp_Lemma (σ : var → vl) (ξ : var → var) v :
  rename ξ v.[σ] = v.[σ >>> rename ξ]
with
tm_rename_comp_Lemma (σ : var → vl) (ξ : var → var) t :
  rename ξ t.|[σ] = t.|[σ >>> rename ξ]
with
dm_rename_comp_Lemma (σ : var → vl) (ξ : var → var) d :
  rename ξ d.|[σ] = d.|[σ >>> rename ξ]
with
ty_rename_comp_Lemma (σ : var → vl) (ξ : var → var) T :
  rename ξ T.|[σ] = T.|[σ >>> rename ξ]
with
path_rename_comp_Lemma (σ : var → vl) (ξ : var → var) p :
  rename ξ p.|[σ] = p.|[σ >>> rename ξ].
Proof.
  all: [> destruct v | destruct t | destruct d | destruct T | destruct p].
  all: rewrite /= ? up_comp_subst_ren_internal; f_equal => //;
    auto using vl_rename_Lemma, vl_comp_rename_Lemma; finish_lists l x.
Qed.

Lemma vl_comp_Lemma (σ τ : var → vl) v : v.[σ].[τ] = v.[σ >> τ]
with
tm_comp_Lemma (σ τ : var → vl) t : t.|[σ].|[τ] = t.|[σ >> τ]
with
dm_comp_Lemma (σ τ : var → vl) d : d.|[σ].|[τ] = d.|[σ >> τ]
with
ty_comp_Lemma (σ τ : var → vl) T : T.|[σ].|[τ] = T.|[σ >> τ]
with
path_comp_Lemma (σ τ : var → vl) p : p.|[σ].|[τ] = p.|[σ >> τ].
Proof.
  all: [> destruct v | destruct t | destruct d | destruct T | destruct p].
  all: rewrite /= ? up_comp_internal; f_equal;
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

Instance hsubst_lemmas_ctx : HSubstLemmas vl ctx := _.

Instance inh_label : Inhabited label := _.
Instance hsubst_lemmas_dms : HSubstLemmas vl dms := _.

(******************************************************************************)
(** * Auxiliary definitions for operational semantics. *)
(******************************************************************************)

Fixpoint path2tm p: tm :=
  match p with
  | pv v => tv v
  | pself p l => tproj (path2tm p) l
  end.

(******************************************************************************)
(** ** Auxiliary definitions for operational semantics: primitives. *)
(******************************************************************************)
Definition un_op_eval (u : un_op) (v1 : vl) : option vl :=
  match u, v1 with
  | unot, vlit (lbool b) => Some (vlit (lbool (negb b)))
  | _, _ => None
  end.

Definition bin_op_eval_bool (b : bin_op) (b1 b2 : bool) : option vl :=
  match b with
  | beq => Some $ vlit $ lbool $ bool_decide (b1 = b2)
  | _ => None
  end.

Definition bin_op_eval_int (b : bin_op) (n1 n2 : Z) : option vl :=
  match b with
  | bplus => Some $ vlit $ lint (n1 + n2)
  | bminus =>
    if bool_decide (n2 ≤ n1)%Z then
      Some $ vlit $ lint (n1 - n2)
    else
      None
  | btimes => Some $ vlit $ lint (n1 - n2)
  | bdiv =>
    match n2 with
    | Z0 => None
    | _ => Some $ vlit $ lint (n1 / n2)
    end
  | blt => Some $ vlit $ lbool $ bool_decide (n1 < n2)%Z
  | ble => Some $ vlit $ lbool $ bool_decide (n1 ≤ n2)%Z
  | beq => Some $ vlit $ lbool $ bool_decide (n1 = n2)%Z
  end.

Definition bin_op_eval (b : bin_op) (v1 v2 : vl) : option vl :=
  match v1, v2 with
  | vlit (lint n1), vlit (lint n2) => bin_op_eval_int b n1 n2
  | vlit (lbool b1), vlit (lbool b2) => bin_op_eval_bool b b1 b2
  | _, _ => None
  end.

(******************************************************************************)
(** ** Auxiliary definitions for operational semantics: object lookup. *)
(******************************************************************************)

Fixpoint dms_lookup l ds : option dm :=
  match ds with
  | [] => None
  | (l', d) :: ds =>
    match (decide (l = l')) with
    | left Heq => Some d
    | right _ => dms_lookup l ds
    end
  end.

(** Substitute object inside itself (to give semantics to the "self"
    variable). To use when descending under the [vobj] binder. *)
Definition selfSubst ds: dms := ds.|[vobj ds/].

(** Member selection, on paper [v.l ↘ d]. *)
Definition objLookup v (l: label) d: Prop :=
  ∃ ds, v = vobj ds ∧ (dms_lookup l (selfSubst ds)) = Some d.
Hint Unfold objLookup : core.

(* Precedence: tighter than negation and conjunction, must also agree
with [@] notation for paths in [ex_utils.v] to avoid conflicts. *)
Notation "v @ l ↘ d" := (objLookup v l d) (at level 48, l at level 40).

(** Instead of letting obj_opens_to autounfold,
    provide tactics to show it's deterministic and so on. *)

(** Rewrite v @ l ↘ ds to vobj ds' @ l ↘ ds. *)
Ltac simplOpen ds :=
  lazymatch goal with
  | H: ?v @ ?l ↘ ?d |-_=>
    inversion H as (ds & -> & _)
  end.

(** Determinacy of [objLookup]. *)
Lemma objLookupDet v l d1 d2: v @ l ↘ d1 → v @ l ↘ d2 → d1 = d2.
Proof. rewrite /objLookup => *; ev. by simplify_eq. Qed.
Ltac objLookupDet :=
  lazymatch goal with
  | H1: ?v @ ?l ↘ ?d1, H2: ?v @ ?l ↘ ?d2 |- _=>
    have ?: d2 = d1 by [exact: objLookupDet]; simplify_eq
  end.

(** Instantiating iris with Dot *)
Module lang.
Import ectxi_language.

Definition to_val (t: tm) : option vl :=
  match t with
  | tv v => Some v
  | _ => None
  end.

Definition of_val: vl → tm := tv.

(** ** Evaluation context nodes.
On-paper evaluation contexts [K] correspond to [list ectx_item]. *)
Inductive ectx_item :=
| AppLCtx (e2 : tm)
| AppRCtx (v1 : vl)
| ProjCtx (l : label)
| SkipCtx
| UnCtx (u : un_op)
| BinLCtx (b : bin_op) (e2 : tm)
| BinRCtx (b : bin_op) (v1 : vl)
| IfCtx (e1 e2 : tm).

(** Context-filling. *)
Definition fill_item (Ki : ectx_item) (e : tm) : tm :=
  match Ki with
  | AppLCtx e2 => tapp e e2
  | AppRCtx v1 => tapp (tv v1) e
  | ProjCtx l => tproj e l
  | SkipCtx => tskip e
  | UnCtx u => tun u e
  | BinLCtx b e2 => tbin b e e2
  | BinRCtx b v1 => tbin b (tv v1) e
  | IfCtx e1 e2 => tif e e1 e2
  end.

(** ** Head-reduction [e →ₕ e'].
Its context closure [e →ₜ e'] is called [prim_step] and defined by Iris. *)
Inductive head_step : tm → unit → list unit → tm → unit → list tm → Prop :=
(* [(λ x. e) v →ₕ e[x ≔ v]] *)
| st_beta t1 v2 σ:
  head_step (tapp (tv (vabs t1)) (tv v2)) σ [] (t1.|[v2/]) σ []
| st_proj v l σ p:
  (* [v.a ↘ p] *)
  (* ---------- *)
  (* [v.a →ₕ p] *)
  v @ l ↘ dpt p →
  head_step (tproj (tv v) l) σ [] (path2tm p) σ []
(* [coerce v →ₕ v] *)
| st_skip v σ:
  head_step (tskip (tv v)) σ [] (tv v) σ []
(** Rules for primitive operations: *)
| st_un u v1 v σ:
  un_op_eval u v1 = Some v →
  head_step (tun u (tv v1)) σ [] (tv v) σ []
| st_bin b v1 v2 v σ:
  bin_op_eval b v1 v2 = Some v →
  head_step (tbin b (tv v1) (tv v2)) σ [] (tv v) σ []
| st_iftrue e1 e2 σ:
  head_step (tif (tv $ vlit $ lbool true) e1 e2) σ [] e1 σ []
| st_iffalse e1 e2 σ:
  head_step (tif (tv $ vlit $ lbool false) e1 e2) σ [] e2 σ [].

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  revert v; induction e; intros; simplify_option_eq; auto with f_equal.
Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Local Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

Lemma val_stuck e1 σ1 k e2 σ2 ef :
  head_step e1 σ1 k e2 σ2 ef → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 k e2 σ2 ef :
  head_step (fill_item Ki e) σ1 k e2 σ2 ef → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
           end; auto.
Qed.

Lemma dot_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; eauto using of_to_val, val_stuck, fill_item_val,
    fill_item_no_val_inj, head_ctx_step_val with typeclass_instances.
Qed.

End lang.

Export lang.

Canonical Structure dlang_ectxi_lang := ectxi_language.EctxiLanguage lang.dot_lang_mixin.
Canonical Structure dlang_ectx_lang := ectxi_language.EctxLanguageOfEctxi dlang_ectxi_lang.
Canonical Structure dlang_lang := ectx_language.LanguageOfEctx dlang_ectx_lang.
Global Arguments dlang_lang : simpl never.

Lemma hsubst_of_val (v : vl) s : (of_val v).|[s] = of_val (v.[s]).
Proof. done. Qed.

Include Sorts.
End VlSorts.

Implicit Types (vs : vls).

Instance sort_dm : Sort dm := {}.
Instance sort_path : Sort path := {}.
Instance sort_ty : Sort ty := {}.

(** *** Induction principles for syntax. *)

Section syntax_mut_rect.
  Variable Ptm : tm   → Type.
  Variable Pvl : vl   → Type.
  Variable Pdm : dm   → Type.
  Variable Ppt : path → Type.
  Variable Pty : ty   → Type.

  Variable step_tv : ∀ v1, Pvl v1 → Ptm (tv v1).
  Variable step_tapp : ∀ t1 t2, Ptm t1 → Ptm t2 → Ptm (tapp t1 t2).
  Variable step_tproj : ∀ t1 l, Ptm t1 → Ptm (tproj t1 l).
  Variable step_tskip : ∀ t1, Ptm t1 → Ptm (tskip t1).
  Variable step_tun : ∀ u t1, Ptm t1 → Ptm (tun u t1).
  Variable step_tbin : ∀ b t1 t2, Ptm t1 → Ptm t2 → Ptm (tbin b t1 t2).
  Variable step_tif : ∀ t1 t2 t3, Ptm t1 → Ptm t2 → Ptm t3 → Ptm (tif t1 t2 t3).
  Variable step_var_vl : ∀ i, Pvl (var_vl i).
  Variable step_vlit : ∀ l, Pvl (vlit l).
  Variable step_vabs : ∀ t1, Ptm t1 → Pvl (vabs t1).
  (* Original: *)
  (* Variable step_vobj : ∀ l, Pvl (vobj l). *)
  Variable step_vobj : ∀ ds, ForallT Pdm (map snd ds) → Pvl (vobj ds).
  Variable step_dtysyn : ∀ T1, Pty T1 → Pdm (dtysyn T1).
  (* Original: *)
  (* Variable step_dtysem : ∀ vsl g, Pdm (dtysem vs g). *)
  Variable step_dtysem : ∀ vs s, ForallT Pvl vs → Pdm (dtysem vs s).
  Variable step_dpt : ∀ p1, Ppt p1 → Pdm (dpt p1).
  Variable step_pv : ∀ v1, Pvl v1 → Ppt (pv v1).
  Variable step_psefl : ∀ p1 l, Ppt p1 → Ppt (pself p1 l).
  Variable step_TTop : Pty TTop.
  Variable step_TBot : Pty TBot.
  Variable step_TAnd : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TAnd T1 T2).
  Variable step_TOr : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TOr T1 T2).
  Variable step_TLater : ∀ T1, Pty T1 → Pty (TLater T1).
  Variable step_TAll : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TAll T1 T2).
  Variable step_TMu : ∀ T1, Pty T1 → Pty (TMu T1).
  Variable step_TVMem : ∀ l T1, Pty T1 → Pty (TVMem l T1).
  Variable step_TTMem : ∀ l T1 T2, Pty T1 → Pty T2 → Pty (TTMem l T1 T2).
  Variable step_TSel : ∀ p1 l, Ppt p1 → Pty (TSel p1 l).
  Variable step_TSing : ∀ p1, Ppt p1 → Pty (TSing p1).
  Variable step_TPrim : ∀ b, Pty (TPrim b).

  Fixpoint tm_mut_rect t : Ptm t
  with vl_mut_rect v : Pvl v
  with dm_mut_rect d : Pdm d
  with path_mut_rect p : Ppt p
  with ty_mut_rect T : Pty T.
  Proof.
    (* Automation risk producing circular proofs that call right away the lemma we're proving.
       Instead we want to apply one of the [case_] arguments to perform an
       inductive step, and only then call ourselves recursively. *)
    all: [> destruct t | destruct v | destruct d | destruct p | destruct T].
    all:
      try match goal with
      (* Warning: add other arities as needed. *)
      | Hstep : context [?P (?c _ _ _ _)] |- ?P (?c _ _ _ _) => apply Hstep; trivial
      | Hstep : context [?P (?c _ _ _)] |- ?P (?c _ _ _) => apply Hstep; trivial
      | Hstep : context [?P (?c _ _)] |- ?P (?c _ _) => apply Hstep; trivial
      | Hstep : context [?P (?c _)] |- ?P (?c _) => apply Hstep; trivial
      | Hstep : context [?P (?c)] |- ?P (?c) => apply Hstep; trivial
      end.
    - elim: l => [|[l d] ds IHds] //=; auto.
    - elim: l => [|v vs IHxs] //=; auto.
  Qed.

  Lemma syntax_mut_rect : (∀ t, Ptm t) * (∀ v, Pvl v) * (∀ d, Pdm d) * (∀ p, Ppt p) * (∀ T, Pty T).
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

  Variable step_tv : ∀ v1, Pvl v1 → Ptm (tv v1).
  Variable step_tapp : ∀ t1 t2, Ptm t1 → Ptm t2 → Ptm (tapp t1 t2).
  Variable step_tproj : ∀ t1 l, Ptm t1 → Ptm (tproj t1 l).
  Variable step_tskip : ∀ t1, Ptm t1 → Ptm (tskip t1).
  Variable step_tun : ∀ u t1, Ptm t1 → Ptm (tun u t1).
  Variable step_tbin : ∀ b t1 t2, Ptm t1 → Ptm t2 → Ptm (tbin b t1 t2).
  Variable step_tif : ∀ t1 t2 t3, Ptm t1 → Ptm t2 → Ptm t3 → Ptm (tif t1 t2 t3).
  Variable step_var_vl : ∀ i, Pvl (var_vl i).
  Variable step_vlit : ∀ l, Pvl (vlit l).
  Variable step_vabs : ∀ t1, Ptm t1 → Pvl (vabs t1).
  (* Original: *)
  (* Variable step_vobj : ∀ l, Pvl (vobj l). *)
  Variable step_vobj : ∀ ds, Forall Pdm (map snd ds) → Pvl (vobj ds).
  Variable step_dtysyn : ∀ T1, Pty T1 → Pdm (dtysyn T1).
  (* Original: *)
  (* Variable step_dtysem : ∀ vsl g, Pdm (dtysem vs g). *)
  Variable step_dtysem : ∀ vs s, Forall Pvl vs → Pdm (dtysem vs s).
  Variable step_dpt : ∀ p1, Ppt p1 → Pdm (dpt p1).
  Variable step_pv : ∀ v1, Pvl v1 → Ppt (pv v1).
  Variable step_psefl : ∀ p1 l, Ppt p1 → Ppt (pself p1 l).
  Variable step_TTop : Pty TTop.
  Variable step_TBot : Pty TBot.
  Variable step_TAnd : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TAnd T1 T2).
  Variable step_TOr : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TOr T1 T2).
  Variable step_TLater : ∀ T1, Pty T1 → Pty (TLater T1).
  Variable step_TAll : ∀ T1 T2, Pty T1 → Pty T2 → Pty (TAll T1 T2).
  Variable step_TMu : ∀ T1, Pty T1 → Pty (TMu T1).
  Variable step_TVMem : ∀ l T1, Pty T1 → Pty (TVMem l T1).
  Variable step_TTMem : ∀ l T1 T2, Pty T1 → Pty T2 → Pty (TTMem l T1 T2).
  Variable step_TSel : ∀ p1 l, Ppt p1 → Pty (TSel p1 l).
  Variable step_TSing : ∀ p1, Ppt p1 → Pty (TSing p1).
  Variable step_TPrim : ∀ b, Pty (TPrim b).

  Lemma syntax_mut_ind : (∀ t, Ptm t) ∧ (∀ v, Pvl v) ∧ (∀ d, Pdm d) ∧ (∀ p, Ppt p) ∧ (∀ T, Pty T).
  Proof.
    efeed pose proof syntax_mut_rect as H; try done.
    - intros ds HdsT. apply step_vobj, ForallT_Forall, HdsT.
    - intros vs g HvsT. apply step_dtysem, ForallT_Forall, HvsT.
    - ev; split_and! ; assumption.
  Qed.
End syntax_mut_ind.

(** *** Induction principles for closed terms. *)

(** Some inversion lemmas for [nclosed], needed below. See docs for
[solve_inv_fv_congruence] for explanations. *)

(* The proof of this lemma needs asimpl and hence is expensive, so we provide it
   separately. *)
Lemma fv_vobj_ds_inv l d ds n : nclosed_vl (vobj ((l, d) :: ds)) n → nclosed_vl (vobj ds) n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_vobj_d_inv l d ds n : nclosed_vl (vobj ((l, d) :: ds)) n → nclosed d (S n).
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_dtysem_inv_vs s v vs n : nclosed (dtysem (v :: vs) s) n → nclosed (dtysem vs s) n.
Proof. solve_inv_fv_congruence. Qed.

Lemma fv_dtysem_inv_v s v vs n : nclosed (dtysem (v :: vs) s) n → nclosed_vl v n.
Proof. solve_inv_fv_congruence. Qed.

Hint Resolve fv_vobj_ds_inv fv_vobj_d_inv fv_dtysem_inv_v fv_dtysem_inv_vs : fvl.

Section syntax_mut_ind_closed.
  Variable Ptm : tm   → nat → Prop.
  Variable Pvl : vl   → nat → Prop.
  Variable Pdm : dm   → nat → Prop.
  Variable Ppt : path → nat → Prop.
  Variable Pty : ty   → nat → Prop.

  Implicit Types (n : nat).

  Variable step_tv : ∀ n v1,
      nclosed_vl v1 n → nclosed (tv v1) n →
      Pvl v1 n → Ptm (tv v1) n.
  Variable step_tapp : ∀ n t1 t2,
      nclosed t1 n → nclosed t2 n → nclosed (tapp t1 t2) n →
      Ptm t1 n → Ptm t2 n → Ptm (tapp t1 t2) n.
  Variable step_tproj : ∀ n t1 l,
      nclosed t1 n → nclosed (tproj t1 l) n →
      Ptm t1 n → Ptm (tproj t1 l) n.
  Variable step_tskip : ∀ n t1,
      nclosed t1 n → nclosed (tskip t1) n →
      Ptm t1 n → Ptm (tskip t1) n.
  Variable step_tun : ∀ n u t1,
      nclosed t1 n → nclosed (tun u t1) n →
      Ptm t1 n → Ptm (tun u t1) n.
  Variable step_tbin : ∀ n b t1 t2,
      nclosed t1 n → nclosed t2 n → nclosed (tbin b t1 t2) n →
      Ptm t1 n → Ptm t2 n → Ptm (tbin b t1 t2) n.
  Variable step_tif : ∀ n t1 t2 t3,
      nclosed t1 n → nclosed t2 n → nclosed t3 n → nclosed (tif t1 t2 t3) n →
      Ptm t1 n → Ptm t2 n → Ptm t3 n → Ptm (tif t1 t2 t3) n.

  Variable step_var_vl : ∀ n i,
      nclosed_vl (var_vl i) n → Pvl (var_vl i) n.
  Variable step_vlit : ∀ n l,
      nclosed_vl (vlit l) n → Pvl (vlit l) n.
  Variable step_vabs : ∀ n t1,
      nclosed t1 (S n) →
      nclosed_vl (vabs t1) n →
      Ptm t1 (S n) → Pvl (vabs t1) n.
  Variable step_vobj : ∀ n ds,
      nclosed ds (S n) → nclosed_vl (vobj ds) n →
      Forall (flip Pdm (S n)) (map snd ds) →
      Pvl (vobj ds) n.

  Variable step_dtysyn : ∀ n T1,
      nclosed T1 n →
      nclosed (dtysyn T1) n →
      Pty T1 n → Pdm (dtysyn T1) n.
  Variable step_dtysem : ∀ n vs s,
      nclosed vs n → nclosed (dtysem vs s) n →
      Forall (flip Pvl n) vs → Pdm (dtysem vs s) n.
  Variable step_dpt : ∀ n p1,
      nclosed p1 n → nclosed (dpt p1) n →
      Ppt p1 n → Pdm (dpt p1) n.

  Variable step_pv : ∀ n v1,
      nclosed_vl v1 n → nclosed (pv v1) n →
      Pvl v1 n → Ppt (pv v1) n.
  Variable step_psefl : ∀ n p1 l,
      nclosed p1 n →
      Ppt p1 n → Ppt (pself p1 l) n.

  Variable step_TTop : ∀ n,
      nclosed TTop n →
      Pty TTop n.
  Variable step_TBot : ∀ n,
      nclosed TBot n →
      Pty TBot n.

  Variable step_TAnd : ∀ n T1 T2,
      nclosed T1 n → nclosed T2 n → nclosed (TAnd T1 T2) n →
      Pty T1 n → Pty T2 n → Pty (TAnd T1 T2) n.
  Variable step_TOr : ∀ n T1 T2,
      nclosed T1 n → nclosed T2 n → nclosed (TOr T1 T2) n →
      Pty T1 n → Pty T2 n → Pty (TOr T1 T2) n.
  Variable step_TLater : ∀ n T1,
      nclosed T1 n → nclosed (TLater T1) n →
      Pty T1 n → Pty (TLater T1) n.
  Variable step_TAll : ∀ n T1 T2,
      nclosed T1 n → nclosed T2 (S n) → nclosed (TAll T1 T2) n →
      Pty T1 n → Pty T2 (S n) → Pty (TAll T1 T2) n.
  Variable step_TMu : ∀ n T1,
      nclosed T1 (S n) → nclosed (TMu T1) n →
      Pty T1 (S n) → Pty (TMu T1) n.
  Variable step_TVMem : ∀ n l T1,
      nclosed T1 n → nclosed (TVMem l T1) n →
      Pty T1 n → Pty (TVMem l T1) n.
  Variable step_TTMem : ∀ n l T1 T2,
      nclosed T1 n → nclosed T2 n → nclosed (TTMem l T1 T2) n →
      Pty T1 n → Pty T2 n → Pty (TTMem l T1 T2) n.
  Variable step_TSel : ∀ n p1 l,
      nclosed p1 n → nclosed (TSel p1 l) n →
      Ppt p1 n → Pty (TSel p1 l) n.
  Variable step_TSing : ∀ n p1,
      nclosed p1 n → nclosed (TSing p1) n →
      Ppt p1 n → Pty (TSing p1) n.
  Variable step_TPrim : ∀ n b,
      nclosed (TPrim b) n →
      Pty (TPrim b) n.

  Fixpoint nclosed_tm_mut_ind n t : nclosed t n → Ptm t n
  with     nclosed_vl_mut_ind n v : nclosed_vl v n → Pvl v n
  with     nclosed_dm_mut_ind n d : nclosed d n → Pdm d n
  with     nclosed_path_mut_ind n p : nclosed p n → Ppt p n
  with     nclosed_ty_mut_ind n T : nclosed T n → Pty T n.
  Proof.
    (* Automation risk producing circular proofs that call right away the lemma we're proving.
       Instead we want to apply one of the [case_] arguments to perform an
       inductive step, and only then call ourselves recursively. *)
    all: [> destruct t | destruct v | destruct d | destruct p | destruct T].
    all: intro Hcl; let byEapply p := efeed p using (fun q => apply q) by (eauto 2; eauto 1 with fv)
    in
      match goal with
      (* Warning: add other arities as needed. *)
      | Hstep : context [?P (?c _ _ _) _] |- ?P (?c ?a1 ?a2 ?a3) _ => byEapply (Hstep n a1 a2 a3)
      | Hstep : context [?P (?c _ _) _] |- ?P (?c ?a1 ?a2) _ => byEapply (Hstep n a1 a2)
      | Hstep : context [?P (?c _) _] |- ?P (?c ?a1) _ => byEapply (Hstep n a1)
      | Hstep : context [?P (?c) _] |- ?P (?c) _ => byEapply (Hstep n)
      end.
    - elim: l Hcl => [|[l d] ds IHds] Hcl /=; constructor => /=; eauto 3 with fvl.
    - elim: l Hcl => [|v vs IHxs]; constructor => /=; eauto 3 with fvl.
  Qed.

  Lemma nclosed_syntax_mut_ind : (∀ t n, nclosed t n → Ptm t n) ∧ (∀ v n, nclosed_vl v n → Pvl v n) ∧ (∀ d n, nclosed d n → Pdm d n) ∧ (∀ p n, nclosed p n → Ppt p n) ∧ (∀ T n, nclosed T n → Pty T n).
  Proof.
    repeat split; intros.
    - exact: nclosed_tm_mut_ind.
    - exact: nclosed_vl_mut_ind.
    - exact: nclosed_dm_mut_ind.
    - exact: nclosed_path_mut_ind.
    - exact: nclosed_ty_mut_ind.
  Qed.
End syntax_mut_ind_closed.
