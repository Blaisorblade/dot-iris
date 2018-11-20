Require Import Dot.tactics.
Require Import Dot.operational.
Import operational.lang.

(* Print Grammar constr. *)
Reserved Notation "Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).
Reserved Notation "Γ ⊢ { l = d } : τ" (at level 64, l, d, τ at next level).
Reserved Notation "Γ ⊢ds ds : τ" (at level 74, ds, τ at next level).
Reserved Notation "Γ ⊢ₜ τ1 , i1 <: τ2 , i2" (at level 74, τ1, τ2, i1, i2 at next level).

Implicit Type τ L T U: ty.
Implicit Type v: vl.
Implicit Type e: tm.
Implicit Type d: dm.
Implicit Type ds: dms.
(* XXX: finish. *)
(**
TODO. Here we follow Amin's judgment for definition typing: it is Γ ⊢ { l = d } : T, meaning:
this definition, with label l, has type T. This works, but requires
reformulating again a bit semantic definition typing.
*)
Inductive typed (Γ : list ty) : tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a value . *)
| Appv_typed e1 v2 τ1 τ2 :
    Γ ⊢ₜ e1: TAll τ1 τ2 →                        Γ ⊢ₜ tv v2 : τ1 →
    (*────────────────────────────────────────────────────────────────────────────────*)
    Γ ⊢ₜ tapp e1 (tv v2) : τ2.[v2/]
(** Non-dependent application; allowed for any argument. *)
| App_typed e1 e2 τ1 τ2 :
    Γ ⊢ₜ e1: TAll τ1 τ2.[toSubst_ty (+1)] →      Γ ⊢ₜ e2 : τ1 →
    (*────────────────────────────────────────────────────────────────────────────────*)
    Γ ⊢ₜ tapp e1 e2 : τ2
| Proj_typed e τ l:
    Γ ⊢ₜ e : TVMem l τ → Γ ⊢ₜ tproj e l : τ
(** Introduction forms *)
| Lam_typed e τ1 τ2 :
    τ1 :: Γ ⊢ₜ e : τ2 →
    (*─────────────────────────*)
    Γ ⊢ₜ tv (vabs e) : TAll τ1 τ2
| VObj_typed ds T:
    TLater T :: Γ ⊢ds ds: T →
    (*──────────────────────*)
    Γ ⊢ₜ tv (vobj ds): TMu T
(** "General" rules *)
| Var_typed x τ :
    Γ !! x = Some τ →
    (*──────────────────────*)
    Γ ⊢ₜ tv (var_vl x) : τ
| Subs_typed e τ1 τ2 :
    Γ ⊢ₜ τ1 , 0 <: τ2 , 0 → Γ ⊢ₜ  e : τ1 →
    (*──────────────────────*)
    Γ ⊢ₜ e : τ2
(* Must be generalized to something like the following, but skip instructions are needed. *)
(* | Subs_typed e i1 i2 τ1 τ2 : *)
(*     Γ ⊢ₜ τ1 , i1 <: τ2 , i2 → Γ ⊢ₜ  e : τ1 → *)
(*     (*──────────────────────*) *)
(*     Γ ⊢ₜ e : τ2 *)

with dms_typed (Γ : list ty) : dms → ty → Prop :=
| dnil_typed : Γ ⊢ds dnil : TTop
| dcons_typed l d ds τ1 τ2 :
    Γ ⊢ { l = d } : τ1 →
    l = dms_length ds →
    Γ ⊢ds ds : τ2 →
    (*──────────────────────*)
    Γ ⊢ds dcons d ds : TTop

with dm_typed (Γ : list ty) : label → dm → ty → Prop :=
| dty_typed l L T U:
    Γ ⊢ₜ L, 1 <: T, 1 →
    Γ ⊢ₜ T, 1 <: U, 1 →
    Γ ⊢ { l = dtysyn T } : TTMem l L U
| dvl_typed l v τ:
    Γ ⊢ₜ tv v : τ →
    Γ ⊢ { l = dvl v } : TVMem l τ

(* Γ ⊢ₜ τ1 , i1 <: τ2 , i2 means that TLater^i1 τ1 <: TLater^i2 τ2. *)
with subtype (Γ : list ty) : ty → nat → ty → nat → Prop :=
| Refl_stp i τ : Γ ⊢ₜ τ , i <: τ , i
| Trans_stp i1 i2 i3 τ1 τ2 τ3:
    Γ ⊢ₜ τ1 , i1 <: τ2 , i2 → Γ ⊢ₜ τ2 , i2 <: τ3 , i3 → Γ ⊢ₜ τ1 , i1 <: τ3 , i3
| Top_stp i τ : Γ ⊢ₜ τ , i <: TTop , i
| Bot_stp i τ : Γ ⊢ₜ TBot , i <: τ , i

where "Γ ⊢ₜ e : τ" := (typed Γ e τ)
and "Γ ⊢ds ds : τ" := (dms_typed Γ ds τ)
and "Γ ⊢ { l = d } : τ" := (dm_typed Γ l d τ)
and "Γ ⊢ₜ τ1 , i1 <: τ2 , i2" := (subtype Γ τ1 i1 τ2 i2).

