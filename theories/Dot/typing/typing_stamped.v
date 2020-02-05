From D Require Import tactics.
From D.Dot.syn Require Export syn.
From D.Dot.typing Require Export later_sub.
From D.Dot Require Import typing_storeless.

Implicit Types (L T U : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty).
Implicit Types (g : stys).

(* The typing judgement comes from [s/⊢/s⊢] in [typing_storeless.v], and restricting most values to variables (except in object definitions). *)
Reserved Notation "Γ s⊢ₜ[ g  ] e : T" (at level 74, e, T at next level).
Reserved Notation "Γ s⊢ₚ[ g  ] p : T , i" (at level 74, p, T, i at next level).
Reserved Notation "Γ s⊢[ g  ]{ l := d  } : T " (at level 74, l, d, T at next level).
Reserved Notation "Γ s⊢ds[ g  ] ds : T" (at level 74, ds, T at next level).
Reserved Notation "Γ s⊢ₜ[ g  ] T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

(**
Judgments for typing, subtyping, path and definition typing.
*)
Inductive typed Γ g : tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a path. *)
| App_path_typed p2 e1 T1 T2 T2':
    T2 .Tp[ p2 /]~ T2' →
    is_stamped_ty (length Γ) g T2' →
    Γ s⊢ₜ[ g ] e1: TAll T1 T2 →
    Γ s⊢ₚ[ g ] p2 : T1, 0 →
    (*────────────────────────────────────────────────────────────*)
    Γ s⊢ₜ[ g ] tapp e1 (path2tm p2) : T2'
(** Non-dependent application; allowed for any argument. *)
| App_typed e1 e2 T1 T2:
    Γ s⊢ₜ[ g ] e1: TAll T1 (shift T2) →      Γ s⊢ₜ[ g ] e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ s⊢ₜ[ g ] tapp e1 e2 : T2
| Proj_typed e T l:
    Γ s⊢ₜ[ g ] e : TVMem l T →
    (*─────────────────────────*)
    Γ s⊢ₜ[ g ] tproj e l : T
(** Introduction forms *)
| Lam_typed_strong e T1 T2 Γ':
    ⊢G Γ <:* TLater <$> Γ' →
    is_stamped_ty (length Γ) g T1 →
    (* T1 :: Γ' s⊢ₜ[ g ] e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    shift T1 :: Γ' s⊢ₜ[ g ] e : T2 →
    (*─────────────────────────*)
    Γ s⊢ₜ[ g ] tv (vabs e) : TAll T1 T2
| VObj_typed ds T:
    Γ |L T s⊢ds[ g ] ds: T →
    is_stamped_ty (S (length Γ)) g T →
    (*──────────────────────*)
    Γ s⊢ₜ[ g ] tv (vobj ds): TMu T
| Nat_typed n:
    Γ s⊢ₜ[ g ] tv (vnat n): TNat

(** "General" rules *)
| Var_typed x T :
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ s⊢ₜ[ g ] tv (var_vl x) : shiftN x T
| Subs_typed e T1 T2 i :
    Γ s⊢ₜ[ g ] T1, 0 <: T2, i → Γ s⊢ₜ[ g ] e : T1 →
    (*───────────────────────────────*)
    Γ s⊢ₜ[ g ] iterate tskip i e : T2
| Path_typed p T :
    Γ s⊢ₚ[ g ] p : T, 0 →
    (*───────────────────────────────*)
    Γ s⊢ₜ[ g ] path2tm p : T
where "Γ s⊢ₜ[ g ] e : T " := (typed Γ g e T)
with dms_typed Γ g : dms → ty → Prop :=
| dnil_typed : Γ s⊢ds[ g ] [] : TTop
(* This demands definitions and members to be defined in aligned lists. *)
| dcons_typed l d ds T1 T2:
    Γ s⊢[ g ]{ l := d } : T1 →
    Γ s⊢ds[ g ] ds : T2 →
    dms_hasnt ds l →
    (*──────────────────────*)
    Γ s⊢ds[ g ] (l, d) :: ds : TAnd T1 T2
where "Γ s⊢ds[ g ] ds : T" := (dms_typed Γ g ds T)
with dm_typed Γ g : label → dm → ty → Prop :=
| dty_typed T l L U s σ:
    T ~[ length Γ ] (g, (s, σ)) →
    is_stamped_σ (length Γ) g σ →
    Γ s⊢ₜ[ g ] TLater L, 0 <: TLater T, 0 →
    Γ s⊢ₜ[ g ] TLater T, 0 <: TLater U, 0 →
    Γ s⊢[ g ]{ l := dtysem σ s } : TTMem l L U
| dpt_pv_typed l v T:
    Γ s⊢ₜ[ g ] tv v : T →
    Γ s⊢[ g ]{ l := dpt (pv v) } : TVMem l T
| dpath_typed l p T:
    Γ s⊢ₚ[ g ] p : T, 0 →
    Γ s⊢[ g ]{ l := dpt p } : TVMem l T
| dnew_typed l T ds:
    TAnd (TLater T) (TSing (pself (pv (ids 1)) l)) :: Γ s⊢ds[ g ] ds : T →
    is_stamped_ty (S (length Γ)) g T →
    Γ s⊢[ g ]{ l := dpt (pv (vobj ds)) } : TVMem l (TMu T)
where "Γ s⊢[ g ]{ l := d  } : T" := (dm_typed Γ g l d T)
with path_typed Γ g : path → ty → nat → Prop :=
| pv_typed x T:
    Γ s⊢ₜ[ g ] tv (var_vl x) : T →
    Γ s⊢ₚ[ g ] pv (var_vl x) : T, 0
| pv_dlater p T i:
    Γ s⊢ₚ[ g ] p : TLater T, i →
    Γ s⊢ₚ[ g ] p : T, S i
(* Mnemonic: Path from SELecting a Field *)
| pself_typed p T i l:
    Γ s⊢ₚ[ g ] p : TVMem l T, i →
    Γ s⊢ₚ[ g ] pself p l : T, i
| p_subs_typed p T1 T2 i j :
    Γ s⊢ₜ[ g ] T1, i <: T2, i + j →
    Γ s⊢ₚ[ g ] p : T1, i →
    (*───────────────────────────────*)
    Γ s⊢ₚ[ g ] p : T2, i + j
| p_mu_i_typed p T {T' i} :
    T .Tp[ p /]~ T' →
    is_stamped_ty (S (length Γ)) g T →
    Γ s⊢ₚ[ g ] p : T', i →
    Γ s⊢ₚ[ g ] p : TMu T, i
| p_mu_e_typed p T {T' i} :
    T .Tp[ p /]~ T' →
    is_stamped_ty (length Γ) g T' →
    Γ s⊢ₚ[ g ] p : TMu T, i →
    Γ s⊢ₚ[ g ] p : T', i
| pself_inv_typed p T i l:
    Γ s⊢ₚ[ g ] pself p l : T, i →
    (*─────────────────────────*)
    Γ s⊢ₚ[ g ] p : TVMem l T, i
| psingleton_refl_typed T p i :
    Γ s⊢ₚ[ g ] p : T, i →
    Γ s⊢ₚ[ g ] p : TSing p, i
| psingleton_inv_typed p q i:
    Γ s⊢ₚ[ g ] p : TSing q, i →
    is_stamped_path (length Γ) g q →
    Γ s⊢ₚ[ g ] q : TTop, i
| psingleton_trans p q T i:
    Γ s⊢ₚ[ g ] p : TSing q, i →
    Γ s⊢ₚ[ g ] q : T, i →
    Γ s⊢ₚ[ g ] p : T, i
| psingleton_elim T p q l i:
    Γ s⊢ₚ[ g ] p : TSing q, i →
    Γ s⊢ₚ[ g ] pself q l : T, i →
    Γ s⊢ₚ[ g ] pself p l : TSing (pself q l), i
where "Γ s⊢ₚ[ g ] p : T , i" := (path_typed Γ g p T i)
(* Γ s⊢ₜ[ g ] T1, i1 <: T2, i2 means that TLater^i1 T1 <: TLater^i2 T2. *)
with subtype Γ g : ty → nat → ty → nat → Prop :=
| Refl_stp i T :
    is_stamped_ty (length Γ) g T →
    Γ s⊢ₜ[ g ] T, i <: T, i
| Trans_stp i2 T2 {i1 i3 T1 T3}:
    Γ s⊢ₜ[ g ] T1, i1 <: T2, i2 →
    Γ s⊢ₜ[ g ] T2, i2 <: T3, i3 →
    Γ s⊢ₜ[ g ] T1, i1 <: T3, i3
| TLaterL_stp i T:
    is_stamped_ty (length Γ) g T →
    Γ s⊢ₜ[ g ] TLater T, i <: T, S i
| TLaterR_stp i T:
    is_stamped_ty (length Γ) g T →
    Γ s⊢ₜ[ g ] T, S i <: TLater T, i

(* "Structural" rules about indexes *)
| TAddLater_stp T i:
    is_stamped_ty (length Γ) g T →
    Γ s⊢ₜ[ g ] T, i <: TLater T, i
| TMono_stp T1 T2 i j:
    Γ s⊢ₜ[ g ] T1, i <: T2, j →
    Γ s⊢ₜ[ g ] T1, S i <: T2, S j

(* "Logical" connectives *)
| Top_stp i T :
    is_stamped_ty (length Γ) g T →
    Γ s⊢ₜ[ g ] T, i <: TTop, i
| Bot_stp i T :
    is_stamped_ty (length Γ) g T →
    Γ s⊢ₜ[ g ] TBot, i <: T, i
| TAnd1_stp T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ s⊢ₜ[ g ] TAnd T1 T2, i <: T1, i
| TAnd2_stp T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ s⊢ₜ[ g ] TAnd T1 T2, i <: T2, i
| TAnd_stp T U1 U2 i j:
    Γ s⊢ₜ[ g ] T, i <: U1, j →
    Γ s⊢ₜ[ g ] T, i <: U2, j →
    Γ s⊢ₜ[ g ] T, i <: TAnd U1 U2, j
| TOr1_stp T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ s⊢ₜ[ g ] T1, i <: TOr T1 T2, i
| TOr2_stp T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ s⊢ₜ[ g ] T2, i <: TOr T1 T2, i
| TOr_stp T1 T2 U i j:
    Γ s⊢ₜ[ g ] T1, i <: U, j →
    Γ s⊢ₜ[ g ] T2, i <: U, j →
    Γ s⊢ₜ[ g ] TOr T1 T2, i <: U, j

(* Type selections *)
| SelU_stp p L {l U i}:
    Γ s⊢ₚ[ g ] p : TTMem l L U, i →
    Γ s⊢ₜ[ g ] TSel p l, i <: TLater U, i
| LSel_stp p U {l L i}:
    Γ s⊢ₚ[ g ] p : TTMem l L U, i →
    Γ s⊢ₜ[ g ] TLater L, i <: TSel p l, i
| PSub_singleton_stp p q {i T1 T2}:
    T1 ~Tp[ p := q ]* T2 →
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ s⊢ₚ[ g ] p : TSing q, i →
    Γ s⊢ₜ[ g ] T1, i <: T2, i
| PSym_singleton_stp T {p q i}:
    Γ s⊢ₚ[ g ] p : T, i →
    Γ s⊢ₜ[ g ] TSing p, i <: TSing q, i →
    Γ s⊢ₜ[ g ] TSing q, i <: TSing p, i
| PSelf_singleton_stp {p T i} :
    Γ s⊢ₚ[ g ] p : T, i →
    Γ s⊢ₜ[ g ] TSing p, i <: T, i

(* TODO: figure out if the drugs I had when I wrote these rules were good or bad. *)
(* | SelU_stp l L U p i j: *)
(*     Γ s⊢ₚ[ g ] p : TTMem l L U, i → *)
(*     Γ s⊢ₜ[ g ] TSel p l, j <: U, S (i + j) *)
(* | LSel_stp l L U p i j: *)
(*     Γ s⊢ₚ[ g ] p : TTMem l L U, i → *)
(*     Γ s⊢ₜ[ g ] L, S (i + j) <: TSel p l, j *)

(* Subtyping for recursive types. Congruence, and opening in both directions. *)
| Mu_stp_mu T1 T2 i j:
    (iterate TLater i T1 :: Γ) s⊢ₜ[ g ] T1, i <: T2, j →
    is_stamped_ty (S (length Γ)) g T1 →
    Γ s⊢ₜ[ g ] TMu T1, i <: TMu T2, j
| Mu_stp T i:
    is_stamped_ty (length Γ) g T →
    Γ s⊢ₜ[ g ] TMu (shift T), i <: T, i
| Stp_mu T i:
    is_stamped_ty (length Γ) g T →
    Γ s⊢ₜ[ g ] T, i <: TMu (shift T), i

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types.
 "Cov" stands for covariance, "Con" for contravariance. *)
(* Needed? Maybe drop later instead? *)
| TLaterCov_stp T1 T2 i j:
    Γ s⊢ₜ[ g ] T1, S i <: T2, S j →
    Γ s⊢ₜ[ g ] TLater T1, i <: TLater T2, j
| TAllConCov_stp T1 T2 U1 U2 i:
    Γ s⊢ₜ[ g ] TLater T2, i <: TLater T1, i →
    iterate TLater (S i) (shift T2) :: Γ s⊢ₜ[ g ] TLater U1, i <: TLater U2, i →
    is_stamped_ty (length Γ) g T2 →
    Γ s⊢ₜ[ g ] TAll T1 U1, i <: TAll T2 U2, i
| TVMemCov_stp T1 T2 i l:
    Γ s⊢ₜ[ g ] T1, i <: T2, i →
    Γ s⊢ₜ[ g ] TVMem l T1, i <: TVMem l T2, i
| TTMemConCov_stp L1 L2 U1 U2 i l:
    Γ s⊢ₜ[ g ] TLater L2, i <: TLater L1, i →
    Γ s⊢ₜ[ g ] TLater U1, i <: TLater U2, i →
    Γ s⊢ₜ[ g ] TTMem l L1 U1, i <: TTMem l L2 U2, i
  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
| TAllDistr_stp T U1 U2 i:
    is_stamped_ty (length Γ) g T →
    is_stamped_ty (S (length Γ)) g U1 →
    is_stamped_ty (S (length Γ)) g U2 →
    Γ s⊢ₜ[ g ] TAnd (TAll T U1) (TAll T U2), i <: TAll T (TAnd U1 U2), i
| TVMemDistr_stp l T1 T2 i:
    is_stamped_ty (length Γ) g T1 →
    is_stamped_ty (length Γ) g T2 →
    Γ s⊢ₜ[ g ] TAnd (TVMem l T1) (TVMem l T2), i <: TVMem l (TAnd T1 T2), i
| TTMemDistr_stp l L U1 U2 i:
    is_stamped_ty (length Γ) g L →
    is_stamped_ty (length Γ) g U1 →
    is_stamped_ty (length Γ) g U2 →
    Γ s⊢ₜ[ g ] TAnd (TTMem l L U1) (TTMem l L U2), i <: TTMem l L (TAnd U1 U2), i
where "Γ s⊢ₜ[ g ] T1 , i1 <: T2 , i2" := (subtype Γ g T1 i1 T2 i2).

Scheme exp_stamped_objIdent_typed_mut_ind := Induction for typed Sort Prop
with   exp_stamped_objIdent_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   exp_stamped_objIdent_dm_typed_mut_ind := Induction for dm_typed Sort Prop
with   exp_stamped_objIdent_path_typed_mut_ind := Induction for path_typed Sort Prop.
(* with   subtype_mut_ind := Induction for subtype Sort Prop. *)

Combined Scheme exp_stamped_objIdent_typing_mut_ind from exp_stamped_objIdent_typed_mut_ind, exp_stamped_objIdent_dms_typed_mut_ind,
  exp_stamped_objIdent_dm_typed_mut_ind, exp_stamped_objIdent_path_typed_mut_ind.

Scheme stamped_objIdent_typed_mut_ind := Induction for typed Sort Prop
with   stamped_objIdent_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   stamped_objIdent_dm_typed_mut_ind := Induction for dm_typed Sort Prop
with   stamped_objIdent_path_typed_mut_ind := Induction for path_typed Sort Prop
with   stamped_objIdent_subtype_mut_ind := Induction for subtype Sort Prop.

Combined Scheme stamped_objIdent_typing_mut_ind from stamped_objIdent_typed_mut_ind, stamped_objIdent_dms_typed_mut_ind,
  stamped_objIdent_dm_typed_mut_ind, stamped_objIdent_path_typed_mut_ind, stamped_objIdent_subtype_mut_ind.


  (* Scheme typed_mut_ind := Induction for typed Sort Prop
  with   dms_typed_mut_ind := Induction for dms_typed Sort Prop
  with   dm_typed_mut_ind := Induction for dm_typed Sort Prop
  with   path_typed_mut_ind := Induction for path_typed Sort Prop
  with   subtype_mut_ind := Induction for subtype Sort Prop.

  Combined Scheme typing_mut_ind from typed_mut_ind, dms_typed_mut_ind, dm_typed_mut_ind,
    path_typed_mut_ind, subtype_mut_ind. *)

Hint Constructors typed dms_typed dm_typed path_typed subtype : core.
Remove Hints Trans_stp : core.
Hint Extern 10 => try_once Trans_stp : core.

Lemma Lam_typed Γ e T1 T2 g:
  is_stamped_ty (length Γ) g T1 →
  shift T1 :: Γ s⊢ₜ[ g ] e : T2 →
  (*─────────────────────────*)
  Γ s⊢ₜ[ g ] tv (vabs e) : TAll T1 T2.
Proof. apply Lam_typed_strong. ietp_weaken_ctx. Qed.

Lemma Lam_typed_strip1 Γ e V T1 T2 g:
  is_stamped_ty (S (length Γ)) g T1 →
  shift T1 :: V :: Γ s⊢ₜ[ g ] e : T2 →
  (*─────────────────────────*)
  Γ |L V s⊢ₜ[ g ] tv (vabs e) : TAll T1 T2.
Proof.
  intros. apply Lam_typed_strong with (Γ' := (V :: Γ)) => //.
  rewrite /defCtxCons/=; ietp_weaken_ctx.
Qed.

Lemma dvabs_typed' Γ V T1 T2 e l g:
  is_stamped_ty (S (length Γ)) g T1 →
  shift T1 :: V :: Γ s⊢ₜ[ g ] e : T2 →
  Γ |L V s⊢[ g ]{ l := dpt (pv (vabs e)) } : TVMem l (TAll T1 T2).
Proof. by intros; apply dpt_pv_typed, Lam_typed_strip1. Qed.

Ltac typconstructor :=
  match goal with
  | |- typed _ _ _ _ => first [apply Lam_typed_strip1 | apply Lam_typed | constructor]
  | |- dms_typed _ _ _ _ => constructor
  | |- dm_typed _ _ _ _ _ => first [apply dvabs_typed' | constructor]
  | |- path_typed _ _ _ _ _ => constructor
  | |- subtype _ _ _ _ _ _ => constructor
  end.

Section syntyping_lemmas.
  Lemma typing_obj_ident_to_typing_mut Γ g:
    (∀ e T, Γ s⊢ₜ[ g ] e : T → Γ v⊢ₜ[ g ] e : T) ∧
    (∀ ds T, Γ s⊢ds[ g ] ds : T → Γ v⊢ds[ g ] ds : T) ∧
    (∀ l d T, Γ s⊢[ g ]{ l := d } : T → Γ v⊢[ g ]{ l := d } : T) ∧
    (∀ p T i, Γ s⊢ₚ[ g ] p : T, i → Γ v⊢ₚ[ g ] p : T, i) ∧
    (∀ T1 i1 T2 i2, Γ s⊢ₜ[ g ] T1, i1 <: T2, i2 → Γ v⊢ₜ[ g ] T1, i1 <: T2, i2).
  Proof.
    eapply stamped_objIdent_typing_mut_ind with
        (P := λ Γ g e T _, Γ v⊢ₜ[ g ] e : T)
        (P0 := λ Γ g ds T _, Γ v⊢ds[ g ] ds : T)
        (P1 := λ Γ g l d T _, Γ v⊢[ g ]{ l := d } : T)
        (P2 := λ Γ g p T i _, Γ v⊢ₚ[ g ] p : T, i)
        (P3 := λ Γ g T1 i1 T2 i2 _, Γ v⊢ₜ[ g ] T1, i1 <: T2, i2); clear Γ g;
      solve [econstructor; eauto].
  Qed.
  Lemma typing_obj_ident_to_typing Γ g e T:
    Γ s⊢ₜ[ g ] e : T → Γ v⊢ₜ[ g ] e : T.
  Proof. apply typing_obj_ident_to_typing_mut. Qed.
End syntyping_lemmas.
