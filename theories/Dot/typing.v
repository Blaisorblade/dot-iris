From D Require Import tactics.
From D.Dot Require Export dotsyn typeExtractionSyn stampedness.

Reserved Notation "Γ ⊢ₜ e : T" (at level 74, e, T at next level).
Reserved Notation "Γ ⊢ₚ p : T , i" (at level 74, p, T, i at next level).
Reserved Notation "Γ |d V ⊢ d : T" (at level 74, d, T, V at next level).
Reserved Notation "Γ |ds V ⊢ ds : T" (at level 74, ds, T, V at next level).
Reserved Notation "Γ ⊢ₜ T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

Implicit Types (L T U V : ty) (v : vl) (e : tm) (d : dm) (ds : dms) (Γ : list ty) (g : stys).

Class stampTable := getStampTable : stys.

Section syntyping.
  Context `{hasStampTable: stampTable}.
(**
Judgments for typing, subtyping, path and definition typing.
Here we follow Nada Amin's judgment for definition typing: it is Γ ⊢ { l = d } : T,
meaning: this definition, with label l, has type T.
This works, but requires reformulating again a bit semantic definition typing for proofs.
*)
Inductive typed Γ : tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a value . *)
| Appv_typed e1 v2 T1 T2:
    Γ ⊢ₜ e1: TAll T1 T2 →                        Γ ⊢ₜ tv v2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ ⊢ₜ tapp e1 (tv v2) : T2.|[v2/]
(** Non-dependent application; allowed for any argument. *)
| App_typed e1 e2 T1 T2:
    Γ ⊢ₜ e1: TAll T1 T2.|[ren (+1)] →      Γ ⊢ₜ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ ⊢ₜ tapp e1 e2 : T2
| Proj_typed e T l:
    Γ ⊢ₜ e : TVMem l T →
    (*─────────────────────────*)
    Γ ⊢ₜ tproj e l : T
| TMuE_typed v T:
    Γ ⊢ₜ tv v: TMu T →
    (*──────────────────────*)
    Γ ⊢ₜ tv v: T.|[v/] (** Introduction forms *)
| Lam_typed e T1 T2:
    (* T1 :: Γ ⊢ₜ e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    is_stamped_ty (length Γ) getStampTable T1 →
    T1.|[ren (+1)] :: Γ ⊢ₜ e : T2 →
    (*─────────────────────────*)
    Γ ⊢ₜ tv (vabs e) : TAll T1 T2
| VObj_typed ds T:
    Γ |ds T ⊢ ds: T →
    is_stamped_ty (S (length Γ)) getStampTable T →
    (*──────────────────────*)
    Γ ⊢ₜ tv (vobj ds): TMu T
| TMuI_typed v T:
    Γ ⊢ₜ tv v: T.|[v/] →
    (*──────────────────────*)
    Γ ⊢ₜ tv v: TMu T
| Nat_typed n:
    Γ ⊢ₜ tv (vnat n): TNat

(** "General" rules *)
| Var_typed x T :
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ ⊢ₜ tv (var_vl x) : T.|[ren (+x)]
| Subs_typed e T1 T2 i :
    Γ ⊢ₜ T1, 0 <: T2, i → Γ ⊢ₜ e : T1 →
    (*───────────────────────────────*)
    Γ ⊢ₜ iterate tskip i e : T2
(* A bit surprising this is needed, but appears in the DOT papers, and this is
   only admissible if t has a type U that is a proper subtype of TAnd T1 T2. *)
| TAndI_typed T1 T2 t:
    Γ ⊢ₜ t : T1 →
    Γ ⊢ₜ t : T2 →
    Γ ⊢ₜ t : TAnd T1 T2
where "Γ ⊢ₜ e : T " := (typed Γ e T)
with dms_typed Γ : ty → dms → ty → Prop :=
| dnil_typed V : Γ |ds V ⊢ [] : TTop
(* This demands definitions and members to be defined in aligned lists. I think
   we want more freedom, just like in the logical relation? *)
| dcons_typed V l d ds T1 T2:
    Γ |d V ⊢ d : T1 →
    Γ |ds V ⊢ ds : T2 →
    dms_hasnt ds l →
    label_of_ty T1 = Some l →
    (*──────────────────────*)
    Γ |ds V ⊢ (l, d) :: ds : TAnd T1 T2
where "Γ |ds V ⊢ ds : T" := (dms_typed Γ V ds T)
with dm_typed Γ : ty → dm → ty → Prop :=
| dty_typed V l L T U s σ:
    T ~[ S (length Γ) ] (getStampTable, (s, σ)) →
    TLater V :: Γ ⊢ₜ L, 0 <: U, 0 →
    TLater V :: Γ ⊢ₜ L, 1 <: T, 1 →
    TLater V :: Γ ⊢ₜ T, 1 <: U, 1 →
    Γ |d V ⊢ dtysem σ s : TTMem l L U
| dvl_typed V l v T:
    V :: Γ ⊢ₜ tv v : T →
    Γ |d V ⊢ dvl v : TVMem l T
where "Γ |d V ⊢ d : T" := (dm_typed Γ V d T)
with path_typed Γ : path → ty → nat → Prop :=
| pv_typed v T:
    Γ ⊢ₜ tv v : T →
    Γ ⊢ₚ pv v : T, 0
| pv_dlater p T i:
    Γ ⊢ₚ p : TLater T, i →
    Γ ⊢ₚ p : T, S i
(* Mnemonic: Path from SELecting a Field *)
| pself_typed p T i l:
    Γ ⊢ₚ p : T, i →
    Γ ⊢ₚ pself p l : T, i
| p_subs_typed p T1 T2 i j :
    Γ ⊢ₜ T1, i <: T2, j → Γ ⊢ₚ p : T1, i →
    (*───────────────────────────────*)
    Γ ⊢ₚ p : T2, j
where "Γ ⊢ₚ p : T , i" := (path_typed Γ p T i)
(* Γ ⊢ₜ T1, i1 <: T2, i2 means that TLater^i1 T1 <: TLater^i2 T2. *)
with subtype Γ : ty → nat → ty → nat → Prop :=
| Refl_stp i T :
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ T, i <: T, i
| Trans_stp i1 i2 i3 T1 T2 T3:
    Γ ⊢ₜ T1, i1 <: T2, i2 → Γ ⊢ₜ T2, i2 <: T3, i3 → Γ ⊢ₜ T1, i1 <: T3, i3
| TLaterL_stp i T:
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ TLater T, i <: T, S i
| TLaterR_stp i T:
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ T, S i <: TLater T, i

(* "Structural" rules about indexes *)
| TSucc_stp T i:
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ T, i <: T, S i
| TMono_stp T1 T2 i:
    Γ ⊢ₜ T1, i <: T2, i →
    Γ ⊢ₜ T1, S i <: T2, S i

(* "Logical" connectives *)
| Top_stp i T :
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ T, i <: TTop, i
| Bot_stp i T :
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ TBot, i <: T, i
| TAnd1_stp T1 T2 i:
    is_stamped_ty (length Γ) getStampTable T1 →
    is_stamped_ty (length Γ) getStampTable T2 →
    Γ ⊢ₜ TAnd T1 T2, i <: T1, i
| TAnd2_stp T1 T2 i:
    is_stamped_ty (length Γ) getStampTable T1 →
    is_stamped_ty (length Γ) getStampTable T2 →
    Γ ⊢ₜ TAnd T1 T2, i <: T2, i
| TAnd_stp T1 T2 U i:
    Γ ⊢ₜ U, i <: T1, i →
    Γ ⊢ₜ U, i <: T2, i →
    Γ ⊢ₜ U, i <: TAnd T1 T2, i
| TOr1_stp T1 T2 i:
    is_stamped_ty (length Γ) getStampTable T1 →
    is_stamped_ty (length Γ) getStampTable T2 →
    Γ ⊢ₜ T1, i <: TOr T1 T2, i
| TOr2_stp T1 T2 i:
    is_stamped_ty (length Γ) getStampTable T1 →
    is_stamped_ty (length Γ) getStampTable T2 →
    Γ ⊢ₜ T2, i <: TOr T1 T2, i
| TOr_stp T1 T2 U i:
    Γ ⊢ₜ T1, i <: U, i →
    Γ ⊢ₜ T2, i <: U, i →
    Γ ⊢ₜ TOr T1 T2, i <: U, i

(* Type selections *)
| SelU_stp l L U p i j:
    Γ ⊢ₚ p : TTMem l L U, i →
    Γ ⊢ₜ TSel p l, j <: U, S (i + j)
| LSel_stp l L U p i j:
    Γ ⊢ₚ p : TTMem l L U, i →
    Γ ⊢ₜ L, S (i + j) <: TSel p l, j
| SelAU_stp l L U p i j:
    Γ ⊢ₚ p : TTMem l L U, i →
    Γ ⊢ₜ TSelA p l L U, j <: U, i + j
| LSelA_stp l L U p i j:
    Γ ⊢ₚ p : TTMem l L U, i →
    Γ ⊢ₜ L, i + j <: TSelA p l L U, j

(* Subtyping for recursive types. Congruence, and opening in both directions. *)
| mu_x_stp T1 T2 i:
    (T1 :: Γ) ⊢ₜ T1, i <: T2, i →
    is_stamped_ty (S (length Γ)) getStampTable T1 →
    Γ ⊢ₜ TMu T1, i <: TMu T2, i
| mu_1_stp T1 T2 i:
    (T1 :: Γ) ⊢ₜ T1, i <: T2.|[ren (+1)], i →
    is_stamped_ty (S (length Γ)) getStampTable T1 →
    Γ ⊢ₜ TMu T1, i <: T2, i
| mu_2_stp T1 T2 i:
    T1.|[ren (+1)] :: Γ ⊢ₜ T1.|[ren (+1)], i <: T2, i →
    is_stamped_ty (length Γ) getStampTable T1 →
    Γ ⊢ₜ T1, i <: TMu T2, i

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types.
 "Cov" stands for covariance, "Con" for contravariance. *)
(* Needed? Maybe drop later instead? *)
| TLaterCov_stp T1 T2 i:
    Γ ⊢ₜ T1, S i <: T2, S i →
    Γ ⊢ₜ TLater T1, i <: TLater T2, i
| TAllConCov_stp T1 T2 U1 U2 i:
    (* "Tight" premises. To avoid TLater, we'd probably need to index the
    context. But let's not; indexing the conclusion of typing and having an
    elimination form for TLater (which increases the index) would be enough. *)
    (* Γ ⊢ₜ T2, S i <: T1, S i → *)
    (* TLater T2 :: Γ ⊢ₜ U1, S i <: U2, S i → *)
    (* Non-tight premises. *)
    Γ ⊢ₜ T2, i <: T1, i →
    T2.|[ren (+1)] :: Γ ⊢ₜ U1, i <: U2, i →
    is_stamped_ty (length Γ) getStampTable T2 →
    Γ ⊢ₜ TAll T1 U1, i <: TAll T2 U2, i
| TVMemCov_stp T1 T2 i l:
    Γ ⊢ₜ T1, S i <: T2, S i →
    Γ ⊢ₜ TVMem l T1, i <: TVMem l T2, i
| TTMemConCov_stp L1 L2 U1 U2 i l:
    Γ ⊢ₜ L2, S i <: L1, S i →
    Γ ⊢ₜ U1, S i <: U2, S i →
    Γ ⊢ₜ TTMem l L1 U1, i <: TTMem l L2 U2, i
where "Γ ⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).

  Scheme exp_typed_mut_ind := Induction for typed Sort Prop
  with   exp_dms_typed_mut_ind := Induction for dms_typed Sort Prop
  with   exp_dm_typed_mut_ind := Induction for dm_typed Sort Prop
  with   exp_path_typed_mut_ind := Induction for path_typed Sort Prop.
  (* with   subtype_mut_ind := Induction for subtype Sort Prop. *)

  Combined Scheme exp_typing_mut_ind from exp_typed_mut_ind, exp_dms_typed_mut_ind,
    exp_dm_typed_mut_ind, exp_path_typed_mut_ind.

  Hint Constructors Forall.
  Lemma stamped_mut_subject Γ:
    (∀ e  T, Γ ⊢ₜ e : T → is_stamped_tm (length Γ) getStampTable e) ∧
    (∀ V ds T, Γ |ds V ⊢ ds : T → Forall (is_stamped_dm (S (length Γ)) getStampTable) (map snd ds)) ∧
    (∀ V d T, Γ |d V ⊢ d : T → is_stamped_dm (S (length Γ)) getStampTable d) ∧
    (∀ p T i, Γ ⊢ₚ p : T, i → is_stamped_path (length Γ) getStampTable p).
  Proof.
    eapply exp_typing_mut_ind with
        (P := λ Γ e T _, is_stamped_tm (length Γ) getStampTable e)
        (P0 := λ Γ V ds T _, Forall (is_stamped_dm (S (length Γ)) getStampTable) (map snd ds))
        (P1 := λ Γ V d T _, is_stamped_dm (S (length Γ)) getStampTable d)
        (P2 := λ Γ p T i _, is_stamped_path (length Γ) getStampTable p); cbn; intros; eauto.
    - repeat constructor.
    - intros; elim: i {s} => [|i IHi]; rewrite /= ?iterate_0 ?iterate_S //; eauto.
    - intros; ev. constructor; naive_solver.
    - intros; with_is_stamped inverse; eauto.
  Qed.

  Lemma stamped_exp_subject Γ e T: Γ ⊢ₜ e : T →
    is_stamped_tm (length Γ) getStampTable e.
  Proof. unmut_lemma (stamped_mut_subject Γ). Qed.
  Lemma stamped_path_subject Γ p T i:
    Γ ⊢ₚ p : T, i → is_stamped_path (length Γ) getStampTable p.
  Proof. unmut_lemma (stamped_mut_subject Γ). Qed.

  Scheme typed_mut_ind := Induction for typed Sort Prop
  with   dms_typed_mut_ind := Induction for dms_typed Sort Prop
  with   dm_typed_mut_ind := Induction for dm_typed Sort Prop
  with   path_typed_mut_ind := Induction for path_typed Sort Prop
  with   subtype_mut_ind := Induction for subtype Sort Prop.

  Combined Scheme typing_mut_ind from typed_mut_ind, dms_typed_mut_ind, dm_typed_mut_ind,
    path_typed_mut_ind, subtype_mut_ind.

  Lemma stamped_ren n T g:
    is_stamped_ty n g T <->
    is_stamped_ty (S n) g (T.|[ren (+1)]).
  Admitted.

  Lemma stamped_subst_one n T v g:
    is_stamped_ty (S n) g T →
    is_stamped_vl n g v →
    is_stamped_ty n g (T.|[v/]).
  Admitted.

  Lemma stamped_subst_one_rev n T v g:
    is_stamped_ty n g (T.|[v/]) →
    is_stamped_ty (S n) g T.
  Admitted.

  Hint Resolve stamped_path_subject stamped_ren stamped_subst_one stamped_subst_one_rev.

  Inductive stamped_ctx g: ctx → Prop :=
  | stamped_nil : stamped_ctx g []
  | stamped_cons Γ T:
    stamped_ctx g Γ →
    is_stamped_ty (S (length Γ)) g T →
    stamped_ctx g (T :: Γ)
  .

  Lemma stamped_lookup Γ x T g:
    stamped_ctx g Γ →
    Γ !! x = Some T →
    is_stamped_ty (length Γ) g T.|[ren (+x)].
  Proof.
    elim: x Γ => /= [|x IHx] [|U Γ] /= Hctx Hl; asimpl; try discriminate.
    - cinject Hl. by inverse Hctx.
    - replace (T.|[ren (+S x)]) with (T.|[ren (+x)].|[ren (+1)]); last by asimpl.
      eapply (stamped_ren (length Γ) (T.|[ren (+x)])), IHx; eauto. by inverse Hctx.
  Qed.

  (* n (Hctx: stamped_ctx getStampTable n Γ) *)
  Lemma stamped_mut_types Γ :
    (∀ e  T, Γ ⊢ₜ e : T → ∀ (Hctx: stamped_ctx getStampTable Γ), is_stamped_ty (length Γ) getStampTable T) ∧
    (∀ V ds T, Γ |ds V ⊢ ds : T → ∀ (Hctx: stamped_ctx getStampTable Γ), is_stamped_ty (S (length Γ)) getStampTable V →
      is_stamped_ty (S (length Γ)) getStampTable T) ∧
    (∀ V d T, Γ |d V ⊢ d : T → ∀ (Hctx: stamped_ctx getStampTable Γ), is_stamped_ty (S (length Γ)) getStampTable V →
      is_stamped_ty (S (length Γ)) getStampTable T) ∧
    (∀ p T i, Γ ⊢ₚ p : T , i → ∀ (Hctx: stamped_ctx getStampTable Γ), is_stamped_ty (length Γ) getStampTable T) ∧
    (∀ T1 i1 T2 i2, Γ ⊢ₜ T1, i1 <: T2, i2 → ∀ (Hctx: stamped_ctx getStampTable Γ),
      is_stamped_ty (length Γ) getStampTable T1 ∧ is_stamped_ty (length Γ) getStampTable T2).
  Proof.
    eapply typing_mut_ind with
        (P := λ Γ e T _, ∀ (Hctx: stamped_ctx getStampTable Γ),
          is_stamped_ty (length Γ) getStampTable T)
        (P0 := λ Γ V ds T _, ∀ (Hctx: stamped_ctx getStampTable Γ), is_stamped_ty (S (length Γ)) getStampTable V →
          is_stamped_ty (S (length Γ)) getStampTable T)
        (P1 := λ Γ V d T _, ∀ (Hctx: stamped_ctx getStampTable Γ), is_stamped_ty (S (length Γ)) getStampTable V →
          is_stamped_ty (S (length Γ)) getStampTable T)
        (P2 := λ Γ p T i _, ∀ (Hctx: stamped_ctx getStampTable Γ),
          is_stamped_ty (length Γ) getStampTable T)
        (P3 := λ Γ T1 i1 T2 i2 _, ∀ (Hctx: stamped_ctx getStampTable Γ),
               is_stamped_ty (length Γ) getStampTable T1 ∧ is_stamped_ty (length Γ) getStampTable T2); clear Γ.
    all: intros; cbn in *; ev; try solve [ eauto ].
    all: try solve [try specialize (H Hctx); try specialize (H0 Hctx); ev;
      with_is_stamped inverse; eauto; constructor; cbn; eauto].
    (* Needed: substitution lemma for stamping. *)
    - specialize (H Hctx). inverse H. cbn in *.
      apply stamped_exp_subject in t0. inverse t0.
      by eapply stamped_subst_one.
    - specialize (H Hctx). inverse H. cbn in *. by apply stamped_ren.
    - apply stamped_exp_subject in t. inverse t.
      specialize (H Hctx). inverse H.
      by eapply stamped_subst_one.
    (* - constructor; eauto. apply stamped_ren. (* Needed: the context is well-stamped as well! *) admit. *)
    - constructor; cbn; eauto. apply H.
      econstructor; eauto. by eapply stamped_ren in f.
    - by apply stamped_lookup.
    - have Hctx': stamped_ctx getStampTable (TLater V :: Γ). by constructor => //; constructor.
      specialize (H Hctx'); ev; constructor; auto.
    - have Hctx': stamped_ctx getStampTable (V :: Γ). by constructor.
      specialize (H Hctx'); ev; constructor; auto.
    - have Hctx': stamped_ctx getStampTable (T1 :: Γ). by constructor.
      specialize (H Hctx'); ev; constructor; auto.
    - have Hctx': stamped_ctx getStampTable (T1 :: Γ). by constructor.
      specialize (H Hctx'); ev; constructor; eauto. by eapply stamped_ren.
    - have Hctx': stamped_ctx getStampTable (T1.|[ren (+1)] :: Γ).
        constructor => //. by eapply stamped_ren in f.
      specialize (H Hctx'); ev; constructor; eauto.
    - have Hctx': stamped_ctx getStampTable (T2.|[ren (+1)] :: Γ).
        constructor => //. by eapply stamped_ren in f.
      specialize (H Hctx); specialize (H0 Hctx');
        ev; constructor; eauto.
  Qed.

End syntyping.

Notation "Γ ⊢ₜ e : T " := (typed Γ e T).
Notation "Γ |ds V ⊢ ds : T" := (dms_typed Γ V ds T).
Notation "Γ |d V ⊢ d : T" := (dm_typed Γ V d T).
Notation "Γ ⊢ₚ p : T , i" := (path_typed Γ p T i).
Notation "Γ ⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).
