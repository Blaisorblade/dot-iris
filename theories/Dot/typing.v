From D Require Import tactics.
From D.Dot Require Export syn typeExtractionSyn stampedness closed_subst.

Reserved Notation "Γ ⊢ₜ e : T" (at level 74, e, T at next level).
Reserved Notation "Γ ⊢ₚ p : T , i" (at level 74, p, T, i at next level).
Reserved Notation "Γ |d V ⊢ d : T" (at level 74, d, T, V at next level).
Reserved Notation "Γ |ds V ⊢ ds : T" (at level 74, ds, T, V at next level).
Reserved Notation "Γ ⊢ₜ T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

Implicit Types (L T U V : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty) (g : stys).

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
| SelU_stp l L U p i:
    Γ ⊢ₚ p : TTMem l L U, i →
    Γ ⊢ₜ TSel p l, i <: TLater U, i
| LSel_stp l L U p i:
    Γ ⊢ₚ p : TTMem l L U, i →
    Γ ⊢ₜ TLater L, i <: TSel p l, i

(* TODO: figure out if the drugs I had when I wrote these rules were good or bad. *)
(* | SelU_stp l L U p i j: *)
(*     Γ ⊢ₚ p : TTMem l L U, i → *)
(*     Γ ⊢ₜ TSel p l, j <: U, S (i + j) *)
(* | LSel_stp l L U p i j: *)
(*     Γ ⊢ₚ p : TTMem l L U, i → *)
(*     Γ ⊢ₜ L, S (i + j) <: TSel p l, j *)

(* Subtyping for recursive types. Congruence, and opening in both directions. *)
| Mu_stp_mu T1 T2 i:
    (iterate TLater i T1 :: Γ) ⊢ₜ T1, i <: T2, i →
    is_stamped_ty (S (length Γ)) getStampTable T1 →
    Γ ⊢ₜ TMu T1, i <: TMu T2, i
| Mu_stp T i:
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ TMu T.|[ren (+1)], i <: T, i
| Stp_mu T i:
    is_stamped_ty (length Γ) getStampTable T →
    Γ ⊢ₜ T, i <: TMu T.|[ren (+1)], i

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
  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
| TAllDistr_stp T U1 U2 i:
    is_stamped_ty (length Γ) getStampTable T →
    is_stamped_ty (S (length Γ)) getStampTable U1 →
    is_stamped_ty (S (length Γ)) getStampTable U2 →
    Γ ⊢ₜ TAnd (TAll T U1) (TAll T U2), i <: TAll T (TAnd U1 U2), i
| TVMemDistr_stp l T1 T2 i:
    is_stamped_ty (length Γ) getStampTable T1 →
    is_stamped_ty (length Γ) getStampTable T2 →
    Γ ⊢ₜ TAnd (TVMem l T1) (TVMem l T2), i <: TVMem l (TAnd T1 T2), i
| TTMemDistr_strp l L U1 U2 i:
    is_stamped_ty (length Γ) getStampTable L →
    is_stamped_ty (length Γ) getStampTable U1 →
    is_stamped_ty (length Γ) getStampTable U2 →
    Γ ⊢ₜ TAnd (TTMem l L U1) (TTMem l L U2), i <: TTMem l L (TAnd U1 U2), i
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
    - repeat constructor => //=. by eapply lookup_lt_Some.
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
(*
  Definition is_stamped_sub n m g s :=
    ∀ i, i < n → is_stamped_vl m g (s i).
  Definition is_stamped_ren n m g r := is_stamped_sub n m g (ren r).

  Lemma stamped_ren_shift n m j g:
    m >= j + n →
    is_stamped_ren n m g (+j).
  Proof. constructor => //=; lia. Qed.

  Lemma stamped_ren_up n m g r:
    is_stamped_ren n m g r →
    is_stamped_ren (S n) (S m) g (upren r).
  Proof.
    (* rewrite /is_stamped_ren /is_stamped_sub /=. *)
    move => Hr [|i] //= Hi; first by constructor => /=; lia.
    have Hi': i < n by lia.
    specialize (Hr i Hi'); inverse Hr.
    constructor; cbn in *; by lia.
  Qed.
  Hint Resolve stamped_ren_up.
  Require Import stdpp.list.
  Lemma swap_snd_list_pair_rename r ds: map snd (list_pair_rename r ds) = map (rename r) (map snd ds).
  Proof.
    rewrite /list_pair_rename /mapsnd !map_map /=.
    elim: ds => [| [a b] ds IHds] //=; by f_equal.
  Qed.

  Definition nclosed_sub n m s :=
    ∀ i, i < n → nclosed_vl (s i) m.
  Definition nclosed_ren n m (r: var → var) := nclosed_sub n m (ren r).

  Lemma nclosed_ren_mut:
    (∀ e r i j,
      nclosed_ren i j r →
      nclosed e i →
      nclosed (rename r e) j) ∧
    (∀ v r i j,
      nclosed_ren i j r →
      nclosed_vl v i →
      nclosed_vl (rename r v) j) ∧
    (∀ d r i j,
      nclosed_ren i j r →
      nclosed d i →
      nclosed (rename r d) j) ∧
    (∀ p r i j,
      nclosed_ren i j r →
      nclosed p i →
      nclosed (rename r p) j) ∧
    (∀ T r i j,
      nclosed_ren i j r →
      nclosed T i →
      nclosed (rename r T) j).
  Proof.
  Admitted.
  Lemma nclosed_ren_vl: ∀ v r i j,
      nclosed_ren i j r →
      nclosed_vl v i →
      nclosed_vl (rename r v) j.
  Proof. unmut_lemma nclosed_ren_mut. Qed.
  Lemma is_stamped_nclosed_ren i j g r: is_stamped_ren i j g r → nclosed_ren i j r.
  Admitted.

  Lemma stamped_ren_mut:
    (∀ t g r i j,
      is_stamped_ren i j g r →
      is_stamped_tm i g t →
      is_stamped_tm j g (rename r t)) ∧
    (∀ v g r i j,
      is_stamped_ren i j g r →
      is_stamped_vl i g v →
      is_stamped_vl j g (rename r v)) ∧
    (∀ d g r i j,
      is_stamped_ren i j g r →
      is_stamped_dm i g d →
      is_stamped_dm j g (rename r d)) ∧
    (∀ p g r i j,
      is_stamped_ren i j g r →
      is_stamped_path i g p →
      is_stamped_path j g (rename r p)) ∧
    (∀ T g r i j,
      is_stamped_ren i j g r →
      is_stamped_ty i g T →
      is_stamped_ty j g (rename r T)).
  Proof.
    apply syntax_mut_ind; intros; with_is_stamped ltac:(fun H => inversion_clear H);
      cbn in *; try by [constructor; cbn; eauto].
    - eauto.
    - constructor; rewrite swap_snd_list_pair_rename Forall_fmap;
        by decompose_Forall; eauto.
      (* constructor. destruct ds as [| d ds] => //=.
      constructor; rewrite ?rew /mapsnd 1?Forall_fmap /=; first case_match; cbn in *; eauto.
      decompose_Forall. eauto.

      (* inversion_clear H; inversion_clear H2. *)
      decompose_Forall.
      eauto.
      eapply Forall_impl. done.

      rewrite map_map.
      rewrite -map_map.
      rewrite Forall_fmap.
      rewrite Forall_fmap.
      idtac "a". SearchAbout (Forall _ (map _ _)).
      About Forall.
      Print Coq.Lists.List.

      Check Forall_map.
      eapply Forall_impl.
      rewrite map_map /=.
      eapply H3.
      eapply H3.
      specialize (H1 g (upren r)).

      induction ds => //=. constructor.
      by eapply stamped_ren_vl. *)
    - constructor. rewrite /= /rename /list_rename map_length /=.
      ev; eexists; split_and!; eauto; rewrite Forall_fmap.
      decompose_Forall.
      eapply nclosed_ren_vl => //.
      by eapply is_stamped_nclosed_ren.
    Qed.

  Lemma stamped_ren_vl: ∀ v g r i j,
    is_stamped_ren i j g r →
    is_stamped_vl i g v →
    is_stamped_vl j g (rename r v).
  Proof. unmut_lemma stamped_ren_mut. Qed.
    (* move: r i j. induction v => r i j Hr //= Hv; inversion_clear Hv; constructor; cbn in *.
    - specialize (Hr v H); inversion_clear Hr; by cbn in *.
    - admit.
    - elim: l H => [| d ds IHds] //= Hds.
      inversion_clear Hds as [|?? Hd Hds'].
      constructor. admit. auto.
  Admitted. *)
  Hint Resolve stamped_ren_shift.
  Lemma stamped_sub_up n m g s:
    is_stamped_sub n m g s →
    is_stamped_sub (S n) (S m) g (up s).
  Proof.
    move => Hs [|i] Hi //=. by constructor => /=; lia.
    eapply stamped_ren_vl; eauto with lia.
  Qed.
  Hint Resolve stamped_sub_up.

  Lemma stamped_subst_vl v g s m n:
    is_stamped_sub n m g s →
    is_stamped_vl n g v →
    is_stamped_vl m g v.[s]
  with
  stamped_subst_ty T g s m n:
    is_stamped_sub n m g s →
    is_stamped_ty n g T →
    is_stamped_ty m g T.|[s].
  Proof.
    -
      move: s m n. induction v => s i j Hss HsV //=;
      with_is_stamped ltac:(fun H => inversion_clear H); try econstructor; cbn;
      eauto 3 using stamped_sub_up with lia.
      admit.
      admit.
    - move: s m n; induction T => s m n Hss HsT //;
      with_is_stamped ltac:(fun H => inversion_clear H); constructor; cbn;
        eauto 3 using stamped_sub_up.
      (* Missing: case for paths. *)
  Admitted.

  Lemma stamped_subst_ty_rev T g s m n:
    is_stamped_sub n m g s →
    is_stamped_ty m g (T.|[s]) →
    is_stamped_ty n g T.
  Admitted.

  Lemma stamped_ren n T g:
    is_stamped_ty n g T <->
    is_stamped_ty (S n) g (T.|[ren (+1)]).
  Proof.
    have Hs: is_stamped_sub n (S n) g (ren (+1)). by apply stamped_ren_shift; lia.
    split; intros; by [> eapply stamped_subst_ty | eapply stamped_subst_ty_rev].
  Qed.

  Lemma is_stamped_sub_single n v g:
    is_stamped_vl n g v →
    is_stamped_sub (S n) n g (v .: ids).
  Proof. move => Hv [|i] //= Hin; constructor => /=; lia. Qed.

  Lemma stamped_subst_one n T v g:
    is_stamped_ty (S n) g T →
    is_stamped_vl n g v →
    is_stamped_ty n g (T.|[v/]).
  Proof.
    intros; eapply stamped_subst_ty => //; by apply is_stamped_sub_single.
  Qed.

  Lemma stamped_subst_one_rev n T v g:
    is_stamped_ty n g (T.|[v/]) →
    is_stamped_ty (S n) g T.
  Admitted. *)

  Hint Resolve stamped_path_subject is_stamped_ren_ty is_stamped_sub_one is_stamped_sub_one_rev.

  Inductive stamped_ctx g: ctx → Prop :=
  | stamped_nil : stamped_ctx g []
  | stamped_cons Γ T:
    stamped_ctx g Γ →
    is_stamped_ty (S (length Γ)) g T →
    stamped_ctx g (T :: Γ)
  .

  Lemma stamped_nclosed_lookup Γ x T g:
    stamped_ctx g Γ →
    Γ !! x = Some T →
    nclosed T.|[ren (+x)] (length Γ).
  Admitted.

  Lemma stamped_lookup Γ x T g:
    stamped_ctx g Γ →
    Γ !! x = Some T →
    is_stamped_ty (length Γ) g T.|[ren (+x)].
  Proof.
    elim: x Γ => /= [|x IHx] [|U Γ] /= Hctx Hl; asimpl; try discriminate.
    - cinject Hl. by inverse Hctx.
    - replace (T.|[ren (+S x)]) with (T.|[ren (+x)].|[ren (+1)]); last by asimpl.
      have HstΓ: stamped_ctx g Γ. by inverse Hctx.
      eapply (@is_stamped_ren_ty (length Γ) (T.|[ren (+x)]) g), IHx; eauto.
      by eapply stamped_nclosed_lookup.
  Qed.

    (* move => Hfv s1 s2 HsEq.
    specialize (Hfv s1 s2). asimpl in Hfv.

    rewrite ?(decomp_s _ s1) ?(decomp_s _ s2) ?(decomp_s_vl _ s1) ?(decomp_s_vl _ s2).
    rewrite /up /scons.
    injection (Hfv _ _ (eq_n_s_tails HsEq)).
    About eq_n_s_heads.
    rewrite (eq_n_s_heads HsEq).
      by rewritePremises ].

    solve_inv_fv_congruence.
    specialize (Hcl s1 s2). asimpl in Hcl. *)

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
      by eapply is_stamped_sub_one.
    - specialize (H Hctx). inverse H. cbn in *.
      eapply is_stamped_sub_rev_ty => //.
      by eapply nclosed_ren_inv_ty, is_stamped_nclosed_ty.
    - apply stamped_exp_subject in t. inverse t.
      specialize (H Hctx). inverse H.
      by eapply is_stamped_sub_one.
    (* - constructor; eauto. apply stamped_ren. (* Needed: the context is well-stamped as well! *) admit. *)
    - constructor; cbn; eauto. apply H.
      econstructor; eauto.
      eapply is_stamped_ren_ty in f => //.
      by eapply is_stamped_nclosed_ty.
    - constructor =>/=. eapply is_stamped_sub_rev_ty; eauto.
      eapply nclosed_sub_inv. eauto using is_stamped_nclosed_ty.
    - by apply stamped_lookup.
    - have Hctx': stamped_ctx getStampTable (TLater V :: Γ). by constructor => //; constructor.
      specialize (H Hctx'); specialize (H0 Hctx'); ev; constructor; auto.
    - have Hctx': stamped_ctx getStampTable (V :: Γ). by constructor.
      specialize (H Hctx'); ev; constructor; auto.
    - have HsT1: is_stamped_ty (S (length Γ)) getStampTable (iterate TLater i T1).
      + move=> {s} {H}. elim: i => [|i IHi] //=. rewrite iterate_S. by constructor.
      + have Hctx': stamped_ctx getStampTable (iterate TLater i T1 :: Γ). by constructor.
        specialize (H Hctx'); ev; constructor; auto.
    - constructor; eauto. eapply is_stamped_ren_ty in f. by constructor.
      by eapply is_stamped_nclosed_ty.
    - constructor; eauto. eapply is_stamped_ren_ty in f. by constructor.
      by eapply is_stamped_nclosed_ty.
    - have Hctx': stamped_ctx getStampTable (T2.|[ren (+1)] :: Γ).
        constructor => //.
        eapply is_stamped_sub_ty => //. apply is_stamped_ren_shift; lia.
      specialize (H Hctx); specialize (H0 Hctx');
        ev; constructor; eauto.
  Qed.
End syntyping.

Notation "Γ ⊢ₜ e : T " := (typed Γ e T).
Notation "Γ |ds V ⊢ ds : T" := (dms_typed Γ V ds T).
Notation "Γ |d V ⊢ d : T" := (dm_typed Γ V d T).
Notation "Γ ⊢ₚ p : T , i" := (path_typed Γ p T i).
Notation "Γ ⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).
