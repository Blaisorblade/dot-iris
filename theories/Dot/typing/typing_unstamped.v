(**
  An unstamped typing judgment for Dot, allowing only variables in paths, and not arbitrary values.
  We show that unstamped typing derivations from here can
  be converted to stamped derivations of this typing judgment, in lemma
  [stamp_typing_mut].
*)
From D Require Import tactics.
From D.Dot.syn Require Export syn path_repl lr_syn_aux.
From D.Dot.typing Require Export typing_aux_defs.
From D.Dot.stamping Require Export stampingDefsCore.

Set Implicit Arguments.

Implicit Types (L T U : ty) (v : vl) (e : tm) (d : dm) (p: path) (ds : dms) (Γ : list ty).

(* The typing judgement comes from [s/⊢/u⊢/] over [Dot/typing_stamped.v], and dropping stamping. *)
Reserved Notation "Γ u⊢ₜ e : T" (at level 74, e, T at next level).
Reserved Notation "Γ u⊢ₚ p : T , i" (at level 74, p, T, i at next level).
Reserved Notation "Γ u⊢{ l := d  } : T" (at level 74, l, d, T at next level).
Reserved Notation "Γ u⊢ds ds : T" (at level 74, ds, T at next level).
Reserved Notation "Γ u⊢ₜ T1 , i1 <: T2 , i2" (at level 74, T1, T2, i1, i2 at next level).

(**
Judgments for typing, subtyping, path and definition typing.
*)
Inductive typed Γ : tm → ty → Prop :=
(** First, elimination forms *)
(** Dependent application; only allowed if the argument is a path. *)
| App_path_typed p2 e1 T1 T2:
    is_unstamped_ty' (S (length Γ)) T2 →
    is_unstamped_path' (length Γ) p2 →
    (* T2 .Tp[ p2 /]~ T2' → *)
    Γ u⊢ₜ e1: TAll T1 T2 →
    Γ u⊢ₚ p2 : T1, 0 →
    (*────────────────────────────────────────────────────────────*)
    Γ u⊢ₜ tapp e1 (path2tm p2) : T2 .Tp[ p2 /]
(** Non-dependent application; allowed for any argument. *)
| App_typed e1 e2 T1 T2:
    Γ u⊢ₜ e1: TAll T1 (shift T2) →      Γ u⊢ₜ e2 : T1 →
    (*────────────────────────────────────────────────────────────*)
    Γ u⊢ₜ tapp e1 e2 : T2
| Proj_typed e T l:
    Γ u⊢ₜ e : TVMem l T →
    (*─────────────────────────*)
    Γ u⊢ₜ tproj e l : T
(** Introduction forms *)
| Lam_typed_strong e T1 T2 Γ':
    ⊢G Γ <:* TLater <$> Γ' →
    is_unstamped_ty' (length Γ) T1 →
    (* T1 :: Γ' u⊢ₜ e : T2 → (* Would work, but allows the argument to occur in its own type. *) *)
    shift T1 :: Γ' u⊢ₜ e : T2 →
    (*─────────────────────────*)
    Γ u⊢ₜ tv (vabs e) : TAll T1 T2
| VObj_typed ds T:
    Γ |L T u⊢ds ds: T →
    is_unstamped_ty' (S (length Γ)) T →
    (*──────────────────────*)
    Γ u⊢ₜ tv (vobj ds): TMu T

(** "General" rules *)
| Var_typed x T :
    (* After looking up in Γ, we must weaken T for the variables on top of x. *)
    Γ !! x = Some T →
    (*──────────────────────*)
    Γ u⊢ₜ tv (var_vl x) : shiftN x T
| Subs_typed e T1 T2 i :
    Γ u⊢ₜ T1, 0 <: T2, i → Γ u⊢ₜ e : T1 →
    (*───────────────────────────────*)
    Γ u⊢ₜ iterate tskip i e : T2
| Path_typed p T :
    Γ u⊢ₚ p : T, 0 →
    (*───────────────────────────────*)
    Γ u⊢ₜ path2tm p : T

(** Primitives. *)
| T_Nat_typed n:
    Γ u⊢ₜ tv (vnat n): TNat
| T_Bool_typed b:
    Γ u⊢ₜ tv (vbool b): TBool
| T_Un_typed u e1 B1 Br (Hu : un_op_syntype u B1 Br) :
    Γ u⊢ₜ e1 : TPrim B1 →
    Γ u⊢ₜ tun u e1 : TPrim Br
| T_Bin_typed b e1 e2 B1 B2 Br (Hu : bin_op_syntype b B1 B2 Br) :
    Γ u⊢ₜ e1 : TPrim B1 →
    Γ u⊢ₜ e2 : TPrim B2 →
    Γ u⊢ₜ tbin b e1 e2 : TPrim Br
| T_If_typed e e1 e2 T :
    Γ u⊢ₜ e: TBool →
    Γ u⊢ₜ e1 : T →
    Γ u⊢ₜ e2 : T →
    Γ u⊢ₜ tif e e1 e2 : T
where "Γ u⊢ₜ e : T " := (typed Γ e T)
with dms_typed Γ : dms → ty → Prop :=
| dnil_typed : Γ u⊢ds [] : TTop
(* This demands definitions and members to be defined in aligned lists. *)
| dcons_typed l d ds T1 T2:
    Γ u⊢{ l := d } : T1 →
    Γ u⊢ds ds : T2 →
    dms_hasnt ds l →
    (*──────────────────────*)
    Γ u⊢ds (l, d) :: ds : TAnd T1 T2
where "Γ u⊢ds ds : T" := (dms_typed Γ ds T)
with dm_typed Γ : label → dm → ty → Prop :=
| dty_typed T l L U:
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ TLater L, 0 <: TLater T, 0 →
    Γ u⊢ₜ TLater T, 0 <: TLater U, 0 →
    Γ u⊢{ l := dtysyn T } : TTMem l L U
| dpt_pv_typed l v T:
    Γ u⊢ₜ tv v : T →
    Γ u⊢{ l := dpt (pv v) } : TVMem l T
| dpath_typed l p T:
    Γ u⊢ₚ p : T, 0 →
    is_unstamped_path (length Γ) AlsoNonVars p →
    Γ u⊢{ l := dpt p } : TVMem l T
| dnew_typed l T ds:
    TAnd (TLater T) (TSing (pself (pv (ids 1)) l)) :: Γ u⊢ds ds : T →
    is_unstamped_ty' (S (length Γ)) T →
    Γ u⊢{ l := dpt (pv (vobj ds)) } : TVMem l (TMu T)
| dpt_sub_typed T1 T2 p l:
    Γ u⊢ₜ T1, 0 <: T2, 0 →
    Γ u⊢{ l := dpt p } : TVMem l T1 →
    Γ u⊢{ l := dpt p } : TVMem l T2
where "Γ u⊢{ l := d  } : T" := (dm_typed Γ l d T)
with path_typed Γ : path → ty → nat → Prop :=
| pv_typed x T:
    Γ u⊢ₜ tv (var_vl x) : T →
    Γ u⊢ₚ pv (var_vl x) : T, 0
(* Mnemonic: Path from SELecting a Field *)
| pself_typed p T i l:
    Γ u⊢ₚ p : TVMem l T, i →
    Γ u⊢ₚ pself p l : T, i
| p_subs_typed p T1 T2 i j :
    Γ u⊢ₜ T1, i <: T2, i + j →
    Γ u⊢ₚ p : T1, i →
    (*───────────────────────────────*)
    Γ u⊢ₚ p : T2, i + j
| p_mu_i_typed p T {i} :
    is_unstamped_ty' (S (length Γ)) T →
    Γ u⊢ₚ p : T .Tp[ p /], i →
    Γ u⊢ₚ p : TMu T, i
| p_mu_e_typed p T {i} :
    is_unstamped_ty' (S (length Γ)) T →
    Γ u⊢ₚ p : TMu T, i →
    Γ u⊢ₚ p : T .Tp[ p /], i
| pself_inv_typed p T i l:
    Γ u⊢ₚ pself p l : T, i →
    (*─────────────────────────*)
    Γ u⊢ₚ p : TVMem l T, i
| psingleton_refl_typed T p i :
    Γ u⊢ₚ p : T, i →
    Γ u⊢ₚ p : TSing p, i
| psingleton_inv_typed p q i:
    Γ u⊢ₚ p : TSing q, i →
    is_unstamped_path' (length Γ) q →
    Γ u⊢ₚ q : TTop, i
| psingleton_trans p q T i:
    Γ u⊢ₚ p : TSing q, i →
    Γ u⊢ₚ q : T, i →
    Γ u⊢ₚ p : T, i
| psingleton_elim T p q l i:
    Γ u⊢ₚ p : TSing q, i →
    Γ u⊢ₚ pself q l : T, i →
    Γ u⊢ₚ pself p l : TSing (pself q l), i
where "Γ u⊢ₚ p : T , i" := (path_typed Γ p T i)
(* Γ u⊢ₜ T1, i1 <: T2, i2 means that TLater^i1 T1 <: TLater^i2 T2. *)
with subtype Γ : ty → nat → ty → nat → Prop :=
| Refl_stp i T :
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ T, i <: T, i
| Trans_stp i2 T2 {i1 i3 T1 T3}:
    Γ u⊢ₜ T1, i1 <: T2, i2 →
    Γ u⊢ₜ T2, i2 <: T3, i3 →
    Γ u⊢ₜ T1, i1 <: T3, i3
| TLaterL_stp i T:
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ TLater T, i <: T, S i
| TLaterR_stp i T:
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ T, S i <: TLater T, i

(* "Structural" rule about indexes *)
| TAddLater_stp T i:
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ T, i <: TLater T, i

(* "Logical" connectives *)
| Top_stp i T :
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ T, i <: TTop, i
| Bot_stp i T :
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ TBot, i <: T, i
| TAnd1_stp T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ u⊢ₜ TAnd T1 T2, i <: T1, i
| TAnd2_stp T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ u⊢ₜ TAnd T1 T2, i <: T2, i
| TAnd_stp T U1 U2 i j:
    Γ u⊢ₜ T, i <: U1, j →
    Γ u⊢ₜ T, i <: U2, j →
    Γ u⊢ₜ T, i <: TAnd U1 U2, j
| TOr1_stp T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ u⊢ₜ T1, i <: TOr T1 T2, i
| TOr2_stp T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ u⊢ₜ T2, i <: TOr T1 T2, i
| TOr_stp T1 T2 U i j:
    Γ u⊢ₜ T1, i <: U, j →
    Γ u⊢ₜ T2, i <: U, j →
    Γ u⊢ₜ TOr T1 T2, i <: U, j

(* Type selections *)
| SelU_stp p L {l U i}:
    Γ u⊢ₚ p : TTMem l L U, i →
    Γ u⊢ₜ TSel p l, i <: TLater U, i
| LSel_stp p U {l L i}:
    Γ u⊢ₚ p : TTMem l L U, i →
    Γ u⊢ₜ TLater L, i <: TSel p l, i
| PSub_singleton_stp p q {i T1 T2}:
    T1 ~Tp[ p := q ]* T2 →
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ u⊢ₚ p : TSing q, i →
    Γ u⊢ₜ T1, i <: T2, i
| PSym_singleton_stp T {p q i}:
    Γ u⊢ₚ p : T, i →
    Γ u⊢ₜ TSing p, i <: TSing q, i →
    Γ u⊢ₜ TSing q, i <: TSing p, i
| PSelf_singleton_stp {p T i} :
    Γ u⊢ₚ p : T, i →
    Γ u⊢ₜ TSing p, i <: T, i

(* TODO: figure out if the drugs I had when I wrote these rules were good or bad. *)
(* | SelU_stp l L U p i j: *)
(*     Γ u⊢ₚ p : TTMem l L U, i → *)
(*     Γ u⊢ₜ TSel p l, j <: U, S (i + j) *)
(* | LSel_stp l L U p i j: *)
(*     Γ u⊢ₚ p : TTMem l L U, i → *)
(*     Γ u⊢ₜ L, S (i + j) <: TSel p l, j *)

(* Subtyping for recursive types. Congruence, and opening in both directions. *)
| Mu_stp_mu T1 T2 i j:
    (iterate TLater i T1 :: Γ) u⊢ₜ T1, i <: T2, j →
    is_unstamped_ty' (S (length Γ)) T1 →
    Γ u⊢ₜ TMu T1, i <: TMu T2, j
| Mu_stp T i:
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ TMu (shift T), i <: T, i
| Stp_mu T i:
    is_unstamped_ty' (length Γ) T →
    Γ u⊢ₜ T, i <: TMu (shift T), i

(* "Congruence" or "variance" rules for subtyping. Unneeded for "logical" types.
 "Cov" stands for covariance, "Con" for contravariance. *)
| TAllConCov_stp T1 T2 U1 U2 i:
    Γ u⊢ₜ TLater T2, i <: TLater T1, i →
    iterate TLater (S i) (shift T2) :: Γ u⊢ₜ TLater U1, i <: TLater U2, i →
    is_unstamped_ty' (length Γ) T2 →
    Γ u⊢ₜ TAll T1 U1, i <: TAll T2 U2, i
| TVMemCov_stp T1 T2 i l:
    Γ u⊢ₜ T1, i <: T2, i →
    Γ u⊢ₜ TVMem l T1, i <: TVMem l T2, i
| TTMemConCov_stp L1 L2 U1 U2 i l:
    Γ u⊢ₜ TLater L2, i <: TLater L1, i →
    Γ u⊢ₜ TLater U1, i <: TLater U2, i →
    Γ u⊢ₜ TTMem l L1 U1, i <: TTMem l L2 U2, i
  (* Is it true that for covariant F, F[A ∧ B] = F[A] ∧ F[B]?
    Dotty assumes that, tho DOT didn't capture it.
    F[A ∧ B] <: F[A] ∧ F[B] is provable by covariance.
    Let's prove F[A] ∧ F[B] <: F[A ∧ B] in the model.
    *)
| TAllDistr_stp T U1 U2 i:
    is_unstamped_ty' (length Γ) T →
    is_unstamped_ty' (S (length Γ)) U1 →
    is_unstamped_ty' (S (length Γ)) U2 →
    Γ u⊢ₜ TAnd (TAll T U1) (TAll T U2), i <: TAll T (TAnd U1 U2), i
| TVMemDistr_stp l T1 T2 i:
    is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 →
    Γ u⊢ₜ TAnd (TVMem l T1) (TVMem l T2), i <: TVMem l (TAnd T1 T2), i
| TTMemDistr_stp l L U1 U2 i:
    is_unstamped_ty' (length Γ) L →
    is_unstamped_ty' (length Γ) U1 →
    is_unstamped_ty' (length Γ) U2 →
    Γ u⊢ₜ TAnd (TTMem l L U1) (TTMem l L U2), i <: TTMem l L (TAnd U1 U2), i

(* "Structural" rule about indexes. Only try last. *)
| TLater_Mono_stp T1 T2 i j:
    Γ u⊢ₜ T1, i <: T2, j →
    Γ u⊢ₜ TLater T1, i <: TLater T2, j
where "Γ u⊢ₜ T1 , i1 <: T2 , i2" := (subtype Γ T1 i1 T2 i2).

(* Make [T] first argument: Hide Γ for e.g. typing examples. *)
Global Arguments dty_typed {Γ} T _ _ _ _ _ _ : assert.

Scheme unstamped_typed_mut_ind := Induction for typed Sort Prop
with   unstamped_dms_typed_mut_ind := Induction for dms_typed Sort Prop
with   unstamped_dm_typed_mut_ind := Induction for dm_typed Sort Prop
with   unstamped_path_typed_mut_ind := Induction for path_typed Sort Prop
with   unstamped_subtype_mut_ind := Induction for subtype Sort Prop.

Combined Scheme unstamped_typing_mut_ind from unstamped_typed_mut_ind, unstamped_dms_typed_mut_ind, unstamped_dm_typed_mut_ind,
  unstamped_path_typed_mut_ind, unstamped_subtype_mut_ind.

Hint Constructors typed dms_typed dm_typed path_typed subtype : core.
Remove Hints Trans_stp : core.
Hint Extern 10 => try_once Trans_stp : core.

Ltac ettrans := eapply Trans_stp.

Lemma AddIJ_stp {Γ T} i j (Hst: is_unstamped_ty' (length Γ) T) :
  Γ u⊢ₜ T, j <: T, i + j.
Proof.
  elim: i => [|n IHn]; first by auto.
  ettrans; first apply IHn.
  ettrans; [exact: TAddLater_stp | by constructor].
Qed.

Lemma AddIJ_stp' {Γ T} i j (Hst: is_unstamped_ty' (length Γ) T) (Hle : i <= j) :
  Γ u⊢ₜ T, i <: T, j.
Proof. rewrite (le_plus_minus i j Hle) Nat.add_comm. exact: AddIJ_stp. Qed.

Lemma AddI_stp Γ T i (Hst: is_unstamped_ty' (length Γ) T) :
  Γ u⊢ₜ T, 0 <: T, i.
Proof. apply (AddIJ_stp' (i := 0) (j := i)); by [|lia]. Qed.

Lemma Sub_later_shift {Γ T1 T2 i j}
  (Hs1: is_unstamped_ty' (length Γ) T1)
  (Hs2: is_unstamped_ty' (length Γ) T2)
  (Hsub: Γ u⊢ₜ T1, S i <: T2, S j):
  Γ u⊢ₜ TLater T1, i <: TLater T2, j.
Proof.
  ettrans; first exact: TLaterL_stp.
  by eapply Trans_stp, TLaterR_stp.
Qed.

Lemma Sub_later_shift_inv {Γ T1 T2 i j}
  (Hs1: is_unstamped_ty' (length Γ) T1)
  (Hs2: is_unstamped_ty' (length Γ) T2)
  (Hsub: Γ u⊢ₜ TLater T1, i <: TLater T2, j):
  Γ u⊢ₜ T1, S i <: T2, S j.
Proof.
  ettrans; first exact: TLaterR_stp.
  by eapply Trans_stp, TLaterL_stp.
Qed.

Lemma path_tp_weaken {Γ p T i j} (Hst: is_unstamped_ty' (length Γ) T) : i <= j →
  Γ u⊢ₚ p : T, i → Γ u⊢ₚ p : T, j.
Proof.
  intros Hle Hp.
  rewrite (le_plus_minus i j Hle); move: {j Hle} (j - i) => k.
  eapply p_subs_typed, Hp.
  apply: AddIJ_stp'; by [|lia].
Qed.

Lemma pv_dlater {Γ p T i} :
  is_unstamped_ty' (length Γ) T →
  Γ u⊢ₚ p : TLater T, i →
  Γ u⊢ₚ p : T, S i.
Proof.
  intros Hu Hp; apply p_subs_typed with (j := 1) (T1 := TLater T) (T2 := T) in Hp;
    move: Hp; rewrite (plusnS i 0) (plusnO i); intros; by [|constructor].
Qed.


(* Lemma delay_stp Γ T1 T2 i j :
  (* is_unstamped_ty' (length Γ) T1 →
  is_unstamped_ty' (length Γ) T2 → *)
  Γ u⊢ₜ T1, i <: T2, j →
  TLater <$> Γ u⊢ₜ T1, S i <: T2, S j.
Proof.
  induction 1;
  try (by constructor; rewrite ?fmap_length //).

  by econstructor.
  (* eapply IHsubtype1 => //.
  eapply IHsubtype2.
  Timeout 1 try_once Trans_stp; eauto.

  econstructor; eauto.
  inverse_is_unstamped. *)
  apply (SelU_stp (L := L)). admit.
    (* (path_tp_weaken (i := i)); rewrite ?fmap_length;
  try by [|lia]. admit.  *)
  apply (LSel_stp (U := U)). admit.
  eapply PSub_singleton_stp; rewrite ?fmap_length //. admit.
  eapply (PSym_singleton_stp (T := T)) =>//. admit.
  eapply PSelf_singleton_stp =>//. admit.
Admitted. *)

Scheme idx_unstamped_path_typed_mut_ind := Induction for path_typed Sort Prop
with   idx_unstamped_subtype_mut_ind := Induction for subtype Sort Prop.
Combined Scheme idx_unstamped_typing_mut_ind from
  idx_unstamped_subtype_mut_ind, idx_unstamped_path_typed_mut_ind.

About idx_unstamped_typing_mut_ind.

Lemma delay_stp_mut Γ :
  (∀ T1 i T2 j,
    (* is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 → *)
    Γ u⊢ₜ T1, i <: T2, j →
    TLater <$> Γ u⊢ₜ T1, S i <: T2, S j)
    ∧
  (∀ p T i,
    (* is_unstamped_ty' (length Γ) T1 →
    is_unstamped_ty' (length Γ) T2 → *)
    Γ u⊢ₚ p : T, i →
    TLater <$> Γ u⊢ₚ p : T , S i).
Proof.
  eapply idx_unstamped_typing_mut_ind with
    (P := λ Γ p T i _,
      (* is_unstamped_ty' (length Γ) T1 →
      is_unstamped_ty' (length Γ) T2 → *)
      TLater <$> Γ u⊢ₚ p : T , S i)
    (P0 := λ Γ T1 i T2 j _,
      (* is_unstamped_ty' (length Γ) T1 →
      is_unstamped_ty' (length Γ) T2 → *)
      (* Γ u⊢ₜ T1, i <: T2, j → *)
      TLater <$> Γ u⊢ₜ T1, S i <: T2, S j); clear Γ; intros;
    try (by constructor; rewrite ?fmap_length);
    try (by econstructor; rewrite ?fmap_length);
    last by eapply (p_subs_typed (i := S i)).

  -
   inverse t.
  + eapply (p_subs_typed (i := 0)); admit. (*Seems doable *)
  + have ?: i = 0 by admit. subst. rewrite ->(iterate_0 tskip) in *. simplify_eq/=. admit. (* Nope *)
  +  destruct p; simplify_eq/=. (* Nope *)
  admit.
  -
  - econstructor; rewrite ?fmap_length //.
  7: by econstructor.
  apply
  econstructor.



Axiom undelay_stp : ∀ Γ Γ' T1 T2 i j,
  ⊢G Γ <:* Γ' →
  Γ' u⊢ₜ T1, i <: T2, j →
  Γ u⊢ₜ T1, i <: T2, j.

Lemma TMono_stp_adm {Γ T1 T2 i j} :
  Γ u⊢ₜ T1, i <: T2, j →
  Γ u⊢ₜ T1, S i <: T2, S j.
Proof. intros Hs; eapply undelay_stp, delay_stp, Hs; ietp_weaken_ctx. Qed.
by
eauto.
induction 1; try by econstructor.

 (path_tp_weaken (i := i)); rewrite ?fmap_length;
 apply (LSel_stp (U := U)), (path_tp_weaken (i := i)); rewrite ?fmap_length;
 try by [|lia]. admit.

 u⊢ₚ p : TSing q, i


    (* (∀ p T i, Γ v⊢ₚ[ g ] p : T , i → ∀ (Hctx: stamped_ctx g Γ), is_stamped_ty (length Γ) g T) ∧ *)
 repeat constructor.
 apply LSel_stp.
 econstructor.
  - 3: rewrite ?fmap_length //.

constructor.
1-24: try by econstructor; rewrite ?fmap_length.



Lemma TMono_stp_adm {Γ T1 T2 i j} :
  Γ u⊢ₜ T1, i <: T2, j →
  Γ u⊢ₜ T1, S i <: T2, S j.
Proof. induction 1; try by econstructor.
admit.
admit.
admit.
admit.
admit.

(* False *)
constructor=>//. admit.
constructor=>//.
Timeout 1 eauto.


Lemma unstamped_path_root_is_var Γ p T i:
  Γ u⊢ₚ p : T, i → ∃ x, path_root p = var_vl x.
Proof. by elim; intros; cbn; eauto 2 using is_unstamped_path_root. Qed.

Lemma dtysem_not_utyped Γ l d T :
  Γ u⊢{ l := d } : T → ∀ σ s, d ≠ dtysem σ s.
Proof. by case. Qed.

Lemma Lam_typed Γ e T1 T2:
  is_unstamped_ty' (length Γ) T1 →
  shift T1 :: Γ u⊢ₜ e : T2 →
  (*─────────────────────────*)
  Γ u⊢ₜ tv (vabs e) : TAll T1 T2.
Proof. apply Lam_typed_strong. ietp_weaken_ctx. Qed.

Lemma Lam_typed_strip1 Γ e V T1 T2:
  is_unstamped_ty' (S (length Γ)) T1 →
  shift T1 :: V :: Γ u⊢ₜ e : T2 →
  (*─────────────────────────*)
  Γ |L V u⊢ₜ tv (vabs e) : TAll T1 T2.
Proof.
  intros. apply Lam_typed_strong with (Γ' := (V :: Γ)) => //.
  rewrite /defCtxCons/=; ietp_weaken_ctx.
Qed.

Lemma dvabs_typed' Γ V T1 T2 e l:
  is_unstamped_ty' (S (length Γ)) T1 →
  shift T1 :: V :: Γ u⊢ₜ e : T2 →
  Γ |L V u⊢{ l := dpt (pv (vabs e)) } : TVMem l (TAll T1 T2).
Proof. by intros; apply dpt_pv_typed, Lam_typed_strip1. Qed.


Lemma TMono_stp {Γ T1 T2 i j} :
  Γ u⊢ₜ T1, i <: T2, j →
  is_unstamped_ty' (length Γ) T1 →
  is_unstamped_ty' (length Γ) T2 →
  Γ u⊢ₜ T1, S i <: T2, S j.
Proof.
  intros.
  ettrans; first exact: TLaterR_stp.
  ettrans; last exact: TLaterL_stp.
  exact: TLater_Mono_stp.
Qed.

Ltac typconstructor :=
  match goal with
  | |- typed _ _ _ => first [apply Lam_typed_strip1 | apply Lam_typed | constructor]
  | |- dms_typed _ _ _ => constructor
  | |- dm_typed _ _ _ _ => first [apply dvabs_typed' | constructor]
  | |- path_typed _ _ _ _ => first [apply pv_dlater | constructor]
  | |- subtype _ _ _ _ _ =>
    first [apply Sub_later_shift | constructor ]
  end.
