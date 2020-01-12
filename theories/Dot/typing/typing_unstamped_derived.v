From stdpp Require Import strings.
From D Require Import tactics.
From D.Dot Require Import syn synLemmas exampleInfra typing_unstamped.
From D.Dot Require Import unstampedness_binding.
Import DBNotation.

Lemma is_unstamped_pvar i n : i < n → is_unstamped_path n (pv (var_vl i)).
Proof. eauto. Qed.
Hint Resolve is_unstamped_pvar : core.
Lemma is_unstamped_pvars i n l : i < n → is_unstamped_ty n (pv (var_vl i) @; l).
Proof. eauto. Qed.
Hint Resolve is_unstamped_pvars : core.

Ltac typconstructor := match goal with
  | |- typed _ _ _ => constructor
  | |- dms_typed _ _ _ _ => constructor
  | |- dm_typed _ _ _ _ _ => constructor
  | |- path_typed _ _ _ _ => constructor
  | |- subtype _ _ _ _ _ => constructor
  end.

(* Ltac tcrush := repeat first [ fast_done | typconstructor | stcrush ]. *)
Ltac tcrush := repeat first [ eassumption | reflexivity | typconstructor | stcrush ].

Lemma is_unstamped_TLater_n i {n T}:
  is_unstamped_ty n T →
  is_unstamped_ty n (iterate TLater i T).
Proof. elim: i => [|//i IHi]; rewrite ?iterate_0 ?iterate_S //; auto. Qed.

Ltac wtcrush := repeat first [ fast_done | typconstructor | stcrush ] ; try solve [
  first [
    by eauto 3 using is_unstamped_TLater_n, is_unstamped_ren1_ty, is_unstamped_ren1_path |
    try_once is_unstamped_weaken_dm |
    try_once is_unstamped_weaken_ty |
    try_once is_unstamped_weaken_path ]; eauto].

Ltac ettrans := eapply Trans_stp.

Ltac asideLaters :=
  repeat first
    [ettrans; last (apply TLaterR_stp; tcrush)|
    ettrans; first (apply TLaterL_stp; tcrush)].

Ltac lNext := ettrans; first apply TAnd2_stp; tcrush.
Ltac lThis := ettrans; first apply TAnd1_stp; tcrush.


(* Copy of the one from unary_lr. Maybe move again back elsewhere. *)
Definition label_of_ty T : option label :=
  match T with
  | TTMem l _ _ => Some l
  | TVMem l _ => Some l
  | _ => None
  end.

Ltac lookup :=
  lazymatch goal with
  | |- _ u⊢ₜ ?T1, _ <: ?T2, _ =>
    let T1' := eval hnf in T1 in
    match T1' with
    | (TAnd ?T11 ?T12) =>
      (* first [unify (label_of_ty T11) (label_of_ty T2); lThis | lNext] *)
      let ls := eval cbv in (label_of_ty T11, label_of_ty T2) in
      match ls with
      | (Some ?l1, Some ?l1) => lThis
      | (Some ?l1, Some ?l2) => lNext
      end
    end
  end.
Ltac ltcrush := tcrush; repeat lookup.

Ltac hideCtx' Γ :=
  let x := fresh "Γ" in set x := Γ.
Ltac hideCtx :=
  match goal with
  | |- ?Γ u⊢ₜ _ : _ => hideCtx' Γ
  | |- ?Γ u⊢ₜ _, _ <: _, _ => hideCtx' Γ
  | |- ?Γ u⊢ₚ _ : _, _  => hideCtx' Γ
  | |- ?Γ |d _ u⊢{ _ := _  } : _ => hideCtx' Γ
  | |- ?Γ |ds _ u⊢ _ : _ => hideCtx' Γ
  end.

Lemma Var_typed' Γ x T1 T2 :
  Γ !! x = Some T1 →
  T2 = T1.|[ren (+x)] →
  (*──────────────────────*)
  Γ u⊢ₜ tv (var_vl x) : T2.
Proof. intros; subst; tcrush. Qed.

Lemma Var0_typed Γ T :
  Γ !! 0 = Some T →
  (*──────────────────────*)
  Γ u⊢ₜ tv (var_vl 0) : T.
Proof. intros; eapply Var_typed'; by rewrite ?hsubst_id. Qed.

Ltac var := exact: Var0_typed || exact: Var_typed'.

Lemma Subs_typed_nocoerce T1 T2 {Γ e} :
  Γ u⊢ₜ e : T1 →
  Γ u⊢ₜ T1, 0 <: T2, 0 →
  Γ u⊢ₜ e : T2.
Proof. rewrite -(iterate_0 tskip e). eauto. Qed.
Hint Resolve Subs_typed_nocoerce : core.

Lemma Var_typed_sub Γ x T1 T2 :
  Γ !! x = Some T1 →
  Γ u⊢ₜ T1.|[ren (+x)], 0 <: T2, 0 →
  (*──────────────────────*)
  Γ u⊢ₜ tv (var_vl x) : T2.
Proof. by intros; eapply Subs_typed_nocoerce; [var|]. Qed.

Lemma Var0_typed_sub Γ T1 T2 :
  Γ !! 0 = Some T1 →
  Γ u⊢ₜ T1, 0 <: T2, 0 →
  (*──────────────────────*)
  Γ u⊢ₜ tv (var_vl 0) : T2.
Proof. intros. by eapply Var_typed_sub; [| rewrite ?hsubst_id]. Qed.

Ltac varsub := (eapply Var0_typed_sub || eapply Var_typed_sub); first done.

Lemma Appv_typed' T2 {Γ e1 x2 T1 T3} :
  Γ u⊢ₜ e1: TAll T1 T2 →                        Γ u⊢ₜ tv (ids x2) : T1 →
  T3 = T2.|[ids x2/] →
  (*────────────────────────────────────────────────────────────*)
  Γ u⊢ₜ tapp e1 (tv (ids x2)) : T3.
Proof. intros; subst; by econstructor. Qed.

Lemma TMuE_typed' Γ x T1 T2:
  Γ u⊢ₜ tv (ids x): μ T1 →
  T2 = T1.|[ids x/] →
  (*──────────────────────*)
  Γ u⊢ₜ tv (ids x): T2.
Proof. intros; subst; auto. Qed.

Lemma Sub_later_shift {Γ T1 T2 i j}
  (Hs1: is_unstamped_ty (length Γ) T1)
  (Hs2: is_unstamped_ty (length Γ) T2)
  (Hsub: Γ u⊢ₜ T1, S i <: T2, S j):
  Γ u⊢ₜ TLater T1, i <: TLater T2, j.
Proof. by asideLaters. Qed.

Lemma Sub_later_shift_inv {Γ T1 T2 i j}
  (Hs1: is_unstamped_ty (length Γ) T1)
  (Hs2: is_unstamped_ty (length Γ) T2)
  (Hsub: Γ u⊢ₜ TLater T1, i <: TLater T2, j):
  Γ u⊢ₜ T1, S i <: T2, S j.
Proof.
  ettrans; first exact: TLaterR_stp.
  by ettrans; last eapply TLaterL_stp.
Qed.

Lemma LSel_stp' Γ U {p l L i}:
  is_unstamped_ty (length Γ) L →
  Γ u⊢ₚ p : TTMem l L U, i →
  Γ u⊢ₜ L, i <: TSel p l, i.
Proof. intros; ettrans; last exact: (@LSel_stp _ p); tcrush. Qed.

(* Worse than dty_typed, but shown in the paper. *)
Lemma dty_typed_intermediate Γ T V l L U:
  is_unstamped_ty (S (length Γ)) T →
  TLater V :: Γ u⊢ₜ L, 0 <: T, 0 →
  TLater V :: Γ u⊢ₜ T, 0 <: U, 0 →
  Γ |d V u⊢{ l := dtysyn T } : TTMem l L U.
Proof. intros; apply dty_typed; tcrush. Qed.

(** * Manipulating laters, basics. *)

Lemma AddIJ_stp {Γ T} i j (Hst: is_unstamped_ty (length Γ) T) :
  Γ u⊢ₜ T, j <: T, i + j.
Proof.
  elim: i => [|n IHn]; first tcrush.
  ettrans; first apply IHn.
  ettrans; [exact: TAddLater_stp | tcrush].
Qed.

Lemma AddI_stp Γ T i (Hst: is_unstamped_ty (length Γ) T) :
  Γ u⊢ₜ T, 0 <: T, i.
Proof. rewrite -(plusnO i). by apply (AddIJ_stp i 0). Qed.

Lemma AddIB_stp Γ T U i:
  Γ u⊢ₜ T, 0 <: U, 0 →
  Γ u⊢ₜ T, i <: U, i.
Proof.
  move => Hstp; elim: i => [|n IHn]; first tcrush.
  exact: TMono_stp.
Qed.

(** * Derived constructions. *)

Lemma Let_typed Γ t u T U :
  Γ u⊢ₜ t : T →
  T.|[ren (+1)] :: Γ u⊢ₜ u : U.|[ren (+1)] →
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ lett t u : U.
Proof. move => Ht Hu HsT. apply /App_typed /Ht /Lam_typed /Hu /HsT. Qed.

Lemma val_LB T U Γ i x l :
  Γ u⊢ₜ tv (ids x) : type l >: T <: U →
  Γ u⊢ₜ ▶: T, i <: (pv (ids x) @; l), i.
Proof. intros; apply /AddIB_stp /(@LSel_stp _ (pv _)); tcrush. Qed.

Lemma val_UB T L Γ i x l :
  Γ u⊢ₜ tv (ids x) : type l >: L <: T →
  Γ u⊢ₜ (pv (ids x) @; l), i <: ▶: T, i.
Proof. intros; eapply AddIB_stp, SelU_stp; tcrush. Qed.

(* These rules from storeless typing must be encoded somehow via variables. *)
(* Lemma packTV_LB T n Γ i :
  is_unstamped_ty n T →
  n <= length Γ →
  Γ u⊢ₜ ▶: T, i <: (pv (packTV T) @; "A"), i.
Proof. intros; apply /val_LB /packTV_typed'. Qed. *)

(* Lemma packTV_UB T n Γ i :
  is_unstamped_ty n T →
  n <= length Γ →
  Γ u⊢ₜ (pv (packTV T) @; "A"), i <: ▶: T, i.
Proof. intros; by apply /val_UB /packTV_typed'. Qed. *)

Lemma Dty_typed Γ T V l:
  is_unstamped_ty (S (length Γ)) T →
  Γ |d V u⊢{ l := dtysyn T } : TTMem l T T.
Proof. intros. tcrush. Qed.

(* We can derive rules Bind1 and Bind2 (the latter only conjectured) from
  "Type Soundness for Dependent Object Types (DOT)", Rompf and Amin, OOPSLA '16. *)
Lemma Bind1 Γ T1 T2 i:
  is_unstamped_ty (S (length Γ)) T1 → is_unstamped_ty (length Γ) T2 →
  iterate TLater i T1 :: Γ u⊢ₜ T1, i <: T2.|[ren (+1)], i →
  Γ u⊢ₜ μ T1, i <: T2, i.
Proof.
  intros Hus1 Hus2 Hsub.
  ettrans; first exact: (Mu_stp_mu Hsub).
  exact: Mu_stp.
Qed.

Lemma Bind2 Γ T1 T2 i:
  is_unstamped_ty (length Γ) T1 → is_unstamped_ty (S (length Γ)) T2 →
  iterate TLater i T1.|[ren (+1)] :: Γ u⊢ₜ T1.|[ren (+1)], i <: T2, i →
  Γ u⊢ₜ T1, i <: μ T2, i.
Proof.
  intros Hus1 Hus2 Hsub.
  ettrans; last apply (Mu_stp_mu Hsub); [exact: Stp_mu | wtcrush].
Qed.

Lemma Bind1' Γ T1 T2:
  is_unstamped_ty (S (length Γ)) T1 → is_unstamped_ty (length Γ) T2 →
  T1 :: Γ u⊢ₜ T1, 0 <: T2.|[ren (+1)], 0 →
  Γ u⊢ₜ μ T1, 0 <: T2, 0.
Proof. intros; exact: Bind1. Qed.

Lemma Bind2' Γ T1 T2:
  is_unstamped_ty (length Γ) T1 → is_unstamped_ty (S (length Γ)) T2 →
  T1.|[ren (+1)] :: Γ u⊢ₜ T1.|[ren (+1)], 0 <: T2, 0 →
  Γ u⊢ₜ T1, 0 <: μ T2, 0.
Proof. intros; exact: Bind2. Qed.

Ltac mltcrush := tcrush; try ((apply Bind1' || apply Bind1); tcrush); repeat lookup.

(* Simplified package introduction, for talk. *)
Lemma BindSpec Γ (L T U : ty):
  is_unstamped_ty (S (length Γ)) T →
  is_unstamped_ty (S (length Γ)) L → is_unstamped_ty (S (length Γ)) U →
  {@ type "A" >: T <: T }%ty :: Γ u⊢ₜ L, 0 <: T, 0 →
  {@ type "A" >: T <: T }%ty :: Γ u⊢ₜ T, 0 <: U, 0 →
  Γ u⊢ₜ tv (ν {@ type "A" = T }) : μ {@ type "A" >: L <: U }.
Proof.
  intros; eapply Subs_typed_nocoerce; tcrush; rewrite iterate_0.
  ltcrush.
Qed.

Lemma p_subs_typed' {Γ p T1 T2 i} :
  Γ u⊢ₜ T1, i <: T2, i →
  Γ u⊢ₚ p : T1, i →
  (*───────────────────────────────*)
  Γ u⊢ₚ p : T2, i.
Proof.
  intros; rewrite -(plusnO i).
  by eapply p_subs_typed; rewrite ?plusnO.
Qed.

Lemma psingleton_sym_typed Γ p q i:
  is_unstamped_path (length Γ) q →
  Γ u⊢ₚ p : TSing q, i →
  Γ u⊢ₚ q : TSing p, i.
Proof.
  intros Hus Hpq. eapply p_subs_typed'.
  eapply (PSym_singleton_stp Hpq). by apply PSelf_singleton_stp, Hpq.
  eapply psingleton_refl_typed.
  by apply (psingleton_inv_typed Hpq).
Qed.

Lemma PSub_singleton_stp_inv {Γ i p q T1 T2}:
  T1 ~Tp[ p := q ]* T2 →
  is_unstamped_ty (length Γ) T1 →
  is_unstamped_ty (length Γ) T2 →
  is_unstamped_path (length Γ) p →
  Γ u⊢ₚ q : TSing p, i →
  Γ u⊢ₜ T1, i <: T2, i.
Proof. intros. by eapply PSub_singleton_stp, psingleton_sym_typed. Qed.

Lemma pand_typed {Γ p T1 T2 i}:
  Γ u⊢ₚ p : T1, i →
  Γ u⊢ₚ p : T2, i →
  Γ u⊢ₚ p : TAnd T1 T2, i.
Proof.
  intros Hp1 Hp2. eapply p_subs_typed', psingleton_refl_typed, Hp1.
  constructor; exact: PSelf_singleton_stp.
Qed.

Lemma Mu_stp' {Γ T T' i}:
  T' = shift T →
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ μ T', i <: T, i.
Proof. intros; subst. auto. Qed.

Lemma dvabs_sub_typed {Γ} V T1 T2 e l L:
  shift T1 :: V :: Γ u⊢ₜ e : T2 →
  TLater V :: Γ u⊢ₜ TAll T1 T2, 0 <: L, 0 →
  is_unstamped_ty (S (length Γ)) T1 →
  Γ |d V u⊢{ l := dvl (vabs e) } : TVMem l L.
Proof.
  intros He Hsub Hs.
  eapply dvl_sub_typed; first apply Hsub.
  tcrush.
Qed.

(* Note how we must weaken the type (or its environment) to account for the
   self-variable of the created object. *)
Definition packTV l T := (ν {@ type l = shift T }).

Lemma packTV_typed' T n Γ l :
  is_unstamped_ty n T →
  n <= length Γ →
  Γ u⊢ₜ tv (packTV l T) : typeEq l T.
Proof.
  move => HsT1 Hle; move: (Hle) (HsT1) => /le_n_S Hles /is_unstamped_ren1_ty HsT2.
  apply (Subs_typed_nocoerce (μ {@ typeEq l (shift T) }));
    last (ettrans; first apply (@Mu_stp _ ({@ typeEq l T })); wtcrush).
  apply VObj_typed; wtcrush.
Qed.

Lemma packTV_typed T Γ l :
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ tv (packTV l T) : typeEq l T.
Proof. intros; exact: packTV_typed'. Qed.

Definition tyApp t l T :=
  lett t (lett (tv (packTV l (shift T))) (tapp (tv x1) (tv x0))).

Lemma tyApp_typed Γ T U V t l :
  Γ u⊢ₜ t : TAll (tparam l) U →
  (** This subtyping premise is needed to perform "avoidance", as in compilers
    for ML and Scala: that is, producing a type [V] that does not refer to
    variables bound by let in the expression. *)
  (∀ L, typeEq l T.|[ren (+2)] :: L :: Γ u⊢ₜ U.|[up (ren (+1))], 0 <: V.|[ren (+2)], 0) →
  is_unstamped_ty (length Γ) T →
  is_unstamped_ty (S (length Γ)) U →
  Γ u⊢ₜ tyApp t l T : V.
Proof.
  move => Ht Hsub HuT1 HuU1.
  eapply Let_typed; [exact: Ht| |tcrush].
  eapply Let_typed; [apply packTV_typed| |]; wtcrush.
  rewrite /= -!hrenS -/(typeEq _ _).

  apply /Subs_typed_nocoerce /Hsub.

  eapply Appv_typed'; first var.
  have HuT3 : is_unstamped_ty (S (S (length Γ))) (shiftN 2 T)
    by rewrite hrenS; wtcrush.
  varsub; tcrush; rewrite !hsubst_comp; f_equal. autosubst.
Qed.

(** * Manipulating laters, more.

 *)
Lemma TLaterRN_stp Γ T i j:
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ T, j + i <: iterate TLater j T, i.
Proof.
  elim: j T => /= [|j IHj] T HuT; rewrite ?iterate_0 ?iterate_Sr /=; tcrush.
  ettrans.
  - exact: TLaterR_stp.
  - apply (IHj (TLater T)); stcrush.
Qed.

Lemma TLaterLN_stp {Γ T} i j :
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ iterate TLater j T, i <: T, j + i.
Proof.
  elim: j T => /= [|j IHj] T HuT; rewrite ?iterate_0 ?iterate_Sr /=; tcrush.
  ettrans.
  - apply (IHj (TLater T)); stcrush.
  - exact: TLaterL_stp.
Qed.

(* This can be useful when [T] is a singleton type. *)
Lemma dropLaters Γ e T U i:
  Γ u⊢ₜ e : T →
  Γ u⊢ₜ T, 0 <: iterate TLater i U, 0 →
  is_unstamped_ty (length Γ) T →
  is_unstamped_ty (length Γ) U →
  Γ u⊢ₜ iterate tskip i e : TAnd T U.
Proof.
  intros HeT Hsub HuT HuU.
  eapply Subs_typed, HeT => {HeT}.
  typconstructor; [exact: AddI_stp|] => {HuT}.
  ettrans; [apply: Hsub|] => {Hsub}.
  have := (TLaterLN_stp 0 i HuU); rewrite plusnO; exact.
Qed.

(**
  Like [let: x := e1 in e2], but dropping [i] laters from [e1]'s type while
  preserving its identity by adding a singleton type. See
*)
Definition deLater e1 i e2 := lett e1 (lett (iterate tskip i (tv x0)) e2).

Lemma deLaterSingV0 {Γ} p i e T U:
  Γ u⊢ₚ p : TSing p, 0 →
  shift (TSing p) :: Γ u⊢ₜ shift (TSing p), 0 <: iterate TLater i T, 0 →
  TAnd (TSing (shiftN 2 p)) (shift T) :: TSing (shift p) :: Γ u⊢ₜ e : shiftN 2 U →
  is_unstamped_ty (length Γ) T →
  is_unstamped_path (length Γ) p →
  Γ u⊢ₜ deLater (path2tm p) i e : U.
Proof.
  intros HpT1 Hsub HeU HuT Hup.
  apply Let_typed with (T := TSing p); tcrush.
  apply Let_typed with (T := TAnd (shift (TSing p)) T); rewrite /= -?hrenS; wtcrush.
  apply dropLaters; [ var | .. ]; rewrite /= -?hrenS; wtcrush.
Qed.

(** More general version of [deLaterSingV0]. Not sure if too general or useful. *)
Lemma deLaterSingV1 {Γ} p i e T1 T2 U:
  Γ u⊢ₚ p : T1, 0 →
  shift (TAnd (TSing p) T1) :: Γ u⊢ₜ shift T1, 0 <: iterate TLater i T2, 0 →
  TAnd (TAnd (TSing (shiftN 2 p)) (shiftN 2 T1)) (shift T2) ::
    TAnd (TSing (shift p)) (shift T1) :: Γ u⊢ₜ e : shiftN 2 U →
  is_unstamped_ty (length Γ) T1 →
  is_unstamped_ty (length Γ) T2 →
  is_unstamped_path (length Γ) p →
  Γ u⊢ₜ deLater (path2tm p) i e : U.
Proof.
  intros HpT1 Hsub HeU HuT1 HuT2 Hup.
  apply Let_typed with (T := TAnd (TSing p) T1); tcrush.
  by apply pand_typed, HpT1; eapply psingleton_refl_typed, HpT1.
  apply Let_typed with (T := TAnd (shift (TAnd (TSing p) T1)) T2); rewrite /= -?hrenS; wtcrush.
  apply dropLaters; [ var | lNext | ..]; rewrite /= -?hrenS; wtcrush.
Qed.

(** Best version of [deLaterSing]. *)
Lemma deLaterSing {Γ} p i e T1 U:
  Γ u⊢ₚ p : iterate TLater i T1, 0 →
  TAnd (TSing (shiftN 2 p)) (shiftN 2 T1) ::
    TAnd (TSing (shift p)) (iterate TLater i (shift T1)) :: Γ u⊢ₜ e : shiftN 2 U →
  is_unstamped_ty (length Γ) T1 →
  is_unstamped_path (length Γ) p →
  Γ u⊢ₜ deLater (path2tm p) i e : U.
Proof.
  intros HpT1 HeU HuT1 Hup.
  apply Let_typed with (T := TAnd (TSing p) (iterate TLater i T1)); wtcrush.
  by apply pand_typed, HpT1; eapply psingleton_refl_typed, HpT1.
  apply Let_typed with (T := TAnd (TSing (shift p)) (shift T1));
    rewrite /= -?hrenS ?TLater_subst; wtcrush.
  eapply Subs_typed; last var; tcrush; [lThis|lNext]; wtcrush.
  by apply: AddI_stp; wtcrush.
  rewrite -{3}(plusnO i). apply TLaterLN_stp; wtcrush.
Qed.

Lemma selfIntersect Γ T U i j:
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ T, i <: U, j + i →
  Γ u⊢ₜ T, i <: TAnd U T, j + i .
Proof. intros; tcrush. exact: AddIJ_stp. Qed.

Lemma TDistr_TLater_And_stp Γ T1 T2 i :
  is_unstamped_ty (length Γ) T1 →
  is_unstamped_ty (length Γ) T2 →
  Γ u⊢ₜ TAnd (TLater T1) (TLater T2), i <: TLater (TAnd T1 T2), i.
Proof. intros; asideLaters; tcrush; [lThis|lNext]. Qed.

(** Inverse of [TDistr_TLater_And_stp]. *)
Lemma TDistr_TLater_And_stp_inv Γ T1 T2 i :
  is_unstamped_ty (length Γ) T1 →
  is_unstamped_ty (length Γ) T2 →
  Γ u⊢ₜ TLater (TAnd T1 T2), i <: TAnd (TLater T1) (TLater T2), i.
Proof. intros; tcrush. Qed.

Lemma TDistr_TLater_Or_stp Γ T1 T2 i :
  is_unstamped_ty (length Γ) T1 →
  is_unstamped_ty (length Γ) T2 →
  Γ u⊢ₜ TLater (TOr T1 T2), i <: TOr (TLater T1) (TLater T2), i.
Proof.
  intros; asideLaters; typconstructor; ettrans;
    [| apply TOr1_stp | | apply TOr2_stp]; tcrush.
Qed.

(** Inverse of [TDistr_TLater_Or_stp]. *)
Lemma TDistr_TLater_Or_stp_inv Γ T1 T2 i :
  is_unstamped_ty (length Γ) T1 →
  is_unstamped_ty (length Γ) T2 →
  Γ u⊢ₜ TOr (TLater T1) (TLater T2), i <: TLater (TOr T1 T2), i.
Proof. intros; tcrush. Qed.

(** TLater swaps with TMu, part 1. *)
Lemma TDistr_TLater_Mu_stp Γ T i :
  is_unstamped_ty (S (length Γ)) T →
  Γ u⊢ₜ TLater (TMu T), i <: TMu (TLater T), i.
Proof. intros; asideLaters; tcrush. Qed.

(** TLater swaps with TMu, part 2. *)
Lemma TDistr_TLater_Mu_stp_inv Γ T i :
  is_unstamped_ty (S (length Γ)) T →
  Γ u⊢ₜ TMu (TLater T), i <: TLater (TMu T), i.
Proof. intros; asideLaters; tcrush. Qed.

(** Show that [singleton_Mu_[12]] and [p_mu_[ie]_typed] are interderivable. *)
Lemma singleton_Mu_1 {Γ p T i} :
  Γ u⊢ₚ p : TMu T, i →
  is_unstamped_ty (S (length Γ)) T →
  Γ u⊢ₜ TSing p, i <: T .Tp[ p /], i.
Proof. intros Hp Hu; apply PSelf_singleton_stp, (p_mu_e_typed Hu Hp). Qed.

Lemma singleton_Mu_2 {Γ p T i} :
  Γ u⊢ₚ p : T .Tp[ p /], i →
  is_unstamped_ty (S (length Γ)) T →
  Γ u⊢ₜ TSing p, i <: TMu T, i.
Proof. intros Hp Hu; apply PSelf_singleton_stp, (p_mu_i_typed Hu Hp). Qed.

(* Avoid automation, to ensure we don't use [p_mu_e_typed] to show them. *)
Lemma p_mu_e_typed' {Γ T p i} :
  Γ u⊢ₚ p : TMu T, i →
  is_unstamped_ty (S (length Γ)) T →
  Γ u⊢ₚ p : T .Tp[ p /], i.
Proof.
  intros Hp Hu. eapply p_subs_typed', (psingleton_refl_typed Hp).
  apply (singleton_Mu_1 Hp Hu).
Qed.

Lemma p_mu_i_typed' {Γ T p i} :
  Γ u⊢ₚ p : T .Tp[ p /], i →
  is_unstamped_ty (S (length Γ)) T →
  Γ u⊢ₚ p : TMu T, i.
Proof.
  intros Hp Hu. eapply p_subs_typed', (psingleton_refl_typed Hp).
  apply (singleton_Mu_2 Hp Hu).
Qed.

(**
Show soundness of subtyping for recursive types in the Dotty compiler — just cases in subtype checking.

The first case is in
https://github.com/lampepfl/dotty/blob/0.20.0-RC1/compiler/src/dotty/tools/dotc/core/TypeComparer.scala#L550-L552
And that matches Mu_stp_mu.

https://github.com/lampepfl/dotty/blob/0.20.0-RC1/compiler/src/dotty/tools/dotc/core/TypeComparer.scala#L554-L557
We formalize that as the derived rule below.

The action of [fixRecs] depends on the type [T1] of [p].
Hence, here we we assume the action of [fixRecs] has already been carried out:
to do that, one must unfold top-level recursive types in the type of [p],
as allowed through [T_Mu_E_p], rules for intersection types and intersection introduction.
On the other hand, this derived rule handles the substitution in [T2] directly.
*)
Lemma singleton_Mu_dotty1 {Γ p i T1' T2} :
  Γ u⊢ₜ T1', i <: T2 .Tp[ p /], i →
  Γ u⊢ₚ p : T1', i →
  is_unstamped_ty (S (length Γ)) T2 →
  Γ u⊢ₜ TSing p, i <: TMu T2, i.
Proof.
  intros Hsub Hp Hu.
  apply singleton_Mu_2, Hu.
  apply (p_subs_typed' Hsub Hp).
Qed.

Definition anfBind t := lett t (tv x0).

Lemma AnfBind_typed Γ t (T U: ty) :
  Γ u⊢ₜ t : T →
  shift T :: Γ u⊢ₜ tv x0 : shift U →
  is_unstamped_ty (length Γ) T →
  Γ u⊢ₜ anfBind t : U.
Proof. intros; eapply Let_typed; eauto. Qed.
