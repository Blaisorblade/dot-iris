From Coq Require FunctionalExtensionality.
From D Require Import iris_prelude proper proofmode_extra.
From D Require Export succ_notation.
From D Require Import saved_interp_n asubst_intf dlang lty.
From D Require Import swap_later_impl.
From D.Dot Require dot_lty unary_lr.

Set Suggest Proof Using.
Set Default Proof Using "Type".
Set Implicit Arguments.
Unset Strict Implicit.

Implicit Types (Σ : gFunctors).

Module Type HoSemTypes
  (Import VS : VlSortsSig)
  (Import LWP : LiftWp VS)
  (Import L : Lty VS LWP).

(** A semantic kind of arity [n] induces an partial order representing
subtyping on types of arity [n], indexed by environments. *)
Notation sr_kind Σ := (env → hoLtyO Σ → hoLtyO Σ → iPropO Σ).
Notation sr_kindO Σ := (env -d> hoLtyO Σ -d> hoLtyO Σ -d> iPropO Σ).

Definition hoLty_equiv {Σ} (T1 T2 : hoLtyO Σ) : iProp Σ :=
  ∀ args v, T1 args v ↔ T2 args v.

Lemma iff_sym `{PROP : bi} (A B : PROP) :
   (A ↔ B) -∗ (B ↔ A).
Proof. by rewrite /bi_iff -bi.and_comm. Qed.

(* XXX Unused *)
Lemma iff_trans `{!BiAffine PROP} (A B C : PROP)
  `{!Persistent A, !Persistent B, !Persistent C} :
   (A ↔ B) -∗ (B ↔ C) -∗ A ↔ C.
Proof.
  iIntros "H1 H2"; iSplit; iIntros "H".
  iApply ("H2" with "(H1 H)").
  iApply ("H1" with "(H2 H)").
Qed.

Lemma hoLty_equiv_refl {Σ} (T : hoLtyO Σ) :
  ⊢ hoLty_equiv T T.
Proof. iIntros "%args %v". by rewrite -equiv_iff. Qed.

Lemma hoLty_equiv_sym {Σ} (T1 T2 : hoLtyO Σ) :
  hoLty_equiv T1 T2 -∗ hoLty_equiv T2 T1.
Proof. iIntros "H %args %v"; iApply (iff_sym with "H"). Qed.

Lemma hoLty_equiv_split `{dlangG Σ} args (T1 T2 : hoLtyO Σ) :
  hoLty_equiv T1 T2 -∗ (T1 args ⊆ T2 args ⊆ T1 args).
Proof. iIntros "Heq"; iSplit; iIntros "%v H"; iApply ("Heq" with "H"). Qed.


(** * Semantic Full Kind. *)
Record sf_kind {Σ} := _SfKind {
  sf_kind_sub :> sr_kind Σ;
  sf_kind_sub_ne_2 ρ : NonExpansive2 (sf_kind_sub ρ);
  sf_kind_sub_internal_proper (T1 T2 U1 U2 : hoLtyO Σ) ρ:
    hoLty_equiv T1 T2 -∗
    hoLty_equiv U1 U2 -∗
    sf_kind_sub ρ T1 U1 -∗ sf_kind_sub ρ T2 U2;
  sf_kind_sub_trans ρ T1 T2 T3 :
    sf_kind_sub ρ T1 T2 -∗
    sf_kind_sub ρ T2 T3 -∗
    sf_kind_sub ρ T1 T3;
  sf_kind_sub_quasi_refl_1 ρ T1 T2 :
    sf_kind_sub ρ T1 T2 -∗
    sf_kind_sub ρ T1 T1;
  sf_kind_sub_quasi_refl_2 ρ T1 T2 :
    sf_kind_sub ρ T1 T2 -∗
    sf_kind_sub ρ T2 T2;
}.
Add Printing Constructor sf_kind.
(* Existing Instance sf_kind_sub_ne. Using :> would create an ambiguous coercion to Funclass. *)
#[global] Arguments sf_kind : clear implicits.
#[global] Arguments sf_kind_sub {_} !_.
#[global] Arguments _SfKind {_} _.
Notation SfKind F := (_SfKind F notc_hole _ _ _ _).

Declare Scope sf_kind_scope.
Bind Scope sf_kind_scope with sf_kind.
Delimit Scope sf_kind_scope with K.
Notation kApp := (sf_kind_sub : sf_kind _ → sr_kindO _).

Section sf_kind_ofe.
  Context {Σ}.
  Notation tpred := (sf_kind Σ).
  (* Forces inserting coercions to -d>. *)

  Instance sf_kind_equiv : Equiv tpred := λ A B, kApp A ≡ B.
  Instance sf_kind_dist : Dist tpred := λ n A B, kApp A ≡{n}≡ B.
  Lemma sf_kind_ofe_mixin : OfeMixin tpred.
  Proof. by apply (iso_ofe_mixin kApp). Qed.
  Canonical Structure sf_kindO := OfeT tpred sf_kind_ofe_mixin.

  Lemma sf_kind_equiv_intro (K1 K2 : sf_kind Σ) : kApp K1 ≡ kApp K2 → K1 ≡ K2.
  Proof. apply. Qed.
End sf_kind_ofe.
#[global] Arguments sf_kindO : clear implicits.


Program Definition kSub {Σ} (f : env → env) (K : sf_kind Σ) : sf_kind Σ :=
  SfKind (λI ρ, K (f ρ)).
Next Obligation.
  move=> Σ f K ρ n T1 T2 HT U1 U2 HU /=; exact: sf_kind_sub_ne_2.
Qed.
Next Obligation. intros; simpl; exact: sf_kind_sub_internal_proper. Qed.
Next Obligation. intros; simpl; exact: sf_kind_sub_trans. Qed.
Next Obligation. intros; simpl; exact: sf_kind_sub_quasi_refl_1. Qed.
Next Obligation. intros; simpl; exact: sf_kind_sub_quasi_refl_2. Qed.

#[global] Program Instance inhabited_sf_kind {Σ}: Inhabited (sf_kind Σ) :=
  populate $ SfKind (λI _ _ _, False).
Next Obligation. done. Qed.
Next Obligation. cbn; eauto. Qed.
Next Obligation. cbn; eauto. Qed.
Next Obligation. cbn; eauto. Qed.
Next Obligation. cbn; eauto. Qed.

#[global] Instance ids_sf_kind {Σ} : Ids (sf_kind Σ) := λ _, inhabitant.

#[global] Instance hsubst_sf_kind {Σ} : HSubst vl (sf_kind Σ) :=
  λ σ K, kSub (λ ρ, (σ >> ρ)) K.


#[global] Instance sf_kind_sub_ne {Σ n} :
  Proper (dist n ==> (=) ==> dist n ==> dist n ==> dist n) (@sf_kind_sub Σ).
Proof.
  intros K1 K2 HK ρ ? <- T1 T2 HT U1 U2 HU.
  etrans; last exact: HK. by apply sf_kind_sub_ne_2.
  (* have ? := sf_kind_sub_ne_2 K1; rewrite HT HU. apply HK. *)
Qed.
#[global] Instance sf_kind_sub_proper {Σ} :
  Proper ((≡) ==> (=) ==> (≡) ==> (≡) ==> (≡)) (@sf_kind_sub Σ).
Proof.
  intros K1 K2 HK ρ ? <- T1 T2 HT U1 U2 HU. etrans; last exact: HK.
  by apply ne_proper_2; [exact: sf_kind_sub_ne_2|..].
  (* have Hne := sf_kind_sub_ne_2 K1. *)
  (* have Hp := !! (ne_proper_2 (K1 ρ)). *)
  (* rewrite HT HU; exact: HK. *)
Qed.
#[global] Instance: Params (@sf_kind_sub) 1 := {}.

Lemma sf_kind_equivI {Σ} (K1 K2 : sf_kindO Σ):
  (∀ ρ T1 T2, K1 ρ T1 T2 ≡ K2 ρ T1 T2) ⊣⊢@{iPropI Σ} (K1 ≡ K2).
Proof. by uPred.unseal. Qed.

Lemma sf_kind_eq {Σ} (K1 K2 : sf_kind Σ) : sf_kind_sub K1 = sf_kind_sub K2 → K1 = K2.
Proof.
  destruct K1, K2; cbn.
  intros ->. f_equal; exact: ProofIrrelevance.proof_irrelevance.
Qed.

(* This is really properness of sf_kind_sub; but it's also proper over the
first argument K. Maybe that's worth a wrapper with swapped arguments. *)
Lemma sf_kind_proper {Σ} (K : sf_kind Σ) ρ :
  Proper ((≡) ==> (≡) ==> (≡)) (K ρ).
Proof. move=> T1 T2 HT U1 U2 HU. exact: sf_kind_sub_proper. Qed.
Lemma sf_kind_proper' {Σ} (K : sf_kind Σ) ρ T1 T2 :
  T1 ≡ T2 → K ρ T1 T1 ≡ K ρ T2 T2.
Proof. intros Heq. exact: sf_kind_proper. Qed.

Lemma sfkind_respects `{dlangG Σ} (K : sf_kind Σ) ρ T1 T2 :
  hoLty_equiv T1 T2 -∗ K ρ T1 T1 -∗ K ρ T2 T2.
Proof. iIntros "#H". iApply (sf_kind_sub_internal_proper with "H H"). Qed.

Section sf_kind_subst.
  Context {Σ}.

  (* XXX move to lty, generalize, name, etc. We can define something like kSub for arbitrary iPred, derive
  kSubstOne and oShift, prove that they correspond to shift and substitution, lift them over reader monads...
  and only finally lift that over sf_kind. *)
  (* XXX Name. *)

  #[global] Instance hsubst_sf_kind_lemmas : HSubstLemmas vl (sf_kind Σ).
  Proof.
    split; intros; apply sf_kind_eq; rewrite /hsubst_sf_kind/kSub/=; [|done|];
      f_ext => ρ; autosubst.
  Qed.
  #[global] Instance rename_sf_kind : Rename (sf_kind Σ) := λ r K, K.|[ren r].
  #[global] Instance sort_sf_kind : Sort (sf_kind Σ) := {}.
  #[global] Instance hsubst_sf_kind_ne ρ :
    NonExpansive (hsubst (outer := sf_kind Σ) ρ).
  Proof. solve_proper_ho. Qed.

  #[global] Instance hsubst_sf_kind_proper ρ :
    Proper ((≡) ==> (≡)) (hsubst (outer := sf_kind Σ) ρ) := ne_proper _.

  Definition kSubstOne {Σ} v (K : sf_kind Σ) : sf_kind Σ :=
    kSub (λ ρ, v.[ρ] .: ρ) K.
  Lemma kSubstOne_eq (K : sf_kind Σ) v ρ : sf_kind_sub K.|[v/] ρ = kSubstOne v K ρ.
  Proof. by rewrite /= subst_swap_base. Qed.

  Definition kShift {Σ} (K : sf_kind Σ) : sf_kind Σ :=
    kSub (λ ρ, stail ρ) K.

  (** Analogue of [hoEnvD_subst_compose_ind]; the lemma setup here is however slightly
      simplified. *)
  Lemma sf_kind_subst_compose (K : sf_kind Σ) ρ1 ρ2 T1 T2 :
    K.|[ρ1] ρ2 T1 T2 ⊣⊢ K (ρ1 >> ρ2) T1 T2.
  Proof. done. Qed.

  Lemma kShift_eq (K : sf_kind Σ) :
    kShift K ≡ shift K.
  Proof. intros ρ T1 T2. rewrite sf_kind_subst_compose. autosubst. Qed.

  Lemma kShift_cancel (K : sf_kind Σ) v :
    (kShift K).|[v/] ≡ K.
  Proof. by rewrite kShift_eq shift_sub. Qed.

  Lemma kShift_cancel' (K : sf_kind Σ) :
    K.|[up (ren (+1))].|[ids 0/] ≡ K.
  Proof. move=> ρ /=; f_equiv; autosubst. Qed.

  Definition oLam (τ : oltyO Σ) : oltyO Σ :=
    Olty (λI args ρ, τ (atail args) (ahead args .: ρ)).
    (* auncurry (λ v, Olty (λ args ρ, τ args (v .: ρ))). *)

  Definition _oTAppV w (T : oltyO Σ) : oltyO Σ :=
    Olty (λI args ρ, T (acons w.[ρ] args) ρ).

End sf_kind_subst.

Notation oTAppV T w := (_oTAppV w T).
#[global] Instance: Params (@_oTAppV) 3 := {}.

Section utils.
  Context `{dlangG Σ}.

  #[global] Instance _oTAppV_ne v: NonExpansive (_oTAppV (Σ := Σ) v).
  Proof. solve_proper_ho. Qed.
  #[global] Instance _oTAppV_proper v:
    Proper ((≡) ==> (≡)) (_oTAppV (Σ := Σ) v) := ne_proper _.

  #[global] Instance oLam_ne : NonExpansive (oLam (Σ := Σ)).
  Proof. solve_proper_ho. Qed.

  #[global] Instance oLam_proper :
    Proper ((≡) ==> (≡)) (oLam (Σ := Σ)) := ne_proper _.

  Lemma oTAppV_subst (T : olty Σ) v ρ :
    (oTAppV T v).|[ρ] ≡ oTAppV T.|[ρ] v.[ρ].
  Proof.
    move=> ???/=.
    by rewrite /hsubst /hsubst_hoEnvD subst_comp.
  Qed.

  Lemma envApply_oTAppV_eq (T : olty Σ) v ρ :
    envApply (oTAppV T v) ρ ≡ acurry (envApply T ρ) v.[ρ].
  Proof. done. Qed.

  Definition sr_kintv (L U : oltyO Σ) : sr_kind Σ := λI ρ φ1 φ2,
    oClose L ρ ⊆ oClose φ1 ⊆ oClose φ2 ⊆ oClose U ρ.

  Lemma sr_kintv_refl L U ρ φ :
    sr_kintv L U ρ φ φ ⊣⊢ oClose L ρ ⊆ oClose φ ⊆ oClose U ρ.
  Proof.
    by rewrite /sr_kintv (bi_emp_valid_True subtype_refl) (left_id True)%I.
  Qed.

  Lemma sr_kintv_respects_hoLty_equiv_1 {T1 T2} (L U : olty Σ) U1 ρ :
    hoLty_equiv T1 T2 -∗ sr_kintv L U ρ T1 U1 -∗ sr_kintv L U ρ T2 U1.
  Proof.
    rewrite !(hoLty_equiv_split anil).
    iIntros "#(HT1 & HT2) #(HL&HM&$) /="; iSplit.
    by iApply (subtype_trans with "HL HT1").
    by iApply (subtype_trans with "HT2 HM").
  Qed.

  Lemma sr_kintv_respects_hoLty_equiv_2 {U1 U2} (L U : olty Σ) T1 ρ :
    hoLty_equiv U1 U2 -∗ sr_kintv L U ρ T1 U1 -∗ sr_kintv L U ρ T1 U2.
  Proof.
    rewrite !(hoLty_equiv_split anil).
    iIntros "#(HU1 & HU2) #($&HM&HU) /="; iSplit.
    by iApply (subtype_trans with "HM HU1").
    by iApply (subtype_trans with "HU2 HU").
  Qed.
End utils.

Program Definition sf_kintv `{dlangG Σ} (L U : oltyO Σ) : sf_kind Σ :=
  SfKind (sr_kintv L U).
Next Obligation. cbn; solve_proper_ho. Qed.
Next Obligation.
  iIntros "* HT HU H"; iApply (sr_kintv_respects_hoLty_equiv_2 with "HU").
  iApply (sr_kintv_respects_hoLty_equiv_1 with "HT H").
Qed.
Next Obligation.
  iIntros "* #($&HLT1&_) #(_ & HT2T3 & $)".
  iApply (subtype_trans with "HLT1 HT2T3").
Qed.
Next Obligation.
  intros; rewrite sr_kintv_refl; iIntros "/= #($ & B & C)".
  iApply (subtype_trans with "B C").
Qed.
Next Obligation.
  intros; rewrite sr_kintv_refl; iIntros "/= #(A & B & $)".
  iApply (subtype_trans with "A B").
Qed.

Notation sf_star := (sf_kintv oBot oTop).

Lemma acurry_respects_hoLty_equiv {Σ} {T1 T2 : hoLty Σ} arg :
  hoLty_equiv T1 T2 -∗ hoLty_equiv (acurry T1 arg) (acurry T2 arg).
Proof. by iIntros "H %%". Qed.

Program Definition sf_kpi `{dlangG Σ} (S : oltyO Σ) (K : sf_kind Σ) :
  sf_kind Σ := SfKind
    (λI ρ φ1 φ2,
      ∀ arg, S anil ρ arg →
      K (arg .: ρ) (acurry φ1 arg) (acurry φ2 arg)).
Next Obligation.
  move=> Σ ? ? S K ρ n T1 T2 HT U1 U2 HU /=.
  f_equiv => ?; f_equiv.
  by apply sf_kind_sub_ne_2; apply acurry_ne.
Qed.
Next Obligation.
  intros; iIntros "#Heq1 #Heq2 /= #HT %arg HS".
  rewrite (acurry_respects_hoLty_equiv (T1 := T1) arg).
  rewrite (acurry_respects_hoLty_equiv (T1 := U1) arg).
  iApply (sf_kind_sub_internal_proper with "Heq1 Heq2 (HT HS)").
Qed.
Next Obligation.
  intros; iIntros "#H1 #H2 %arg #Harg".
  iApply (sf_kind_sub_trans with "(H1 Harg) (H2 Harg)").
Qed.
Next Obligation.
  intros; iIntros "/= #H * #Harg"; iApply (sf_kind_sub_quasi_refl_1 with "(H Harg)").
Qed.
Next Obligation.
  intros; iIntros "/= #H * #Harg"; iApply (sf_kind_sub_quasi_refl_2 with "(H Harg)").
Qed.

Section kinds_types.
  Context `{dlangG Σ}.

  #[global] Instance: NonExpansive2 (sf_kintv (Σ := Σ)).
  Proof. rewrite /sf_kintv /sr_kintv. solve_proper_ho. Qed.
  #[global] Instance sf_kintv_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (sf_kintv (Σ := Σ)) := ne_proper_2 _.

  #[global] Instance sf_kpi_ne : NonExpansive2 (sf_kpi (Σ := Σ)).
  Proof. solve_proper_ho. Qed.
  #[global] Instance sf_kpi_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (sf_kpi (Σ := Σ)) := ne_proper_2 _.

  Lemma kShift_sf_kpi_eq S (K : sf_kind Σ) :
    kShift (sf_kpi S K) ≡ sf_kpi (oShift S) K.|[up (ren (+1))].
  Proof.
    move=> ???/=; properness; first done; f_equiv.
    rewrite /stail; autosubst.
  Qed.

  (** Subtle: this requires [ahead] to be total! *)
  Lemma sTEq_oLaterN_oLam (τ : oltyO Σ) m :
    oLaterN m (oLam τ) ≡ oLam (oLaterN m τ).
  Proof. done. Qed.

  Lemma sTEq_oLaterN_oTAppV (τ : oltyO Σ) m v:
    oLaterN m (oTAppV τ v) ≡ oTAppV (oLaterN m τ) v.
  Proof. done. Qed.
End kinds_types.

Module SKindSyn.

(* XXX rename *)
(** An inductive representation of gHkDOT semantic kinds. *)
Inductive s_kind {Σ} : nat → Type :=
  | s_kintv : oltyO Σ → oltyO Σ → s_kind 0
  | s_kpi n : oltyO Σ → s_kind n → s_kind n.+1.
#[global] Arguments s_kind: clear implicits.

Inductive s_kind_rel {Σ} {R : relation (oltyO Σ)} : ∀ {n : nat}, relation (s_kind Σ n) :=
  | s_kintv_rel L1 L2 U1 U2 :
    R L1 L2 → R U1 U2 →
    s_kind_rel (s_kintv L1 U1) (s_kintv L2 U2)
  | s_kpi_rel {n} S1 S2 (K1 K2 : s_kind Σ n) :
    R S1 S2 →
    s_kind_rel K1 K2 →
    s_kind_rel (s_kpi S1 K1) (s_kpi S2 K2).
#[global] Arguments s_kind_rel {_} R _ _ _.

Section s_kind_rel_prop.
  Context `{R : relation (oltyO Σ)}.
  #[global] Instance s_kind_rel_refl n `(!Reflexive R) : Reflexive (s_kind_rel R n).
  Proof. elim; constructor; eauto. Qed.

  #[global] Instance s_kind_rel_sym `(!Symmetric R) n : Symmetric (s_kind_rel R n).
  Proof. induction 1; constructor; eauto. Qed.
  #[global] Instance s_kind_rel_trans n `(!Transitive R) : Transitive (s_kind_rel R n).
  Proof. induction 1; inversion 1; simplify_eq; constructor; eauto. Qed.
  #[global] Instance s_kind_rel_equiv n `(!Equivalence R) : Equivalence (s_kind_rel R n).
  Proof. split; apply _. Qed.

  #[global] Instance s_kintv_inj : Inj2 R R (s_kind_rel R 0) s_kintv.
  Proof. inversion 1; simplify_eq; auto. Qed.
  #[global] Instance s_kpi_inj n: Inj2 R (s_kind_rel R n) (s_kind_rel R n.+1) (s_kpi (n := n)).
  Proof. inversion 1; simplify_eq; auto. Qed.
End s_kind_rel_prop.

Section s_kind_ofe.
  Context {Σ}.
  Instance s_kind_equiv {n} : Equiv (s_kind Σ n) := s_kind_rel (≡) n.
  Instance s_kind_dist {n} : Dist (s_kind Σ n) := λ m, s_kind_rel (dist m) n.
  Lemma s_kind_ofe_mixin {n}: OfeMixin (s_kind Σ n).
  Proof.
    split.
    - move => x y; split => Hx.
      + move=> m. induction Hx; constructor;
        unfold s_kind_dist in *; eauto.
      + by induction (Hx 0); constructor; (apply equiv_dist || apply IHd) => m;
          have := (Hx m); intros [??]%(inj2 _).
    - apply _.
    - move => m x y; elim; constructor; eauto; by apply dist_S.
  Qed.
End s_kind_ofe.

Canonical Structure s_kindO Σ n := OfeT (s_kind Σ n) s_kind_ofe_mixin.

Section s_kind_rel_proper.
  Context `{R : relation (oltyO Σ)}.

  #[global] Instance s_kintv_proper_s_kind_rel : Proper (R ==> R ==> s_kind_rel R 0) s_kintv.
  Proof. constructor; auto. Qed.
  #[global] Instance s_kpi_proper_s_kind_rel n : Proper (R ==> s_kind_rel R n ==> s_kind_rel R n.+1) (s_kpi (n := n)).
  Proof. constructor; auto. Qed.
End s_kind_rel_proper.

Section s_kind_rel_proper.
  Context {Σ}.

  #[global] Instance s_kintv_ne : NonExpansive2 (s_kintv (Σ := Σ)).
  Proof. apply _. Qed.
  #[global] Instance s_kpi_ne n : NonExpansive2 (s_kpi (Σ := Σ) (n := n)).
  Proof. apply _. Qed.

  #[global] Instance s_kintv_proper : Proper ((≡) ==> (≡) ==> (≡)) (s_kintv (Σ := Σ)).
  Proof. apply _. Qed.
  #[global] Instance s_kpi_proper n : Proper ((≡) ==> (≡) ==> (≡)) (s_kpi (Σ := Σ) (n := n)).
  Proof. apply _. Qed.
End s_kind_rel_proper.

Instance s_kind_ids {Σ} : ∀ n, Ids (s_kind Σ n) := fix s_kind_ids n := λ _,
  match n with
  | 0 => s_kintv oTop oBot
  | n.+1 => s_kpi inhabitant (s_kind_ids _ 0)
  end.
Fixpoint s_kind_hsubst {Σ n} (ρ : env) (K : s_kindO Σ n) : s_kindO Σ n :=
  match K with
  | s_kintv S1 S2 => s_kintv S1.|[ρ] S2.|[ρ]
  | @s_kpi _ n S K =>
    let _ : HSubst vl (s_kind Σ n) := s_kind_hsubst in
    s_kpi S.|[ρ] K.|[up ρ]
  end.
Instance hsubst_s_kind {Σ n} : HSubst vl (s_kind Σ n) := s_kind_hsubst.
Instance: Params (@hsubst_s_kind) 2 := {}.

#[global] Instance s_kind_hsubst_lemmas {Σ n} : HSubstLemmas vl (s_kind Σ n).
Proof.
  split => //.
  - elim=> [S1 S2|{}n S K IHK] /=; by rewrite /= ?up_id ?IHK !hsubst_id.
  - elim: n => [//|n + θ x] /=. by move ->.
  - move=> + + K; elim: K => [S1 S2|{}n S K IHK] θ η /=;
      by rewrite !hsubst_comp ?IHK ?up_comp.
Qed.

Fixpoint s_kind_to_sf_kind `{dlangG Σ} {n} (K : s_kind Σ n) : sf_kind Σ :=
  match K with
  | s_kintv L U => sf_kintv L U
  | s_kpi S K => sf_kpi S (s_kind_to_sf_kind K)
  end.
#[global] Instance: Params (@s_kind_to_sf_kind) 4 := {}.

Notation s_to_sf := s_kind_to_sf_kind.
(* Coercion s_kind_to_sf_kind : s_kind >-> sf_kind. *)

Section s_kind_to_sf_kind.
  Context `{dlangG Σ}.

  #[global] Instance s_kind_to_sf_kind_ne {n} :
    NonExpansive (s_kind_to_sf_kind (n := n)).
  Proof. by induction 1; cbn; f_equiv. Qed.
  #[global] Instance s_kind_to_sf_kind_proper {n} :
    Proper ((≡) ==> (≡)) (s_kind_to_sf_kind (n := n)) := ne_proper _.

  Lemma s_kind_equiv_intro {n} (K1 K2 : s_kind Σ n) : K1 ≡ K2 → s_to_sf K1 ≡@{sf_kind _} s_to_sf K2.
  Proof. apply s_kind_to_sf_kind_proper. Qed.

  Lemma s_kind_to_sf_kind_subst {n} (K : s_kind Σ n) ρ :
    (s_kind_to_sf_kind K).|[ρ] ≡ s_kind_to_sf_kind (K.|[ρ]).
  Proof.
    elim: K ρ => [S1 S2 //|{}n S K IHK] ρ ξ T1 T2. cbn.
    properness; first done.
    by rewrite -IHK /hsubst_sf_kind /= -scons_up_swap.
  Qed.
End s_kind_to_sf_kind.

Fixpoint ho_intv {Σ n} (K : s_kindO Σ n) : oltyO Σ → oltyO Σ → s_kindO Σ n :=
  match K with
  | s_kintv _ _ =>
    λ T1 T2, s_kintv T1 T2
  | s_kpi S K =>
    λ T1 T2, s_kpi S (ho_intv K
      (oTAppV (oShift T1) (ids 0)) (oTAppV (oShift T2) (ids 0)))
  end.
Notation ho_sing K T := (ho_intv K T T).
#[global] Instance: Params (@ho_intv) 2 := {}.

Section ho_intv.
  Context {Σ}.
  (* Context `{dlangG Σ}. *)

  #[global] Instance ho_intv_ne {n m}:
    Proper (dist m ==> dist m ==> dist m ==> dist m) (ho_intv (n := n) (Σ := Σ)).
  Proof.
    move=> K1 K2 HK; induction HK => /= [??? ???| L1 L2 HL U1 U2 HU];
      f_equiv => //.
    apply IHHK; by repeat f_equiv.
  Qed.

  #[global] Instance ho_intv_proper {n}:
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (ho_intv (n := n) (Σ := Σ)).
  Proof.
    move=> K1 K2 /equiv_dist HK L1 L2 /equiv_dist HL U1 U2 /equiv_dist HU.
    apply /equiv_dist => m.
    exact: ho_intv_ne.
  Qed.

  Lemma ho_intv_subst {n} (K : s_kindO Σ n) T1 T2 ρ :
    (ho_intv K T1 T2).|[ρ] ≡
    ho_intv K.|[ρ] T1.|[ρ] T2.|[ρ].
  Proof.
    elim: K ρ T1 T2 => [S1 S2//|{}n S K IHK] ρ T1 T2 /=.
    f_equiv; rewrite IHK.
    (* Much faster by hand. *)
    apply ho_intv_proper; first done;
      (etrans; first apply oTAppV_subst);
      rewrite id_subst;
      apply _oTAppV_proper, oShift_subst.
    (* Time by f_equiv; rewrite !oTAppV_subst !oShift_subst id_subst. *)
    (* Time by rewrite !oTAppV_subst !oShift_subst id_subst. *)
  Qed.
End ho_intv.

End SKindSyn.

End HoSemTypes.

Module HkDotSemTypes.
Import dot_lty unary_lr.
Include HoSemTypes VlSorts dlang_inst dot_lty.

Implicit Types
         (v w : vl) (e : tm) (d : dm) (ds : dms) (p : path)
         (ρ : var → vl) (l : label).

Definition sem_kind_path_repl {Σ} p q (K1 K2 : sf_kind Σ) : Prop :=
  ∀ ρ T1 T2, alias_paths p.|[ρ] q.|[ρ] → K1 ρ T1 T2 ≡ K2 ρ T1 T2.
Notation "K1 ~sKd[ p := q  ]* K2" :=
  (sem_kind_path_repl p q K1 K2) (at level 70).

Definition oDTMemK `{!dlangG Σ} (K : sf_kind Σ) : dltyO Σ :=
  oDTMemRaw (λI ρ ψ, K ρ (packHoLtyO ψ) (packHoLtyO ψ)).

Definition oDTMemSpec `{!dlangG Σ} (L U : oltyO Σ) : dltyO Σ :=
  oDTMemK (sf_kintv L U).

Lemma oDTMemSpec_oDTMem_eq `{!dlangG Σ} L U : oDTMemSpec L U ≡ oDTMem L U.
Proof.
  move=> ρ d /=; f_equiv=> ψ; f_equiv. apply sr_kintv_refl.
Qed.

Definition cTMemK `{!dlangG Σ} l (K : sf_kind Σ) : clty Σ := dty2clty l (oDTMemK K).
Notation oTMemK l K := (clty_olty (cTMemK l K)).

Definition oDTMemAnyKind `{!dlangG Σ} : dltyO Σ := Dlty (λI ρ d,
  ∃ (ψ : hoD Σ), d ↗n ψ).
Definition cTMemAnyKind `{!dlangG Σ} l : clty Σ := dty2clty l oDTMemAnyKind.
Notation oTMemAnyKind l := (clty_olty (cTMemAnyKind l)).

Program Definition kpSubstOne `{!dlangG Σ} p (K : sf_kind Σ) : sf_kind Σ :=
  SfKind
    (λI ρ T1 T2, path_wp p.|[ρ] (λ v, K (v .: ρ) T1 T2)).
Next Obligation.
  move=> Σ ? p K v m T1 T2 HT U1 U2 HU /=. f_equiv=>?. exact: sf_kind_sub_ne_2.
Qed.
Next Obligation.
  iIntros "* #Heq1 #Heq2 H". iApply (path_wp_wand with "H");
    iIntros "* HK"; iApply (sf_kind_sub_internal_proper with "Heq1 Heq2 HK").
Qed.
Next Obligation.
  iIntros "* HK1 HK2". iDestruct (path_wp_and' with "HK1 HK2") as "HK".
  iApply (path_wp_wand with "HK"); iIntros "* [HK1 HK2]".
  iApply (sf_kind_sub_trans with "HK1 HK2").
Qed.
Next Obligation.
  iIntros "* H"; iApply (path_wp_wand with "H"); iIntros "*".
  iApply sf_kind_sub_quasi_refl_1.
Qed.
Next Obligation.
  iIntros "* H"; iApply (path_wp_wand with "H"); iIntros "*".
  iApply sf_kind_sub_quasi_refl_2.
Qed.
Notation "K .sKp[ p /]" := (kpSubstOne p K) (at level 65).

Definition oTApp `{!dlangG Σ} (T : oltyO Σ) (p : path) : oltyO Σ :=
  Olty (λ args ρ v, path_wp p.|[ρ] (λ w, T (acons w args) ρ v)).

Section proper_eq.
  Context `{!dlangG Σ}.

  #[global] Instance oDTMemK_ne : NonExpansive (oDTMemK (Σ := Σ)).
  Proof. solve_proper_ho. Qed.
  #[global] Instance oDTMemK_proper :
    Proper ((≡) ==> (≡)) (oDTMemK (Σ := Σ)) := ne_proper _.
  #[global] Instance cTMemK_ne l : NonExpansive (cTMemK (Σ := Σ) l).
  Proof. solve_proper_ho. Qed.
  #[global] Instance cTMemK_proper l :
    Proper ((≡) ==> (≡)) (cTMemK (Σ := Σ) l) := ne_proper _.

  Lemma cTMemK_eq l (K : sf_kind Σ) d ρ :
    cTMemK l K ρ [(l, d)] ⊣⊢ oDTMemK K ρ d.
  Proof. apply dty2clty_singleton. Qed.

  Lemma oTMemK_eq l K args ρ v :
    oTMemK l K args ρ v ⊣⊢
    ∃ ψ d, ⌜v @ l ↘ d⌝ ∧ d ↗n ψ ∧ K ρ (packHoLtyO ψ) (packHoLtyO ψ).
  Proof. apply bi_exist_nested_swap. Qed.

  Lemma cTMemAnyKind_eq l d ρ :
    cTMemAnyKind l ρ [(l, d)] ⊣⊢ oDTMemAnyKind ρ d.
  Proof. apply dty2clty_singleton. Qed.

  Lemma cTMemK_subst l (K : sf_kind Σ) ρ :
    (oTMemK l K).|[ρ] = oTMemK l K.|[ρ].
  Proof. done. Qed.

  Lemma kpSubstOne_eq (K : sf_kind Σ) v :
    K.|[v/] ≡ K .sKp[ pv v /].
  Proof. move=> ???. by rewrite /= path_wp_pv_eq subst_swap_base. Qed.

  Lemma oTApp_pv (T : oltyO Σ) w :
    oTApp T (pv w) ≡ oTAppV T w.
  Proof. intros ???. by rewrite /= path_wp_pv_eq. Qed.

  Lemma sTEq_oLaterN_oTApp_pv (τ : oltyO Σ) m v:
    oLaterN m (oTApp τ (pv v)) ≡ oTApp (oLaterN m τ) (pv v).
  Proof. by rewrite !oTApp_pv. Qed.

  Lemma sTSub_oTApp_oLaterN (τ : oltyO Σ) m p args ρ v:
    oTApp (oLaterN m τ) p args ρ v ⊢ oLaterN m (oTApp τ p) args ρ v.
  Proof. by rewrite /= path_wp_laterN_swap. Qed.

  Lemma sTEq_Beta (T : oltyO Σ) p :
    oTApp (oLam T) p ≡ T .sTp[ p /].
  Proof. done. Qed.

  Lemma sTEq_BetaV (T : oltyO Σ) v :
    oTAppV (oLam T) v ≡ T.|[v/].
  Proof. move => args ρ w /=. by rewrite subst_swap_base. Qed.

End proper_eq.
End HkDotSemTypes.
