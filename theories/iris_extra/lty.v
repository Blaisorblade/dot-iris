(** * Formalize infrastructure for semantic types; not shown in the paper.

In Iris one represents semantic types as persistent Iris predicates on
values.
Since D* syntactic types can contain variables ranging on values, semantic
types take a value substitution as argument.

Using Autosubst, we can define substitution on semantic types by
precomposition: [ τ.|[s] = λ ρ, τ (ρ >> s) ].

All this infrastructure works for arbitrary languages implementing
[ValuesSig].
*)
From Coq Require FunctionalExtensionality.
From iris.algebra Require Import list.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import language.
From D.pure_program_logic Require Import lifting adequacy.
From D Require Import prelude iris_prelude asubst_intf dlang proper.

Implicit Types (Σ : gFunctors).

Set Suggest Proof Using.
Set Default Proof Using "Type".

Global Instance bottom_fun {A} `{Bottom B}: Bottom (A → B) := (λ _, ⊥).
Global Instance top_fun {A} `{Top B}: Top (A → B) := (λ _, ⊤).
Global Instance bottom_ofe_fun {A} {B : ofeT} `{Bottom B}: Bottom (A -d> B) := (λ _, ⊥).
Global Instance top_ofe_fun {A} {B : ofeT} `{Top B}: Top (A -d> B) := (λ _, ⊤).

(** ** "Iris Persistent Predicates" [iPPred].

We use such predicates also for definition bodies and definition lists.
Adapted from
https://gitlab.mpi-sws.org/iris/examples/blob/d4f4153920ea82617c7222aeeb00b6710d51ee03/theories/logrel_heaplang/ltyping.v#L5. *)

Record iPPred vl Σ := IPPred {
  iPPred_car :> vl → iProp Σ;
}.
Add Printing Constructor iPPred.
Global Arguments IPPred {_ _} _%I.
Global Arguments iPPred_car {_ _} !_ _ /.
Declare Scope iPPred_scope.
Bind Scope iPPred_scope with iPPred.
Delimit Scope iPPred_scope with T.

(** ** OFE on [iPPred]. *)
Section iPPred_ofe.
  Context {vl : Type} {Σ}.
  Notation vpred := (iPPred vl Σ).
  Implicit Types (ψ : vl -d> iPropO Σ) (τ : vpred).

  (* Forces inserting coercions to -d>. *)
  Notation lApp := (iPPred_car : iPPred _ _ → _ -d> _).

  Instance iPPred_equiv : Equiv vpred := λ A B, lApp A ≡ B.
  Instance iPPred_dist : Dist vpred := λ n A B, lApp A ≡{n}≡ B.
  Lemma iPPred_ofe_mixin : OfeMixin vpred.
  Proof. by apply (iso_ofe_mixin lApp). Qed.
  Canonical Structure iPPredO := OfeT vpred iPPred_ofe_mixin.

  Lemma iPPred_equivI {τ1 τ2 : iPPred vl Σ} :
    iPPred_car τ1 ≡@{vl -d> _} iPPred_car τ2 ⊣⊢@{iPropI Σ} τ1 ≡ τ2.
  Proof. by uPred.unseal. Qed.

  (** ** Show iPPred forms a COFE.
  Only needed to define Lty using Iris fixpoints (e.g. for normal recursive
  types), so _currently_ unused. *)

  Global Instance iPPred_cofe : Cofe iPPredO.
  Proof.
    apply (iso_cofe (A := vl -d> iPropO Σ) IPPred lApp) => //.
  Qed.

  Global Instance bottom_iprop : Bottom (iProp Σ) := False%I.
  Global Instance top_iprop : Top (iProp Σ) := True%I.

  Global Instance bottom_ippred {s}: Bottom (iPPred s Σ) := IPPred (λ _, ⊥).
  Global Instance top_ippred {s}: Top (iPPred s Σ) := IPPred (λ _, ⊤).

  Global Program Instance iPPred_inhabited : Inhabited vpred := populate ⊥.

  Global Instance iPPred_car_ne n : Proper (dist n ==> (=) ==> dist n) (@iPPred_car vl Σ).
  Proof. by intros A A' HA w ? <-. Qed.
  Global Instance iPPred_car_proper : Proper ((≡) ==> (=) ==> (≡)) (@iPPred_car vl Σ).
  Proof. by intros A A' HA w ? <-. Qed.

  Lemma lty_eq τ1 τ2: iPPred_car τ1 = iPPred_car τ2 → τ1 = τ2.
  Proof.
    move: τ1 τ2 => [φ1 ] [φ2 ] /=. by rewrite /iPPred_car => ->.
  Qed.
End iPPred_ofe.

Global Arguments iPPredO : clear implicits.

Module Type Lty (Import VS: VlSortsSig) (Import LVS : LiftWp VS).

(**
** "Logical TYpes": persistent Iris predicates over values. *)
Notation lty := (iPPred vl).
Notation ltyO := (iPPredO vl).
Notation Lty := (IPPred (vl := vl)).
Notation lty_car := (iPPred_car (vl := vl)) (only parsing).
(* Forces inserting coercions to -d>. *)
Notation lApp := (iPPred_car : lty _ → _ -d> _).

Notation iRel P Σ := (P Σ → P Σ → iProp Σ).
Definition subtype_lty `{dlangG Σ} : iRel ltyO Σ := λI φ1 φ2,
  ∀ v, φ1 v → φ2 v.
Infix "⊆" := subtype_lty : bi_scope.
Notation "X ⊆@{ Σ } Y" := (subtype_lty (Σ := Σ) X Y) (at level 70, only parsing) : bi_scope.
Notation "X ⊆ Y ⊆ Z" := (X ⊆ Y ∧ Y ⊆ Z)%I : bi_scope.
Notation "X ⊆ Y ⊆ Z ⊆ W" := (X ⊆ Y ∧ Y ⊆ Z ∧ Z ⊆ W)%I (at level 70, Y, Z at next level) : bi_scope.

Section subtype_lty.
  Context `{dlangG Σ}.

  Global Instance subtype_lty_ne : NonExpansive2 (subtype_lty (Σ := Σ)).
  Proof. solve_proper_ho. Qed.
  Global Instance subtype_lty_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (subtype_lty (Σ := Σ)) := ne_proper_2 _.

  Lemma subtype_refl {T}: ⊢ T ⊆@{Σ} T.
  Proof. by iIntros "%v $". Qed.

  Lemma subtype_trans {T1} T2 {T3} :
    T1 ⊆ T2 -∗ T2 ⊆ T3 -∗ T1 ⊆@{Σ} T3.
  Proof. iIntros "H1 H2 %v HT1". iApply ("H2" with "(H1 HT1)"). Qed.
End subtype_lty.


(** * "Open Logical TYpes": persistent Iris predicates over environments and values. *)
Definition olty Σ n := vec vl n → env → lty Σ.
Notation oltyO Σ n := (vec vl n -d> env -d> ltyO Σ).

Notation olty_car τ := (λ args ρ v, lty_car (τ args ρ) v).
Definition oApp {Σ n} : olty Σ n → hoEnvD Σ n := λ φ, olty_car φ.


Definition hoLty Σ n := vec vl n → lty Σ.
Definition hoLtyO Σ n := vec vl n -d> ltyO Σ.
Notation hoLty_car τ := (λ args v, lty_car (τ args) v).
Notation HoLty φ := (λ args, Lty (λI v, φ args v)).


Definition envApply {Σ n} : oltyO Σ n → env → hoLtyO Σ n :=
  λ T, flip T.
Instance: Params (@envApply) 2 := {}.
Instance envApply_proper n :
  Proper ((≡) ==> (=) ==> (≡)) (envApply (Σ := Σ) (n := n)).
Proof. solve_proper_ho. Qed.

Definition packHoLtyO {Σ n} (φ : hoD Σ n) : hoLtyO Σ n :=
  HoLty (λI args v, ▷ φ args v).
Instance: Params (@packHoLtyO) 2 := {}.
Instance packHoLtyO_contractive {Σ n} :
  Contractive (packHoLtyO (Σ := Σ) (n := n)).
Proof. solve_contractive_ho. Qed.
Instance packHoLtyO_proper {Σ n} :
  Proper ((≡) ==> (≡)) (packHoLtyO (Σ := Σ) (n := n)) := contractive_proper _.

(** ** Substitution over [olty]. *)
Section olty_subst.
  Context `{dlangG Σ} {i : nat}.
  Implicit Types (φ : hoEnvD Σ i) (τ : olty Σ i).

  Lemma olty_eq τ1 τ2:
    (∀ args ρ, olty_car τ1 args ρ = olty_car τ2 args ρ) →
    τ1 = τ2.
  Proof. intros * Heq; f_ext => args; f_ext => ρ. apply lty_eq, Heq. Qed.

  Lemma olty_eq' τ1 τ2: olty_car τ1 = olty_car τ2 → τ1 = τ2.
  Proof.
    intros Heq; apply olty_eq => args ρ.
    apply (f_equal_dep _ _ ρ
              (f_equal_dep _ _ args Heq)).
  Qed.

  Lemma lift_olty_eq {τ1 τ2 : oltyO Σ i} {args ρ v} :
    τ1 ≡ τ2 → τ1 args ρ v ≡ τ2 args ρ v.
  Proof. apply. Qed.

  Lemma olty_equivI {n} (T1 T2 : oltyO Σ n):
    (∀ args ρ v, T1 args ρ v ≡ T2 args ρ v) ⊣⊢@{iPropI Σ} (T1 ≡ T2).
  Proof.
    repeat setoid_rewrite discrete_fun_equivI.
    f_equiv=>args; f_equiv=>ρ.
    by rewrite -iPPred_equivI discrete_fun_equivI.
  Qed.

  Global Instance ids_hoEnvD : Ids (hoEnvD Σ i) := λ _, inhabitant.
  Global Instance rename_hoEnvD : Rename (hoEnvD Σ i) :=
    λ r φ args ρ, φ args (r >>> ρ).
  Global Instance hsubst_hoEnvD : HSubst vl (hoEnvD Σ i) :=
    λ sb φ args ρ, φ args (sb >> ρ).

  Ltac renLemmas_hoEnvD :=
    hnf; rewrite /hsubst /hsubst_hoEnvD => /= *;
    do 2 (apply FunctionalExtensionality.functional_extensionality_dep => ?); autosubst.

  Global Instance HSubstLemmas_hoEnvD : HSubstLemmas vl (hoEnvD Σ i).
  Proof. split => //; renLemmas_hoEnvD. Qed.

  Global Instance: Sort (hoEnvD Σ i) := {}.

  Lemma hoEnvD_subst_compose_ind φ args ρ1 ρ2 v: φ.|[ρ1] args ρ2 v ⊣⊢ φ args (ρ1 >> ρ2) v.
  Proof. done. Qed.

  Lemma hoEnvD_subst_compose φ args ρ1 ρ2 ρ3 :
    ρ1 >> ρ2 = ρ3 → φ.|[ρ1] args ρ2 ≡ φ args ρ3.
  Proof. by move=> <-. Qed.

  Lemma hoEnvD_weaken_one φ args ρ:
    shift φ args ρ ≡ φ args (stail ρ).
  Proof. apply hoEnvD_subst_compose. autosubst. Qed.

  Lemma hoEnvD_subst_one φ v args ρ:
    φ.|[v/] args ρ ≡ φ args (v.[ρ] .: ρ).
  Proof. apply hoEnvD_subst_compose. autosubst. Qed.

  (* XXX these alternative statements infer (@ids vl ρ] [*)
  (* Lemma hoEnvD_subst_ids φ ρ {args} : φ args ρ ≡ φ.|[ρ] args ids. *)
  (* Program Lemma hoEnvD_subst_ids φ ρ {args} : φ args ρ ≡ φ.|[ρ] args ids. *)
  Lemma hoEnvD_subst_ids φ ρ {args} : φ args ρ ≡ φ.|[ρ] args (@ids vl ids_vl).
  Proof. symmetry. apply hoEnvD_subst_compose. autosubst. Qed.

  Lemma hoEnvD_finsubst_commute_cl φ σ ρ v (HclT : nclosed φ (length σ)) args :
    φ.|[∞ σ] args ρ v ≡ φ args (∞ σ.|[ρ]) v.
  Proof.
    rewrite hoEnvD_subst_compose_ind !(hoEnvD_subst_ids φ) -hsubst_comp.
    (* *The* step requiring [HclT]. *)
    by rewrite (subst_compose HclT).
  Qed.

  Definition Olty (olty_car : vec vl i → (var → vl) → vl → iProp Σ) : oltyO Σ i :=
    λ args ρ, Lty (olty_car args ρ).

  Global Instance ids_olty : Ids (olty Σ i) := λ _, inhabitant.
  Global Program Instance rename_olty : Rename (olty Σ i) :=
    λ r τ, Olty (rename r (olty_car τ)).
  Global Program Instance hsubst_olty : HSubst vl (olty Σ i) :=
    λ sb τ, Olty ((olty_car τ).|[sb]).

  Global Instance hsubstLemmas_olty : HSubstLemmas vl (olty Σ i).
  Proof.
    split => [T|//|s1 s2 T]; apply olty_eq => args ρ; f_ext => v.
    all: by rewrite /hsubst/= ?hsubst_id -?hsubst_comp.
  Qed.

  Global Instance: Sort (olty Σ i) := {}.

  Global Instance hsubst_olty_ne ρ :
    NonExpansive (hsubst (outer := oltyO Σ i) ρ).
  Proof. solve_proper_ho. Qed.

  Global Instance hsubst_olty_proper ρ :
    Proper ((≡) ==> (≡)) (hsubst (outer := oltyO Σ i) ρ) := ne_proper _.

  Lemma olty_subst_compose_ind τ args ρ1 ρ2 v: τ.|[ρ1] args ρ2 v ⊣⊢ τ args (ρ1 >> ρ2) v.
  Proof. apply hoEnvD_subst_compose_ind. Qed.

  Lemma olty_subst_compose τ args ρ1 ρ2 ρ3 :
    ρ1 >> ρ2 = ρ3 → τ.|[ρ1] args ρ2 ≡ τ args ρ3.
  Proof. apply hoEnvD_subst_compose. Qed.

  Lemma olty_weaken_one τ args ρ:
    shift τ args ρ ≡ τ args (stail ρ).
  Proof. apply hoEnvD_weaken_one. Qed.

  Lemma olty_subst_one τ v w args ρ:
    τ.|[v/] args ρ w ≡ τ args (v.[ρ] .: ρ) w.
  Proof. apply hoEnvD_subst_one. Qed.

  Lemma olty_subst_ids τ ρ {args} : τ args ρ ≡ τ.|[ρ] args ids.
  Proof. symmetry. apply olty_subst_compose. autosubst. Qed.

  Lemma olty_finsubst_commute_cl τ σ ρ v (HclT : nclosed τ (length σ)) args :
    τ.|[∞ σ] args ρ v ≡ τ args (∞ σ.|[ρ]) v.
  Proof.
    rewrite olty_subst_compose_ind !(olty_subst_ids τ) -hsubst_comp.
    (* *The* step requiring [HclT]. *)
    by rewrite (subst_compose HclT).
  Qed.

  (** Shift a type; [oShift T] and [shift T] have different reduction
  behavior. *)
  Definition oShift (T : oltyO Σ i) :=
    Olty (λ args ρ v, T args (stail ρ) v).

  (* Holds definitionally when id_subst does, so for any reasonable concrete language. *)

  Global Instance oShift_ne: NonExpansive oShift.
  Proof. solve_proper_ho. Qed.
  Global Instance oShift_proper : Proper ((≡) ==> (≡)) oShift := ne_proper _.
End olty_subst.

Global Instance: Params (@oShift) 2 := {}.

Section oShift.
  Context `{Σ : gFunctors} {i : nat}.

  Lemma oShift_eq (T : oltyO Σ i) : oShift T ≡ shift T.
  Proof. move=> args ρ v /=. by rewrite hoEnvD_weaken_one. Qed.

  Lemma oShift_subst (T : olty Σ i) ρ :
    (oShift T).|[up ρ] ≡ oShift T.|[ρ].
  Proof.
    (* Working but slow proof: *)
    (* rewrite !oShift_eq; autosubst. *)
    move=>args ξ v; rewrite /= /hsubst /hsubst_hoEnvD /stail/=;
      apply eq_equiv; do 2 f_equal; autosubst.
  Qed.
End oShift.

Notation oClose τ := (τ vnil).

(** Semantic typing contexts [Γ]; the paper only uses syntactic typing
contexts [Γ]. *)
Definition sCtx Σ := listO (oltyO Σ 0).

(** Part of the definition of [G⟦ Γ ⟧].
Define when an environment [ρ] conforms to a semantic typing context [Γ],
that is a list of semantic types.
*)
Reserved Notation "sG⟦ Γ ⟧* ρ" (at level 10).
Fixpoint env_oltyped `{dlangG Σ} (ρ : var → vl) (Γ : sCtx Σ) : iProp Σ :=
  match Γ with
  | φ :: Γ' => sG⟦ Γ' ⟧* (stail ρ) ∧ oClose φ ρ (shead ρ)
  | nil => True
  end
where "sG⟦ Γ ⟧* ρ" := (env_oltyped ρ Γ).
Global Instance: Params (@env_oltyped) 4 := {}.

(** ** Constructors for language-independent semantic types, corresponding to
[⊤], [⊥], [T₁ ∧ T₂], [T₁ ∨ T₂], [μ x. T], [▷]. *)
(** oLaterN *)
Section oLaterN.
  Context {Σ} {i : nat}.
  (** Semantic type constructor for [▷^n T] *)
  Definition oLaterN n (τ : oltyO Σ i) := Olty (λI args ρ v, ▷^n τ args ρ v).

  Global Instance oLaterN_ne m : NonExpansive (oLaterN m).
  Proof. solve_proper_ho. Qed.
  Global Instance oLaterN_proper m : Proper ((≡) ==> (≡)) (oLaterN m) := ne_proper _.

  Lemma oLaterN_eq n τ args ρ v : oLaterN n τ args ρ v = (▷^n τ args ρ v)%I.
  Proof. done. Qed.
End oLaterN.
(** Semantic type constructor for [▷ T] *)
Notation oLater := (oLaterN 1).
Global Instance: Params (@oLaterN) 3 := {}.

Section olty_ofe_2.
  Context `{dlangG Σ} {i : nat}.
  Implicit Types (φ : hoEnvD Σ i) (τ : oltyO Σ i).

  (** oLaterN, part 2 *)

  Lemma oLaterN_0 (T : olty Σ i) :
    oLaterN 0 T ≡ T.
  Proof. done. Qed.

  Lemma oLaterN_S (T : olty Σ i) n :
    oLaterN (S n) T ≡ oLater (oLaterN n T).
  Proof. done. Qed.

  Lemma oLaterN_Sr (T : olty Σ i) n :
    oLaterN (S n) T ≡ oLaterN n (oLater T).
  Proof. move => ???/=. by rewrite swap_later. Qed.

  Lemma oLaterN_plus {m n} {T : olty Σ i} :
    oLaterN (m + n) T ≡ oLaterN m (oLaterN n T).
  Proof. move=> ???. by rewrite/= laterN_plus. Qed.

  Global Instance env_oltyped_proper ρ : Proper ((≡) ==> (≡)) (env_oltyped ρ).
  Proof.
    move: ρ => + G1 G2 /equiv_Forall2.
    elim: G1 G2 => [|T1 G1 IHG1] [|T2 G2] ρ /=; [done|inversion 1..|] =>
      /(Forall2_cons_inv _ _ _ _) [HT HG]; f_equiv; [apply IHG1, HG|apply HT].
  Qed.

  Lemma s_interp_env_lookup Γ ρ (τ : olty Σ 0) x:
    Γ !! x = Some τ →
    sG⟦ Γ ⟧* ρ -∗ oClose (shiftN x τ) ρ (ρ x).
  Proof.
    elim: Γ ρ x => [//|τ' Γ' IHΓ] ρ x Hx /=.
    iDestruct 1 as "[Hg Hv]". move: x Hx => [ [->] | x Hx] /=.
    - rewrite hsubst_id. iApply "Hv".
    - rewrite hrenS.
      iApply (hoEnvD_weaken_one (shiftN x τ)).
      iApply (IHΓ (stail ρ) x Hx with "Hg").
  Qed.

  Definition olty0 (φ : envD Σ) : oltyO Σ 0 :=
    Olty (vopen φ).

  (** *** We can define once and for all basic "logical" types: top, bottom, and, or, later and μ. *)

  (** Semantic type constructor for [⊤] *)
  Definition oTop : oltyO Σ i := ⊤.
  Global Instance top_olty : Top (oltyO Σ i) := Olty ⊤.

  (** Semantic type constructor for [⊥] *)
  Definition oBot : oltyO Σ i := ⊥.
  Global Instance bot_olty : Bottom (oltyO Σ i) := Olty ⊥.

  (** Semantic type constructor for [T₁ ∧ T₂] *)
  Definition oAnd τ1 τ2 : oltyO Σ i := Olty (λI args ρ v, τ1 args ρ v ∧ τ2 args ρ v).
  Global Instance oAnd_ne : NonExpansive2 oAnd.
  Proof. solve_proper_ho. Qed.
  Global Instance oAnd_proper : Proper ((≡) ==> (≡) ==> (≡)) oAnd :=
    ne_proper_2 _.

  (** Semantic type constructor for [T₁ ∨ T₂] *)
  Definition oOr τ1 τ2 : oltyO Σ i := Olty (λI args ρ v, τ1 args ρ v ∨ τ2 args ρ v).
  Global Instance oOr_ne : NonExpansive2 oOr.
  Proof. solve_proper_ho. Qed.
  Global Instance oOr_proper : Proper ((≡) ==> (≡) ==> (≡)) oOr :=
    ne_proper_2 _.

  (** Semantic type constructor for [μ x. T] *)
  Definition oMu (τ : oltyO Σ i) : oltyO Σ i := Olty (λI args ρ v, τ args (v .: ρ) v).
  Global Instance oMu_ne : NonExpansive oMu.
  Proof. solve_proper_ho. Qed.
  Global Instance oMu_proper : Proper ((≡) ==> (≡)) oMu := ne_proper _.

  Lemma oMu_eq (τ : oltyO Σ i) args ρ v : oMu τ args ρ v = τ args (v .: ρ) v.
  Proof. done. Qed.

  Lemma oMu_shift (T : oltyO Σ i) : oMu (shift T) ≡ T.
  Proof. move=> args ρ v. by rewrite /= (hoEnvD_weaken_one T args _ v). Qed.

  Definition interp_expr (φ : hoEnvD Σ 0) : envPred tm Σ :=
    λI ρ t, WP t {{ vclose φ ρ }}.
  Global Arguments interp_expr /.

  Lemma sTEq_oMu_oLaterN (τ : oltyO Σ i) n :
    oLaterN n (oMu τ) ≡ oMu (oLaterN n τ).
  Proof. done. Qed.

  Lemma sTEq_oAnd_oLaterN (τ1 τ2 : oltyO Σ i) n :
    oLaterN n (oAnd τ1 τ2) ≡ oAnd (oLaterN n τ1) (oLaterN n τ2).
  Proof. move => args ρ v /=. by rewrite laterN_and. Qed.

  Lemma sTEq_oOr_oLaterN (τ1 τ2 : oltyO Σ i) n :
    oLaterN n (oOr τ1 τ2) ≡ oOr (oLaterN n τ1) (oLaterN n τ2).
  Proof. move => args ρ v /=. by rewrite laterN_or. Qed.
End olty_ofe_2.

Global Instance: Params (@oAnd) 2 := {}.
Global Instance: Params (@oOr) 2 := {}.
Global Instance: Params (@oMu) 2 := {}.

Notation "sE⟦ τ ⟧" := (interp_expr τ).
End Lty.
