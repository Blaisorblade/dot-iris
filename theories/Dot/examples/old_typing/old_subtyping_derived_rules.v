From D Require Import tactics.
From D.Dot Require Import unstampedness_binding.
From D.Dot Require Import path_repl_lemmas.
From D.Dot Require Import syn ex_utils old_subtyping.
Import DBNotation.

Ltac subtcrush := repeat first [ eassumption | reflexivity | subtypconstructor | stcrush ].

Ltac subwtcrush := repeat first [ fast_done | subtypconstructor | stcrush ] ; try solve [
  first [
    by eauto 3 using is_unstamped_TLater_n, is_unstamped_ren1_ty |
    try_once is_unstamped_weaken_ty ]; eauto].

Ltac asideLaters :=
  repeat first
    [ettrans; last (apply iSub_Later; subtcrush)|
    ettrans; first (apply iLater_Sub; subtcrush)].

Ltac lNext := ettrans; first apply iAnd2_Sub; subtcrush.
Ltac lThis := ettrans; first apply iAnd1_Sub; subtcrush.

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
Ltac subltcrush := subtcrush; repeat lookup.

Lemma iSub_SelL {Γ p U l L i} :
  Γ u⊢ₚ p : TTMemL l L U, i →
  Γ u⊢ₜ TLater L, i <: TSel p l, i.
Proof. intros; exact: iSub_Sel. Qed.

Lemma iSel_SubL {Γ p L l U i} :
  Γ u⊢ₚ p : TTMemL l L U, i →
  Γ u⊢ₜ TSel p l, i <: TLater U, i.
Proof. intros; exact: iSel_Sub. Qed.

Lemma iSub_Sel' U {Γ p l L i} :
  Γ u⊢ₚ p : TTMemL l L U, i →
  Γ u⊢ₜ L, i <: TSel p l, i.
Proof. intros; ettrans; last exact: (iSub_Sel (p := p)); subtcrush. Qed.

(** Specialization of [iSub_Sel'] for convenience. *)
Lemma iSub_Sel'' Γ {p l L i} :
  Γ u⊢ₚ p : TTMemL l L L, i → Γ u⊢ₜ L, i <: TSel p l, i.
Proof. apply iSub_Sel'. Qed.

(** * Manipulating laters, basics. *)

Lemma iSub_AddIJ {Γ T} i j :
  Γ u⊢ₜ T, j <: T, i + j.
Proof.
  elim: i => [|n IHn]; first subtcrush.
  ettrans; first apply IHn.
  ettrans; [exact: iSub_Add_Later | subtcrush].
Qed.

Lemma iSub_AddIJ' {Γ T} i j (Hle : i <= j) :
  Γ u⊢ₜ T, i <: T, j.
Proof. rewrite -(Nat.sub_add i j Hle). exact: iSub_AddIJ. Qed.

Lemma iSub_AddI Γ T i :
  Γ u⊢ₜ T, 0 <: T, i.
Proof. apply (iSub_AddIJ' 0 i); by [|lia]. Qed.

Lemma path_tp_delay {Γ p T i j} : i <= j →
  Γ u⊢ₚ p : T, i → Γ u⊢ₚ p : T, j.
Proof.
  intros Hle Hp.
  rewrite -(Nat.sub_add i j Hle) (Nat.add_comm _ i). move: {j Hle} (j - i) => k.
  eapply iP_ISub, Hp.
  apply: iSub_AddIJ'; by [|lia].
Qed.

(** * Derived constructions. *)
(* We can derive rules iSub_Bind_1 and iSub_Bind_2 (the latter only conjectured) from
  "Type Soundness for Dependent Object Types (DOT)", Rompf and Amin, OOPSLA '16. *)
Lemma iSub_Bind_1 Γ T1 T2 i :
  iterate TLater i T1 :: Γ u⊢ₜ T1, i <: shift T2, i →
  Γ u⊢ₜ μ T1, i <: T2, i.
Proof.
  intros Hsub.
  ettrans; first exact: (iMu_Sub_Mu Hsub).
  exact: iMu_Sub.
Qed.

Lemma iSub_Bind_2 Γ T1 T2 i :
  iterate TLater i (shift T1) :: Γ u⊢ₜ shift T1, i <: T2, i →
  Γ u⊢ₜ T1, i <: μ T2, i.
Proof.
  intros Hsub.
  ettrans; last apply (iMu_Sub_Mu Hsub); exact: iSub_Mu.
Qed.

Lemma iSub_Bind_1' Γ T1 T2 :
  T1 :: Γ u⊢ₜ T1, 0 <: shift T2, 0 →
  Γ u⊢ₜ μ T1, 0 <: T2, 0.
Proof. intros; exact: iSub_Bind_1. Qed.

Lemma iSub_Bind_2' Γ T1 T2 :
  shift T1 :: Γ u⊢ₜ shift T1, 0 <: T2, 0 →
  Γ u⊢ₜ T1, 0 <: μ T2, 0.
Proof. intros; exact: iSub_Bind_2. Qed.

Lemma iMu_Sub' {Γ T T' i} :
  T' = shift T →
  Γ u⊢ₜ μ T', i <: T, i.
Proof. intros; subst. auto. Qed.

#[global] Hint Resolve is_unstamped_path_root : core.

Lemma iP_Sngl_Sym Γ p q i :
  is_unstamped_path' (length Γ) q →
  Γ u⊢ₚ p : TSing q, i →
  Γ u⊢ₚ q : TSing p, i.
Proof.
  intros Hus Hpq. eapply iP_ISub'.
  eapply (iSngl_Sub_Sym Hpq). by apply iSngl_Sub_Self, Hpq.
  eapply iP_Sngl_Refl.
  by apply (iP_Sngl_Inv Hpq); eauto.
Qed.

Lemma iSngl_pq_Sub_inv {Γ i p q T1 T2} :
  T1 ~Tp[ p := q ]* T2 →
  is_unstamped_path' (length Γ) p →
  Γ u⊢ₚ q : TSing p, i →
  Γ u⊢ₜ T1, i <: T2, i.
Proof. intros. by eapply iSngl_pq_Sub, iP_Sngl_Sym. Qed.

Lemma iP_And_I {Γ p T1 T2 i} :
  Γ u⊢ₚ p : T1, i →
  Γ u⊢ₚ p : T2, i →
  Γ u⊢ₚ p : TAnd T1 T2, i.
Proof.
  intros Hp1 Hp2. eapply iP_ISub', iP_Sngl_Refl, Hp1.
  apply iSub_And; exact: iSngl_Sub_Self.
Qed.

(** * Manipulating laters, more. *)
Lemma iSub_LaterN Γ T i j :
  Γ u⊢ₜ T, j + i <: iterate TLater j T, i.
Proof.
  elim: j T => /= [|j IHj] T ; rewrite ?iterate_0 ?iterate_Sr /=; subtcrush.
  ettrans.
  - exact: iSub_Later.
  - apply (IHj (TLater T)); stcrush.
Qed.

Lemma iLaterN_Sub {Γ T} i j :
  Γ u⊢ₜ iterate TLater j T, i <: T, j + i.
Proof.
  elim: j T => /= [|j IHj] T; rewrite ?iterate_0 ?iterate_Sr /=; subtcrush.
  ettrans.
  - apply (IHj (TLater T)); stcrush.
  - exact: iLater_Sub.
Qed.

Lemma iLaterN_Sub_LaterN {Γ i1 i2 j1 j2 T1 T2}
  (Hsub : Γ u⊢ₜ T1, i1 + i2 <: T2, j1 + j2) :
  Γ u⊢ₜ iterate ▶:%ty i2 T1, i1 <: iterate ▶:%ty j2 T2, j1.
Proof.
  ettrans; first apply iLaterN_Sub.
  ettrans; last apply iSub_LaterN.
  rewrite (Nat.add_comm i2 i1) (Nat.add_comm j2 j1).
  exact: Hsub.
Qed.

Lemma selfIntersect Γ T U i j :
  Γ u⊢ₜ T, i <: U, j + i →
  Γ u⊢ₜ T, i <: TAnd U T, j + i .
Proof. intros; subtcrush. exact: iSub_AddIJ. Qed.

Lemma iAnd_Later_Sub_Distr Γ T1 T2 i :
  Γ u⊢ₜ TAnd (TLater T1) (TLater T2), i <: TLater (TAnd T1 T2), i.
Proof. intros; asideLaters; subtcrush; [lThis|lNext]. Qed.

(** Inverse of [iAnd_Later_Sub_Distr]. *)
Lemma iAnd_Later_Sub_Distr_inv Γ T1 T2 i :
  Γ u⊢ₜ TLater (TAnd T1 T2), i <: TAnd (TLater T1) (TLater T2), i.
Proof. intros; subtcrush. Qed.

Lemma iOr_Later_Sub_Distr Γ T1 T2 i :
  Γ u⊢ₜ TOr (TLater T1) (TLater T2), i <: TLater (TOr T1 T2), i.
Proof. intros; subtcrush. Qed.

(** Inverse of [iOr_Later_Sub_Distr]. *)
Lemma iOr_Later_Sub_Distr_inv Γ T1 T2 i :
  Γ u⊢ₜ TLater (TOr T1 T2), i <: TOr (TLater T1) (TLater T2), i.
Proof.
  intros; asideLaters; subtypconstructor; ettrans;
    [| apply iSub_Or1 | | apply iSub_Or2]; subtcrush.
Qed.

(** TLater swaps with TMu, part 1. *)
Lemma iMu_Later_Sub_Distr Γ T i :
  Γ u⊢ₜ TMu (TLater T), i <: TLater (TMu T), i.
Proof. intros; asideLaters; subtcrush. Qed.

(** TLater swaps with TMu, part 2. *)
Lemma iMu_Later_Sub_Distr_inv Γ T i :
  Γ u⊢ₜ TLater (TMu T), i <: TMu (TLater T), i.
Proof. intros; asideLaters; subtcrush. Qed.

(** Show that [singleton_Mu_[12]] and [iP_Mu_[IE]] are interderivable. *)
Lemma singleton_Mu_1 {Γ p T i} :
  Γ u⊢ₚ p : TMu T, i →
  is_unstamped_ty' (length Γ).+1 T →
  Γ u⊢ₜ TSing p, i <: T .Tp[ p /], i.
Proof. intros Hp Hu; apply iSngl_Sub_Self, (iP_Mu_E Hu Hp). Qed.

Lemma singleton_Mu_2 {Γ p T i} :
  Γ u⊢ₚ p : T .Tp[ p /], i →
  is_unstamped_ty' (length Γ).+1 T →
  Γ u⊢ₜ TSing p, i <: TMu T, i.
Proof. intros Hp Hu; apply iSngl_Sub_Self, (iP_Mu_I Hu Hp). Qed.

(* Avoid automation, to ensure we don't use [iP_Mu_E] to show them. *)
Lemma iP_Mu_E_alt {Γ T p i} :
  Γ u⊢ₚ p : TMu T, i →
  is_unstamped_ty' (length Γ).+1 T →
  Γ u⊢ₚ p : T .Tp[ p /], i.
Proof.
  intros Hp Hu. eapply iP_ISub', (iP_Sngl_Refl Hp).
  apply (singleton_Mu_1 Hp Hu).
Qed.

Lemma iP_Mu_I_alt {Γ T p i} :
  Γ u⊢ₚ p : T .Tp[ p /], i →
  is_unstamped_ty' (length Γ).+1 T →
  Γ u⊢ₚ p : TMu T, i.
Proof.
  intros Hp Hu. eapply iP_ISub', (iP_Sngl_Refl Hp).
  apply (singleton_Mu_2 Hp Hu).
Qed.

(**
Show soundness of subtyping for recursive types in the Dotty compiler — just cases in subtype checking.

The first case is in
https://github.com/lampepfl/dotty/blob/0.20.0-RC1/compiler/src/dotty/tools/dotc/core/TypeComparer.scala#L550-L552
And that matches iMu_Sub_Mu.

https://github.com/lampepfl/dotty/blob/0.20.0-RC1/compiler/src/dotty/tools/dotc/core/TypeComparer.scala#L554-L557
We formalize that as the derived rule below.

The action of [fixRecs] depends on the type [T1] of [p].
Hence, here we we assume the action of [fixRecs] has already been carried out:
to do that, one must unfold top-level recursive types in the type of [p],
as allowed through [P_Mu_E], rules for intersection types and intersection introduction.
On the other hand, this derived rule handles the substitution in [T2] directly.
*)
Lemma singleton_Mu_dotty1 {Γ p i T1' T2} :
  Γ u⊢ₜ T1', i <: T2 .Tp[ p /], i →
  Γ u⊢ₚ p : T1', i →
  is_unstamped_ty' (length Γ).+1 T2 →
  Γ u⊢ₜ TSing p, i <: TMu T2, i.
Proof.
  intros Hsub Hp Hu.
  apply singleton_Mu_2, Hu.
  apply (iP_ISub' Hsub Hp).
Qed.

Lemma iP_LaterN {Γ p T i j} :
  Γ u⊢ₚ p : iterate TLater j T, i →
  Γ u⊢ₚ p : T, i + j.
Proof.
  elim: j i => [|j IHj] i Hp; rewrite (plusnO, plusnS); first done.
  apply (IHj i.+1), iP_Later, Hp; subtcrush; exact: is_unstamped_TLater_n.
Qed.

Lemma iMu_LaterN_Sub_Distr_inv {Γ T i n} :
  Γ u⊢ₜ iterate TLater n (TMu T), i <: TMu (iterate TLater n T), i.
Proof.
  elim: n i => [|n IHn] i; first subtcrush; rewrite !iterate_S.
  ettrans; last apply iMu_Later_Sub_Distr_inv.
  by asideLaters; subwtcrush.
Qed.

Lemma iMu_LaterN_Sub_Distr {Γ T i n} :
  Γ u⊢ₜ TMu (iterate TLater n T), i <: iterate TLater n (TMu T), i.
Proof.
  elim: n i => [|n IHn] i; first subtcrush; rewrite !iterate_S.
  ettrans; first apply iMu_Later_Sub_Distr.
  by asideLaters; subwtcrush.
Qed.

(* Lattice theory *)
Lemma iOr_Sub_split Γ T1 T2 U1 U2 i :
  Γ u⊢ₜ T1, i <: U1, i →
  Γ u⊢ₜ T2, i <: U2, i →
  Γ u⊢ₜ TOr T1 T2, i <: TOr U1 U2, i.
Proof.
  intros.
  apply iOr_Sub; [
    eapply iSub_Trans, iSub_Or1 | eapply iSub_Trans, iSub_Or2]; subtcrush.
Qed.

Lemma iSub_And_split Γ T1 T2 U1 U2 i :
  Γ u⊢ₜ T1, i <: U1, i →
  Γ u⊢ₜ T2, i <: U2, i →
  Γ u⊢ₜ TAnd T1 T2, i <: TAnd U1 U2, i.
Proof.
  intros; apply iSub_And; [
    eapply iSub_Trans; first apply iAnd1_Sub |
    eapply iSub_Trans; first apply iAnd2_Sub]; subtcrush.
Qed.

Lemma iDistr_And_Or_Sub_inv {Γ S T U i} :
  Γ u⊢ₜ TOr (TAnd S U) (TAnd T U), i <: TAnd (TOr S T) U , i.
Proof.
  intros; apply iOr_Sub; apply iSub_And; subtcrush;
    (ettrans; first apply iAnd1_Sub); subtcrush.
Qed.

Lemma iDistr_Or_And_Sub {Γ S T U i} :
  Γ u⊢ₜ TOr (TAnd S T) U , i <: TAnd (TOr S U) (TOr T U), i.
Proof.
  intros; apply iOr_Sub; apply iSub_And; subtcrush;
    (ettrans; last apply iSub_Or1); subtcrush.
Qed.

Lemma comm_and {Γ T U i} :
  Γ u⊢ₜ TAnd T U, i <: TAnd U T, i.
Proof. intros; subtcrush. Qed.

Lemma comm_or {Γ T U i} :
  Γ u⊢ₜ TOr T U, i <: TOr U T, i.
Proof. intros; subtcrush. Qed.

Lemma absorb_and_or {Γ T U i} :
  Γ u⊢ₜ TAnd U (TOr T U), i <: U, i.
Proof. intros; subtcrush. Qed.

Lemma absorb_or_and {Γ T U i} :
  Γ u⊢ₜ TOr U (TAnd T U), i <: U, i.
Proof. intros; subtcrush. Qed.

Lemma absorb_or_and2 {Γ T U i} :
  Γ u⊢ₜ TOr (TAnd T U) T, i <: T, i.
Proof. intros; ettrans; first apply comm_or; subtcrush. Qed.

Lemma assoc_or {Γ S T U i} :
  Γ u⊢ₜ TOr (TOr S T) U, i <: TOr S (TOr T U), i.
Proof. intros; subtcrush; (ettrans; last apply iSub_Or2); subtcrush. Qed.

Lemma assoc_and {Γ S T U i} :
  Γ u⊢ₜ TAnd (TAnd S T) U, i <: TAnd S (TAnd T U), i.
Proof. intros. subtcrush; lThis. Qed.

(* Based on Lemma 4.3 in
https://books.google.co.uk/books?id=vVVTxeuiyvQC&lpg=PA104&pg=PA85#v=onepage&q&f=false.
Would be much easier to formalize with setoid rewriting.
*)
Lemma iDistr_Or_And_Sub_inv {Γ S T U i} :
  Γ u⊢ₜ TAnd (TOr S U) (TOr T U), i <: TOr (TAnd S T) U , i.
Proof.
  intros.
  ettrans; first apply iDistr_And_Or_Sub; stcrush => //.
  ettrans; first apply iOr_Sub_split, absorb_and_or; try apply iSub_Refl;
    stcrush => //.
  ettrans; first apply iOr_Sub_split; try apply (iSub_Refl _ U);
    try (ettrans; first apply (comm_and (T := S))); try apply iDistr_And_Or_Sub; stcrush => //.
  ettrans; first apply assoc_or; stcrush => //.
  ettrans; first apply iOr_Sub_split; last apply iSub_Refl; subtcrush.
Qed.

(* Show how TMu commutes with TAnd and TOr. *)
Lemma iMu_And Γ T1 T2 i :
  Γ u⊢ₜ TMu (TAnd T1 T2), i <: TAnd (TMu T1) (TMu T2), i.
Proof. subtcrush. Qed.

Lemma iOr_Mu Γ T1 T2 i :
  Γ u⊢ₜ TOr (TMu T1) (TMu T2), i <: TMu (TOr T1 T2), i.
Proof. subtcrush. Qed.

(* These rules deal with "trivial" recursive types; for the general case see [TAnd_Mu].
For now I failed to prove [TOr_Mu] but it seems much less important. *)
Lemma iAnd_Mu_free Γ T1 T2 i :
  Γ u⊢ₜ TAnd (μ (shift T1)) (TMu (shift T2)), i <: μ (shift (TAnd T1 T2)), i.
Proof.
  ettrans; [|apply iSub_Mu].
  apply iSub_And_split; subtcrush.
Qed.

Lemma iMu_Or_free Γ T1 T2 i :
  Γ u⊢ₜ μ (shift (TOr T1 T2)), i <: TOr (μ (shift T1)) (TMu (shift T2)), i.
Proof.
  ettrans; [apply iMu_Sub|].
  apply iOr_Sub_split; subtcrush.
Qed.
