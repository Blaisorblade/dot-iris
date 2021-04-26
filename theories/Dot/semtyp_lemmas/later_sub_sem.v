(** * When is a context weaker than another? Semantic version. *)


From D Require Import proper.
From D.Dot Require Import dot_semtypes.

Set Suggest Proof Using.
Set Default Proof Using "Type".

(* This is specialized to [anil] because contexts only contain proper types anyway. *)
Definition s_ty_sub `{HdlangG: !dlangG Σ} (T1 T2 : oltyO Σ) := ∀ ρ v, T1 anil ρ v -∗ T2 anil ρ v.
Notation "s⊨T T1 <: T2" := (s_ty_sub T1 T2) (at level 74, T1, T2 at next level).

Definition s_ctx_sub `{HdlangG: !dlangG Σ} (Γ1 Γ2 : sCtx Σ) : Prop := ∀ ρ, sG⟦ Γ1 ⟧* ρ -∗ sG⟦ Γ2 ⟧* ρ.
Notation "s⊨G Γ1 <:* Γ2" := (s_ctx_sub Γ1 Γ2) (at level 74, Γ1, Γ2 at next level).

Section CtxSub.
  Context `{HdlangG: !dlangG Σ}.
  Implicit Type (T : ty) (Γ : ctx).

  (** * Basic lemmas about [s_ctx_sub]. *)
  #[global] Instance: RewriteRelation s_ty_sub := {}.
  #[global] Instance pre_s_ty_sub: PreOrder s_ty_sub.
  Proof. split; first done. by move => x y z H1 H2 ρ v; rewrite (H1 _ _). Qed.

  #[global] Instance: RewriteRelation s_ctx_sub := {}.
  #[global] Instance: PreOrder s_ctx_sub.
  Proof. split; first done. by move => x y z H1 H2 ρ; rewrite (H1 _). Qed.

  #[global] Instance: Proper (equiv ==> equiv ==> iff) s_ctx_sub.
  Proof.
    rewrite /s_ctx_sub => Γ1 Γ2 HΓ Δ1 Δ2 HΔ.
    by setoid_rewrite HΔ; setoid_rewrite HΓ.
  Qed.

  #[global] Instance cons_s_ctx_sub_mono : Proper (s_ty_sub ==> s_ctx_sub ==> s_ctx_sub) cons.
  Proof. move => T1 T2 HlT Γ1 Γ2 Hl ρ. cbn. by rewrite (HlT _) (Hl _). Qed.
  (* This is needed when flip ctx_sub arises from other rules. Doh. *)
  #[global] Instance cons_s_ctx_sub_flip_mono :
    Proper (flip s_ty_sub ==> flip s_ctx_sub ==> flip s_ctx_sub) cons.
  Proof. solve_proper. Qed.

  (** Typing is contravariant in [Γ].
  Note these instances are very specialized. *)
  #[global] Instance setp_mono e : Proper (flip s_ctx_sub ==> (=) ==> (⊢)) (setp e).
  Proof. rewrite /setp => Γ1 Γ2 Hweak T1 T2 ->. by setoid_rewrite (Hweak _). Qed.
  #[global] Instance setp_flip_mono e : Proper (s_ctx_sub ==> flip (=) ==> flip (⊢)) (setp e).
  Proof. apply: flip_proper_3. Qed.

  #[global] Instance sstpd_mono i : Proper (flip s_ctx_sub ==> (=) ==> (=) ==> (⊢)) (sstpd i).
  Proof. rewrite /sstpd => Γ1 Γ2 Hweak T1 T2 -> U1 U2 ->. by setoid_rewrite (Hweak _). Qed.
  #[global] Instance sstpi_flip_mono i : Proper (s_ctx_sub ==> flip (=) ==> flip (=) ==> flip (⊢)) (sstpd i).
  Proof. apply: flip_proper_4. Qed.

  #[global] Instance oLater_mono : Proper (s_ty_sub ==> s_ty_sub) oLater.
  Proof. intros x y Hl ??. by rewrite /= (Hl _ _). Qed.
  #[global] Instance oLater_flip_mono :
    Proper (flip s_ty_sub ==> flip s_ty_sub) oLater.
  Proof. apply: flip_proper_2. Qed.

  Lemma senv_TLater_commute (Γ : sCtx Σ) ρ : sG⟦ oLater <$> Γ ⟧* ρ ⊣⊢ ▷ sG⟦ Γ ⟧* ρ.
  Proof.
    elim: Γ ρ => [| T Γ IH] ρ; cbn; [|rewrite IH later_and];
      iSplit; by [iIntros "$" | iIntros "_"].
  Qed.
End CtxSub.

Typeclasses Opaque s_ty_sub.
Typeclasses Opaque s_ctx_sub.
