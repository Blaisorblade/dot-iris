From stdpp Require Import strings.

From D Require Import tactics.
From D.Dot Require Import syn exampleInfra hoas.
From D.Dot.typing Require Import typing_unstamped typing_unstamped_derived.
Import DBNotation.
Import hoasNotation.

Definition pkgV := ν: p, {@
  type "C" = μ: this, {@ val "incr" : hTSing this };
  type "D" = μ: this, hTAnd (p @; "C") {@ val "decr" : hTSing this };
  val "newD" = λ: _,
    hlett: res := ν: this, {@ val "incr" = this; val "decr" = this }
    in: res
}.

Notation "t @:: l" := ((htskip t) @: l) (at level 59, l at next level).
Definition pkgUserE :=
  hlett: pkg := pkgV in:
  hlett: d := (pkg @: "newD") $: 0 in:
  (d @:: "incr") @: "decr".

Definition pkgVTy := μ: p, {@
  typeEq "C" $ μ: this, {@ val "incr" : hTSing this };
  typeEq "D" $ μ: this, hTAnd (p @; "C") {@ val "decr" : hTSing this };
  val "newD" : ⊤ →: p @; "D"
}.

Definition pkgUserTyB (this : hpath) : hty := {@ val "incr" : hTSing this; val "decr" : hTSing this }.
Definition pkgUserTy := μ: this, pkgUserTyB this.

Lemma pkgVTyped Γ : Γ u⊢ₜ pkgV : pkgVTy.
Proof.
  tcrush.
  hideCtx.
  eapply iT_Let with (T := pkgUserTy); tcrush; [
    eapply (iT_Path (p := pv _)), iP_Sngl_Refl, iP_Val; var..|simplSubst].
  eapply (iT_Sub (i := 0) (T1 := pkgUserTyB hx0)); first last.
  apply (iT_Path (p := pv _)).
  by apply (iP_Mu_E (T := pkgUserTyB hx0) (p := pv x0)); [stcrush| typconstructor; var].

  rewrite /pkgUserTyB.
Admitted.
  (* eapply iSub_Sel''; stcrush.
  typconstructor.
  varsub. simplSubst.
  lNext.
  ltcrush. simplSubst; rewrite iterate_S iterate_0.
  eapply iSub_Sel' with (U := ⊤); tcrush.
  varsub.
  asideLaters.
  mltcrush. *)

Lemma pkgUserTyped Γ : Γ u⊢ₜ pkgUserE : pkgUserTy.
Proof.
  eapply iT_Let with (T := pkgVTy); stcrush. apply pkgVTyped.
  eapply iT_Let with (T := hx0 @; "D"); stcrush.
  hideCtx; simplSubst.
  eapply (iT_All_E (T1 := 𝐍)); tcrush.
  eapply (iT_Sub (i := 0)); first last.
  apply (iT_Path (p := pv _)).
  apply (iP_Mu_E (T := hclose (val "newD" : 𝐍 →: hx0 @; "D")) (p := pv x0));
    [stcrush | typconstructor].
  by varsub; ltcrush.
  by cbn; case_decide; simplify_eq/=; tcrush.
  hideCtx; simplSubst.
  tcrush.
  (* eapply (iT_Sub (i := 1) (T1 := pkgUserTy)).
  rewrite /pkgUserTy /pkgUserTyB.
  ettrans; first apply
  ltcrush.
  typconstructor. *)
  eapply (iT_Sub (i := 1) ); last var.
  ettrans; last apply iLater_Sub; stcrush.
  eapply (iSel_Sub (L := ⊥)).
  (* apply (iP_Mu_E (T := pkgUserTyB hx0) (p := pv x0)). [stcrush| typconstructor; var]. *)

  typconstructor. varsub.
  mltcrush.
  hideCtx; simplSubst.
  eapply iSel_Sub.
  eapply (iT_Sub (i := 1) ); first last.
  var.

  simplSubst.


  varsub.
  mltcrush.
  hideCtx; simplSubst.
  econstructor.
