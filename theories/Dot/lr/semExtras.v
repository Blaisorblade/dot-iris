From iris.proofmode Require Import tactics.
From D.Dot Require Import unary_lr lr_lemmasDefs.

Implicit Types
         (L T U: ty) (v: vl) (e: tm) (d: dm) (ds: dms) (p : path)
         (Γ : ctx).

Section Sec.
  Context `{HdlangG: dlangG Σ}.

  (*XXX : move away from here. Avoid auto-dropping box (and unfolding) when introducing ietp persistently. *)
  Instance: IntoPersistent false (ietp Γ T e) (ietp Γ T e) | 0 := _.

End Sec.
