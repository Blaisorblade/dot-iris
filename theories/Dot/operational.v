From D Require Import dlang.
From D.Dot Require Export syn.

Module LiftWp := LiftWp syn syn.
Export field_lookup LiftWp.

Class dotG Σ := DotG {
  dot_dlang :> dlangG Σ
}.
Existing Instance DotG.

(* For abstracting synToSem. *)
Class dotInterpG Σ := DotInterpG {
  dot_interp: ty -> vls -> vl -> iProp Σ
}.
