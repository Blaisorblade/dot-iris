(** * Infrastructure for examples of DOT programs that uses HOAS. *)
(*
This infrastructure cannot be placed in [ex_utils.v] because [hoas.v] imports
[hoas.v].
*)
From stdpp Require Import strings.
From D Require Import tactics.
From D.Dot Require Import syn ex_utils.
From D.Dot Require Export hoas.

(** * Infinite loops *)
Module loopTms.
Import hoasNotation.

Definition hloopDefV : hvl := ν: self, {@
  val "loop" = λ: w, self @: "loop" $: w
  (* λ w, self.loop w. *)
}.
Definition hloopDefT : hty := val "loop" : ⊤ →: ⊥.
Definition hloopDefTConcr : hty := μ: _, {@ hloopDefT }.

Definition hloopFunTm : htm := hloopDefV @: "loop".
Definition hloopTm : htm := hloopFunTm $: hvint 0.

End loopTms.
