# Type Soundness for DOT via logical relations

Mechanization accompanying the paper "Scala Step-by-Step: Soundness for
DOT with Step-Indexed Logical Relations in Iris".

The mapping between the paper and this mechanization is described in
[correspondence.md](correspondence.md).

## File Layout

Here is a rough layout of the various files.

* `theories/Dot`: guarded DOT. Complete.
* `theories/DSub`, `theories/DSubSyn`: guarded D<:, complete (mentioned in a
  side note in the paper).
* `theories/`: General infrastructure.
* `theories/pure_program_logic`: define a "pure" variant of Iris's weakest
  precondition.
* `theories/iris_extra`: Additional Iris infrastructure.
  - `dlang.v`: instantiate Iris with a language setup for our proofs

Inside the `Dot` folder:
* `syn`: syntax
  - `syn.v`: definition of the basic SYNtax, and instantiate Iris with DOT
    operational semantics.
  - `synLemmas.v`: (SYNtactic Lemmas): lemmas about syntax and binding.
  - `rules.v`: lemmas about this language's operational semantics.
* `lr`: logical relation, semantic typing, compatibility lemmas
  - `path_wp.v`: define path weakest precondition;
  - `dlang_inst.v`: instantiate shared Iris setup from `dlang.v`;
  - `unary_lr.v`: definition of unary logical relation.
  Compatibility lemmas:
  - `lr_lemmasDefs.v`: lemmas about DEFinition typing;
  - `lr_lemmasTSel.v`: lemmas about TSel (type selection);
  - `lr_lemmasNoBinding.v`: various typing lemmas, not requiring `synLemmas.v`;
  - `lr_lemmas.v`: other misc typing lemmas.
* `stamping`: definitions and lemmas about stamping.
* `typing`: syntactic typing and auxiliary lemmas about it
  - `typingStamping.v`: prove stamping of typing derivations.
* `examples`: various gDOT snippets.
* `fundamental.v`: prove fundamental theorem, adequacy and type safety.

## Documentation for developers / additional docs (not relevant to paper)

See `development.md`.
