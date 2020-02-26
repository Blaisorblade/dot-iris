All file paths in this file are relative to the `theories/` folder.

# Correspondence between paper and Coq dev

- gDOT syntax and operational semantics are defined in `Dot/syn/syn.v`.
  - Unstamped typing is defined in `Dot/typing/typing_unstamped.v`.
  - Stamped typing is defined in `Dot/typing/typing_stamped.v`.

- Derived rule `(<:-Later-Shift)` is called `Sub_later_shift` in Coq.

- The fundamental theorem and type soundness for gDOT, are proven in
  `Dot/fundamental.v`.
  - Translation of typing derivations is proved in
    `Dot/typing/typingStamping.v`.

- Examples are in `Dot/examples/`.

- For the code sizes reported in Sec. 6, see `codesize.md`.

- Paper notation E⟦ T ⟧ would translate to E⟦ V⟦ T ⟧ ⟧ in this development;
  however, we generalize many definitions to semantic types.

- Notations such as \overbar{V}⟦ g ⟧ or \overbar{D}⟦ T ⟧ translate to Vs⟦ g ⟧
  and Ds⟦ T ⟧.

## Typing lemma naming conventions

Prefixes: T P D

Translation table:
- -> _
<: -> Sub
∀ -> All
{} -> Obj

For each rule, there are up to three versions, with corresponding prefixes.
- Purely semantic lemma (s)
- Syntactic lemma
- Syntactic typing rule (i for inductive).

The paper's P-Var is here called (s|i|)P_Val.

## Differences between our paper (and technical appendix) and our Coq development.

- While in the paper unstamped and stamped DOT are represented using disjoint
  syntaxes, in Coq there is a single syntax, together with predicates
  `is_unstamped_?` and `is_stamped_?`, characterizing whether some AST is
  unstamped or stamped.

- Unlike in the appendix, our saved predicates support an additional argument
  `args : vec n vl` for some `n`. We always set `n = 0` to ignore this, but our
  implementation has additional flexibility that we plan to use in the future.

- Our mechanization extends gDOT with some primitives, such as booleans and
  naturals, with some associated operations, even tho all of those are
  encodable.

- Compared to the paper, and even to the appendix, we describe (in
  `Dot/typing/typing_storeless.v`) an additional "storeless" typing judgment, a
  strict generalization of stamped typing.
  Storeless typing generalizes some rules of stamped typing to allow arbitrary
  values in paths, and not just variables. This is not at all necessary to our
  proof technique, but it simply allows typing more programs.
