All file paths in this file are relative to the `theories/` folder.

# Correspondence between paper and Coq dev

- gDOT syntax and operational semantics are defined in `Dot/syn/syn.v`.
  - Unstamped typing is defined in `Dot/typing/typing_unstamped.v`.
  - Stamped typing is defined in `Dot/typing/typing_stamped.v`.

- Derived rule `(<:-Later-Shift)` is called `Sub_later_shift` in Coq.

- Typing rule `(D-Typ-Abs-Better)` is derived as `dty_typed_intermediate`.

- The fundamental theorem and type soundness for gDOT, are proven in
  `Dot/fundamental.v`.
  - Translation of typing derivations is proved in
    `Dot/typing/typingStamping.v`.

- Examples are in `Dot/examples/`.

- For the code sizes reported in Sec. 6, see `codesize.md`.

- Paper notation E⟦ T ⟧ would translate to E⟦ V⟦ T ⟧ ⟧ in this development;
  however, we generalize many definitions to semantic types.

## Differences between our paper (and technical appendix) and our Coq development.

- While in the paper unstamped and stamped DOT are represented using disjoint
  syntaxes, in Coq there is a single syntax, together with predicates
  `is_unstamped_?` and `is_stamped_?`, characterizing whether some AST is
  unstamped or stamped.

- Unlike in the appendix, our saved predicates support an additional argument
  `args : vec n vl` for some `n`. We always set `n = 0` to ignore this, but our
  implementation has additional flexibility.

- Our mechanization extends gDOT with some primitives, such as booleans and
  naturals, with some associated operations, even tho all of those are
  encodable.

- Compared to the paper, and even to the appendix, we describe (in
  `Dot/typing/typing_storeless.v`) an additional "storeless" typing judgment, a
  strict generalization of stamped typing.
  Storeless typing generalizes some rules of stamped typing to allow arbitrary
  values in paths, and not just variables. This is not at all necessary to our
  proof technique, but it simply allows typing more programs.

- For convenience, we add to storeless typeless "reflection" rules `Sem_typed`,
  `sem_ptyped` and `Sem_stp`, such that semantic typing implies storeless
  semantic typing. That's just a convenience to prove semantic typing more
  easily, as syntactic typing supports better automation.
