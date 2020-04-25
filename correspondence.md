All file paths in this file are relative to the `theories/` folder.

# Correspondence between paper and Coq dev

## Paper - development mapping

- gDOT syntax and operational semantics (Fig. 3): `Dot/syn/syn.v`
- gDOT unstamped typing judgments (Fig. 6, 7): `Dot/typing/unstamped_typing.v`
- Unstamped typing judgments, derived rules:
  `Dot/typing/unstamped_typing.v`,
  `Dot/typing/unstamped_typing_derived_rules.v`
- Stamped typing is defined in `Dot/typing/stamped_typing.v`.
  - Translation of typing derivations (Thm. 5.3) is proved in
    `Dot/typing/typing_stamping.v`.
- Iris proof rules (Fig. 8): most rules are proven from Iris itself, except two:
  - Impl-▷ is proven in from `iris_extra/swap_later_impl.v`.
  - Saved-Pred-Agree is proven as 
  `saved_ho_sem_type_agree` from [`iris_extra/saved_interp_dep.v`](theories/iris_extra/saved_interp_dep.v).
- Expression weakest precondition (Sec. 5.2.1): Definition and proof rules appear in
  `pure_program_logic`.
- Path weakest precondition (Sec. 5.2.2): defined in `Dot/lr/path_wp.v`.
- Logical relation (Fig. 9):
  - Auxiliary definitions appear in `iris_extra/dlang.v`.
  - Infrastructure on semantic predicates 
    is defined in `Dot/lr/lty.v` and `Dot/lr/dot_lty.v`.
  - The logical relation and semantic judgments are completed in `Dot/unary_lr.v`,
    including adequacy (Thm. 5.5).
- The fundamental theorem (Thm. 5.4) and type soundness for gDOT (Thm. 5.2)
  are proven in `Dot/fundamental.v`.

- Examples are in `Dot/examples/`. In particular:
  - Motivating example (Fig. 2, discussed in Sec. 1.1 and 4.0): `Dot/examples/from_pdot_mutual_rec.v`; here we
    simplified the use of `Option` away, but we do use `Option` when formalizing Sec. 6.3.
  - Covariant lists example (Fig. 10, Sec. 6.1): `Dot/examples/list.v`.
  - Positive integers example (Fig. 11, Sec. 6.2): `Dot/examples/positive_div.v`.
  - Unsafe motivating example (Fig. 12, Sec. 6.3): `Dot/examples/from_pdot_mutual_rec_sem.v`.

- For the code sizes reported in Sec. 6, see `codesize.md`.
- Testcase `tests/test_used_axioms.v` confirms that the only axiom we use is functional extensionality.

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

The paper's P-Var is here called `P_Val`.
The paper's D-And is here replaced by `D_Nil` and `D_Cons`.

## Differences between our paper (and technical appendix) and our Coq development.

- Notations such as \overbar{V}⟦ g ⟧ or \overbar{D}⟦ T ⟧ translate to Vs⟦ g ⟧
  and Ds⟦ T ⟧.

- Paper notation E⟦ T ⟧ would translate to E⟦ V⟦ T ⟧ ⟧ in this development;
  however, we generalize many definitions to semantic types, so that notation
  seldom appears.

- In Coq, definition lists use constructors nil and cons as usual, like in Coq
  developments by Rapoport et al. (e.g. pDOT).
  On paper, definition lists are instead constructed by singleton and
  merge operations (Fig. 3), as in other DOT papers.

- Semantic definition typing was significantly simplified on paper.

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
  `Dot/typing/storeless_typing.v`) an additional "storeless" typing judgment, a
  strict generalization of stamped typing.
  Storeless typing generalizes some rules of stamped typing to allow arbitrary
  values in paths, and not just variables. This is not at all necessary to our
  proof technique, but it simply allows typing more programs.
