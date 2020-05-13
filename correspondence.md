All file paths in this file are relative to the [`theories/`](theories/) folder.

# Correspondence between paper and Coq dev

## Differences between our paper (and technical appendix) and our Coq development

There are a number of small differences between the paper presentation
of gDOT and the formalization in Coq. We briefly discuss them here.

- Notations such as `\overbar{V}⟦ g ⟧` or `\overbar{D}⟦ T ⟧` translate to `Vs⟦ g ⟧`
  and `Ds⟦ T ⟧`.

- In Coq, definition lists use constructors `nil` and `cons` as usual, like in Coq
  developments by Rapoport et al. (e.g. pDOT).
  On paper, definition lists are instead constructed by singleton and
  merge operations (Fig. 3), as in other DOT papers.

- While in the paper unstamped and stamped DOT are represented using disjoint
  syntaxes, in Coq there is a single syntax, together with predicates
  `is_unstamped_?` and `is_stamped_?`, characterizing whether some AST is
  unstamped or stamped.

- Unlike in the appendix, our saved predicates and semantic types support an
  additional argument `args` of type `vec n vl`, where `n` is the _arity_ of the
  semantic type. gDOT only uses predicates of arity `n = 0`, which are
  equivalent to the predicates used on paper.

- Our mechanization extends gDOT with some primitives, such as booleans and
  naturals, with some associated operations, even though all of those primitives
  are encodable.

- Compared to the paper, and even to the appendix, we describe (in
  [`Dot/typing/storeless_typing.v`](theories/Dot/typing/storeless_typing.v))
  an additional "storeless" typing judgment, a
  strict generalization of stamped typing.
  Storeless typing generalizes some rules of stamped typing to allow arbitrary
  values in paths, and not just variables. This is not at all necessary to our
  proof technique, but it simply allows typing more programs while still
  using a syntactic typing judgment.

- We inherit various superficial differences between the on-paper presentation
  of Iris and the actual implementation.
  For instance, in Coq `iProp` is parameterized by an additional index `Σ`.
  We hope such matters are not distracting, and refer to
  https://gitlab.mpi-sws.org/iris/iris/-/tree/master/#further-resources
  for further info.

### Semantic types

The Coq presentation of our logical relation and semantic typing judgments is
more general than on paper (Fig. 9), which inlines together several separate
definitions.

- On paper, the value interpretation `V⟦ T ⟧` maps syntactic types `Type` to
  semantic types, defined as environment-indexed persistent predicates over
  values, of type `Env → Val → iProp`.
  Instead, in Coq, semantic types are a first-class notion, described by Coq
  type `olty Σ 0`; most of Fig. 9 is defined as combinators on semantic types,
  without reference to syntactic types, and Coq notation `V⟦ T ⟧` translates
  syntactic types into semantic types using those combinators.

  - Paper notations `E⟦ T ⟧` and `G⟦ T ⟧` come with counterparts on Semantic types,
    called respectively `sE⟦ T ⟧` and `sG⟦ T ⟧`.

- Similarly, the definition interpretation `Ds⟦ T ⟧` produces semantic
  _definition_ types, called `dslty Σ`.
  Definition typing lemmas require semantic types and semantic definition types
  to satisfy certain coherence constraints; we define a notion of "complete
  semantic types" `clty Σ` containing a semantic type, a semantic
  definition type, and proofs of their consistency.

## Paper — development mapping

### Trusted base
To confirm that we have proved type soundness for gDOT, and that our examples
are well-typed and/or type-safe, it is sufficient to check our type soundness
theorem, and the involved definitions.

Sec. 2:
- syntax and operational semantics for unstamped and stamped gDOT (Fig. 3, Sec. 5.1):
  [`Dot/syn/syn.v`](theories/Dot/syn/syn.v).
  - values, expressions, paths, definition bodies and lists, types are called
    respectively `vl`, `tm`, `path`, `dm`, `dms`, `ty`;
  - member selection: `objLookup`
  - evaluation contexts: `list ectx_item`.
  - operational semantics:
    - head-reduction: `head_step`; reduction: `prim_step`.

Sec. 4:
- gDOT unstamped typing judgments (Sec. 4, Fig. 6, 7):
  - The `Γ1 ≫ ▷ Γ2` judgment, and auxiliary judgments for primitive types:
    [`Dot/typing/typing_aux_defs.v`](theories/Dot/typing/typing_aux_defs.v)
  - Primitive typing rules: [`Dot/typing/unstamped_typing.v`](theories/Dot/typing/unstamped_typing.v)
  - Derived rules:
    [`Dot/typing/unstamped_typing.v`](theories/Dot/typing/unstamped_typing.v),
    [`Dot/typing/unstamped_typing_derived_rules.v`](theories/Dot/typing/unstamped_typing_derived_rules.v)

Sec. 5:
- Safety (Def. 5.1) is defined as `safe` in
  [`iris_extra/det_reduction.v`](theories/iris_extra/det_reduction.v).
- Type soundness for gDOT (Thm. 5.2) is proven in
  [`Dot/fundamental.v`](theories/Dot/fundamental.v) as `Corollary
  type_soundness`.

Sec. 6:
- Examples are written using high-level notations than the one defined in `syn.v`:
  - `Module DBNotation` is defined in
    [`Dot/examples/ex_utils.v`](theories/Dot/examples/ex_utils.v); it is merely
    an alternative Unicode notation for deBruijn terms.
  - `Module hoasNotation` is defined in
    [`Dot/examples/hoas.v`](theories/Dot/examples/hoas.v); it defines an HOAS
    frontend for writing concrete terms.

- Examples are in [`Dot/examples/`](theories/Dot/examples/). In particular:
  - Motivating example (Fig. 2, discussed in Sec. 1.1 and 4.0):
    [`Dot/examples/from_pdot_mutual_rec.v`](theories/Dot/examples/from_pdot_mutual_rec.v).
  - Covariant lists example (Fig. 10, Sec. 6.1): [`Dot/examples/list.v`](theories/Dot/examples/list.v).
  - Positive integers example (Fig. 11, Sec. 6.2): [`Dot/examples/positive_div.v`](theories/Dot/examples/positive_div.v).
  - Unsafe motivating example (Fig. 12, Sec. 6.3): [`Dot/examples/from_pdot_mutual_rec_sem.v`](theories/Dot/examples/from_pdot_mutual_rec_sem.v).

Sec. 7:
- For the (updated) code sizes, see [`codesize.md`](codesize.md).
- Testcase [`tests/test_used_axioms.v`](tests/test_used_axioms.v) confirms that the only axiom we use is functional extensionality.

### Proofs

The proof strategy we describe in the paper is implemented in the following files.

Sec. 5:
- Stamped typing is defined in [`Dot/typing/stamped_typing.v`](theories/Dot/typing/stamped_typing.v).
  - Translation of typing derivations (Thm. 5.3) is proved in
    [`Dot/typing/typing_stamping.v`](theories/Dot/typing/typing_stamping.v).
- Iris proof rules (Sec. 5, Fig. 8): Iris proves all rules shown, except the following ones:
  - Impl-▷ is proven in from [`iris_extra/swap_later_impl.v`](theories/iris_extra/swap_later_impl.v).
  - Saved-Pred-Agree is proven as
  `saved_ho_sem_type_agree` from [`iris_extra/saved_interp_dep.v`](theories/iris_extra/saved_interp_dep.v).
- Expression weakest precondition (Sec. 5.2.1): Definition and proof rules appear in
  [`pure_program_logic`](theories/pure_program_logic).
- Path weakest precondition (Sec. 5.2.2): defined in [`Dot/lr/path_wp.v`](theories/Dot/lr/path_wp.v).
- Logical relation (Sec. 5, Fig. 9):
  - Auxiliary definitions appear in [`iris_extra/dlang.v`](theories/iris_extra/dlang.v).
  - Infrastructure on semantic predicates
    is defined in [`Dot/lr/lty.v`](theories/Dot/lr/lty.v) and [`Dot/lr/dot_lty.v`](theories/Dot/lr/dot_lty.v).
  - The core definition

  - The logical relation and semantic judgments are completed in [`Dot/unary_lr.v`](theories/Dot/unary_lr.v),
    including adequacy (Thm. 5.5).
- The fundamental theorem (Thm. 5.4) is proven in [`Dot/fundamental.v`](theories/Dot/fundamental.v).

## Typing lemma naming conventions

Names of typing rules and lemmas can be derived mechanically from those in
the paper, with a couple of exceptions.

Translation table of symbols in names:
| Paper   | Coq    |
| :-----: | :----: |
| `-`     | `_`    |
| `<:`    | `Sub`  |
| `∀`     | `All`  |
| `{}`    | `Obj`  |

- Exceptions:
  - The paper's P-Var is here called `P_Val`.
  - The paper's D-And is here replaced by `D_Nil` and `D_Cons`.

- The names of all typing rules, but not of subtyping rules, have a prefix
  that identifies the judgment:

| Prefix | Typing Judgment |
| :----: | :-------------- |
| `T`    | Expression      |
| `P`    | Path            |
| `D`    | Definition      |

- The names of subtyping rules contain `<:` or `Sub`, and the name of the
  type constructor the rule concerns; the order relates to the shape of the rule. For
  instance rule `<:-μ` will conclude that type `T <: μ x. T`, while
  rule `μ-<:` will conclude that some type `μ x. T <: T`, assuming certain
  premises.

For each typing rule (say, `T_Path`), there are up to three versions, with
corresponding prefixes.
- A syntactic typing rule, with prefix `i` (for inductive); for instance, `iT_Path`.
- A semantic lemma, as described in the paper, with no prefix; for instance, `T_Path`.
- A purely semantic lemma, with prefix `s`. Such lemmas are not discussed in
  the paper, but "purely semantic" means that the statement does not mention
  syntactic types, but only their semantic version.

Hence, rule `iT_Path` is a syntactic rule for expression typing (the
subsumption rule), called `T-Path` in the paper, while
`sSub_Sel` is a semantic typing lemma corresponding to `<:-Sel`.

# Directory Layout

* [`theories/Dot`](theories/Dot): guarded DOT. Complete.
* [`theories/`](theories/): General infrastructure.
* [`theories/pure_program_logic`](theories/pure_program_logic): define a "pure"
  variant of Iris's weakest precondition.
* [`theories/iris_extra`](theories/iris_extra): Additional Iris infrastructure.
  - [`dlang.v`](theories/iris_extra/dlang.v): instantiate Iris with the language setup for our proofs
  - [`lty.v`](theories/iris_extra/lty.v): define semantic types (called `lty`
    for logical types), together with language-generic utilities, such as
    substitution and substitution lemmas on them.

Inside the [`Dot`](theories/Dot) folder:
* [`syn`](theories/Dot/syn): syntax
  - [`syn.v`](theories/Dot/syn/syn.v): definition of the basic SYNtax, and instantiate Iris with DOT
    operational semantics.
  - [`syn_lemmas.v`](theories/Dot/syn/syn_lemmas.v): (SYNtactic Lemmas): lemmas about syntax and binding.
  - [`rules.v`](theories/Dot/syn/rules.v): lemmas about this language's operational semantics.
* [`lr`](theories/Dot/lr): logical relation, semantic typing judgment
  - [`dlang_inst.v`](theories/Dot/lr/dlang_inst.v): instantiate shared Iris setup from [`dlang.v`](theories/iris_extra/dlang.v);
  - [`path_wp.v`](theories/Dot/lr/path_wp.v): define path weakest precondition;
  - [`dot_lty.v`](theories/Dot/lr/dot_lty.v): define DOT-specific infrastructure on semantic types (lty), such as semantic types for definitions.
  - [`unary_lr.v`](theories/Dot/lr/unary_lr.v): definition of unary logical relation.
  - [`later_sub_sem.v`](theories/Dot/lr/later_sub_sem.v): define semantics of
    the `Γ1 ≫ ▷ Γ2` judgment.
* [`semtyp_lemmas`](theories/Dot/semtyp_lemmas): semantic typing lemmas:
  - [`binding_lr.v`](theories/Dot/semtyp_lemmas/binding_lr.v): misc typing lemmas,
    requiring additional Coq-level dependencies such as lemmas about binding or operational semantics.
  - [`defs_lr.v`](theories/Dot/semtyp_lemmas/defs_lr.v): DEFinitionS;
  - [`no_binding_lr.v`](theories/Dot/semtyp_lemmas/no_binding_lr.v): various
    typing lemmas, not requiring additional dependencies.
  - [`path_repl_lr.v`](theories/Dot/semtyp_lemmas/path_repl_lr.v):
    PATH REPLacement and pDOT-specific lemmas;
  - [`prims_lr.v`](theories/Dot/semtyp_lemmas/prims_lr.v): PRIMitiveS;
  - [`tdefs_lr.v`](theories/Dot/semtyp_lemmas/defs_lr.v): Type DEFinitionS;
  - [`tsel_lr.v`](theories/Dot/semtyp_lemmas/tsel_lr.v): Type SELections;
* [`stamping`](theories/Dot/stamping): definitions and lemmas about stamping.
* [`typing`](theories/Dot/typing): syntactic typing and auxiliary lemmas about it
  - [`typing_stamping.v`](theories/Dot/typing_stamping.v): prove stamping of typing derivations.
* [`examples`](theories/Dot/examples): various gDOT snippets.
* [`fundamental.v`](theories/Dot/fundamental.v): prove fundamental theorem, adequacy and type safety.

