All file paths in this file are relative to the [`theories/`](theories/) folder.

# Correspondence between paper and Coq dev

## Differences between our paper (and technical appendix) and our Coq development

There are a number of small differences between the paper presentation
of gDOT and the formalization in Coq. We briefly discuss them here.

- Notations such as `\overbar{D}⟦ T ⟧` in the paper are translated to
  notations such as `Ds⟦ T ⟧` in Coq.

- In terms, "coerce" is written "skip".

- In Coq, definition lists are represented using Coq's `list`
  data type, whereas singleton and merge operations are used in the paper
  (Fig. 3). Our approach in Coq is influenced by the Coq development of pDOT by
  Rapoport et al.

- While in the paper unstamped and stamped DOT are represented using disjoint
  syntaxes, in Coq there is a single syntax, together with predicates
  `is_unstamped_?` and `is_stamped_?`, characterizing whether some AST is
  unstamped or stamped.

- Unlike in the paper, our saved predicates and semantic types support an
  additional argument `args` of type `vec n vl`, where `n` is the _arity_ of the
  semantic type. This additional argument is useful to provide forwards
  compatibility with higher-kinds. gDOT only uses predicates of arity `n = 0`, which
  are equivalent to the predicates used on paper.

- In the paper, the typing rule and semantics for type `{ A >: L <: U }` uses
  `▷` in front of `L` and `U`.
  Our Coq development is slightly more general and has no such implicit later
  in the rules and semantics for the corresponding connective, called
  `TTMem`. Hence, `{ A >: L <: U }` is encoded as `TTMem "A" (TLater L)
  (TLater U)`. We define an abbreviation `TTMemL`, allowing to write the type
  in question as `TTMemL "A" L U`. However, the restrictions on type members
  described in the paper still arise due to rule `iD_Typ_Abs` in
  [`Dot/typing/typing.v`](theories/Dot/typing/typing.v).

- Our mechanization extends gDOT with some primitives, such as booleans and
  naturals, with some associated operations, even though all of those primitives
  are encodable.

- We inherit various superficial differences between the on-paper presentation
  of Iris and the actual implementation.
  For instance, in Coq `iProp` is parameterized by an additional index `Σ`.
  We hope such matters are not distracting, and refer to
  https://gitlab.mpi-sws.org/iris/iris/-/tree/master/#further-resources
  for further information.

### Legacy typing judgments in examples

- For legacy reasons, syntactically well-typed examples are written in "old"
  unstamped typing, defined in
  [`Dot/examples/old_typing/old_subtyping.v`](theories/Dot/examples/old_typing/old_subtyping.v) and
  [`Dot/examples/old_typing/old_unstamped_typing.v`](theories/Dot/examples/old_typing/old_unstamped_typing.v).
  This typing judgment can be translated to our new judgment;
  [`Dot/examples/old_typing/old_unstamped_typing_to_typing.v`](theories/Dot/examples/old_typing/old_unstamped_typing_to_typing.v).
  The main difference is in the handling of delays and later: subtyping has two
  indexes instead of one.

- As an aid to proof automation for syntactically ill-typed examples, we also
  define and prove type safe a more liberal variant of the "old" typing
  judgment in
  [`Dot/examples/sem/storeless_typing.v`](theories/Dot/examples/sem/storeless_typing.v).
  This is not at all necessary to our proof technique, it just enables some
  simple automation.

### Semantic types

The Coq presentation of our logical relation and semantic typing judgments is
more general than on paper (Fig. 9), which inlines together several separate
definitions.

- On paper, the value interpretation `V⟦ T ⟧` maps syntactic types `Type` to
  semantic types, defined as environment-indexed persistent predicates over
  values, of type `Env → Val → iProp`.
  Instead, in Coq, semantic types are a first-class notion, described by Coq
  type `olty Σ 0`, defined in `iris_extra/lty.v`.

  - Most of Fig. 9 is defined as combinators on semantic types,
    without reference to syntactic types. The Coq notation `V⟦ T ⟧` translates
    syntactic types into semantic types using those combinators.
  - Paper notations `E⟦ T ⟧`, `G⟦ T ⟧` and semantic typing judgments `Γ ⊨ ...`
    come in Coq with counterparts on semantic types, written respectively
    `sE⟦ T ⟧`, `sG⟦ T ⟧` and `Γ s⊨ ...`.

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
theorem, and the definition of the language with its operational semantics and
type system. In more detail:

Sec. 2:
- Syntax, substitution and operational semantics for unstamped and stamped
  gDOT (Fig. 3, Sec. 5.1):
  [`Dot/syn/syn.v`](theories/Dot/syn/syn.v).
  - values, expressions, paths, definition bodies and lists, types are called
    respectively `vl`, `tm`, `path`, `dm`, `dms`, `ty`; see comments for the
    Coq syntax for each constructor;
  - member selection: `objLookup`;
  - evaluation contexts: `list ectx_item`.
  - Operational semantics:
    - head-reduction: `head_step`; reduction: `prim_step`.

Sec. 4:
- gDOT typing judgments (Sec. 4, Fig. 6, 7):
  - The `Γ1 ≫ ▷ Γ2` judgment (called `ctx_strip_syn`), and auxiliary
    judgments for primitive types:
    [`Dot/typing/typing_aux_defs.v`](theories/Dot/typing/typing_aux_defs.v)
  - Path substitution and replacement:
    [`Dot/syn/path_repl.v`](theories/Dot/syn/path_repl.v)
  - Primitive and derived typing rules:
    - Subtyping and path typing:
      [`Dot/typing/subtyping.v`](theories/Dot/typing/subtyping.v)
    - Definition, definition list and term typing:
      [`Dot/typing/typing.v`](theories/Dot/typing/typing.v)

Sec. 5:
- Safety (Def. 5.1) is defined as `safe` in
  [`iris_extra/det_reduction.v`](theories/iris_extra/det_reduction.v).
- Type soundness for gDOT is proven in
  [`Dot/fundamental.v`](theories/Dot/fundamental.v) as
  `Theorem type_soundness`.

Sec. 6:
- Examples are written using higher-level notations than the one defined in `syn.v`:
  - `Module DBNotation` is defined in
    [`Dot/examples/ex_utils.v`](theories/Dot/examples/ex_utils.v); it is merely
    an alternative Unicode notation for deBruijn terms.
  - `Module hoasNotation` is defined in
    [`Dot/examples/hoas.v`](theories/Dot/examples/hoas.v); it defines an HOAS
    frontend for writing concrete terms.

- Syntactically well-typed examples are in [`Dot/examples/syn/`](theories/Dot/examples/syn/).
  In particular:
  - Motivating example (Fig. 2, discussed in Sec. 1.1 and 4.0):
    [`Dot/examples/syn/from_pdot_mutual_rec.v`](theories/Dot/examples/syn/from_pdot_mutual_rec.v).
  - Covariant lists example (Fig. 10, Sec. 6.1): [`Dot/examples/syn/list.v`](theories/Dot/examples/syn/list.v).
- Those examples are written using old unstamped typing, the translation to
  typing is proved by `Theorem renew_typed` in
  [`Dot/examples/old_typing/old_unstamped_typing_to_typing.v`](theories/Dot/examples/old_typing/old_unstamped_typing_to_typing.v).

- Semantically safe examples are in [`Dot/examples/sem/`](theories/Dot/examples/sem/).
  - Positive integers example (Fig. 11, Sec. 6.2): [`Dot/examples/positive_div.v`](theories/Dot/examples/sem/positive_div.v).
  - Unsafe motivating example (Fig. 12, Sec. 6.3): [`Dot/examples/from_pdot_mutual_rec_sem.v`](theories/Dot/examples/sem/from_pdot_mutual_rec_sem.v).

Sec. 7:
- For the (updated) code sizes, see [`codesize.md`](codesize.md).
- Testcase [`tests/test_used_axioms.v`](tests/test_used_axioms.v) confirms that the only axioms we use are functional extensionality and proof irrelevance.

### Proofs

The proof strategy we describe in the paper is implemented in the following files.

Sec. 5:
- Iris connectives (Sec. 5.2) are predefined by Iris, except for `s ↝ φ`,
  defined in [`iris_extra/dlang.v`](theories/iris_extra/dlang.v) as
  `s ↝n[ n ] φ` (where `n` is the arity of semantic predicate `φ`).
- Iris proof rules (Sec. 5.2, Fig. 8): Iris proves all rules shown, except the
  following ones, which are proved by unsealing Iris's model:
  - `Impl-▷` is proven in from [`iris_extra/swap_later_impl.v`](theories/iris_extra/swap_later_impl.v).
  - `Saved-Pred-Agree` is proven as
  `saved_ho_sem_type_agree` from [`iris_extra/saved_interp_dep.v`](theories/iris_extra/saved_interp_dep.v).
- Term weakest precondition (Sec. 5.2.1): Definition and proof rules appear in
  [`pure_program_logic`](theories/pure_program_logic).
- Path weakest precondition (Sec. 5.2.2): defined in [`Dot/lr/path_wp.v`](theories/Dot/lr/path_wp.v).
- Logical relation (Sec. 5, Fig. 9):
  - Auxiliary definitions appear in [`iris_extra/dlang.v`](theories/iris_extra/dlang.v).
  - Syntactic auxiliary definitions appear in [`Dot/syn/lr_syn_aux.v`](theories/Dot/syn/lr_syn_aux.v).
  - Infrastructure on semantic predicates
    is defined in [`Dot/lr/lty.v`](theories/Dot/lr/lty.v) and [`Dot/lr/dot_lty.v`](theories/Dot/lr/dot_lty.v).
  - The logical relation `V⟦ T ⟧` and semantic judgments `Γ ⊨ ...` are completed
    in [`Dot/unary_lr.v`](theories/Dot/unary_lr.v), including adequacy (Thm. 5.5).
- Actual semantic typing lemmas appear in [`Dot/semtyp_lemmas`](theories/Dot/semtyp_lemmas/).
  The most interesting ones are:
  - `sT_Obj_I` (for object construction, using Löb induction);
  - `sD_Typ_Abs`,  `sStp_Sel`, `sSel_Stp`, `sTyp_Stp_Typ` (about type members).
- The unstamped semantic typing judgment is defined in
  [`Dot/lr/sem_unstamped_typing.v`](theories/Dot/lr/sem_unstamped_typing.v),
  which also lifts semantic typing lemmas to use it.

- The fundamental theorem (Thm. 5.4) is proven in [`Dot/fundamental.v`](theories/Dot/fundamental.v).

## Typing lemma naming conventions

Names of typing rules and lemmas can be derived mechanically from those in
the paper, with a couple of exceptions, listed in the following table.

Translation table of symbols in names:
| Paper   | Coq    |
| :-----: | :----: |
| `-`     | `_`    |
| `<:`    | `Stp`  |
| `∀`     | `All`  |
| `{}`    | `Obj`  |

- Exceptions:
  - The paper's D-And is here replaced by `D_Nil` and `D_Cons` because definition
    lists are represented as lists (see above section on differences with the
    paper).

- The names of all typing rules, but not of subtyping rules, have a prefix
  that identifies the judgment:

| Prefix | Typing Judgment |
| :----: | :-------------- |
| `T`    | Term            |
| `P`    | Path            |
| `D`    | Definition      |

- The names of subtyping rules contain `<:` or `Stp`, and the name of the
  type constructor that the rule is about. The order relates to the shape of the rule. For
  instance rule `<:-μ` will conclude that type `T <: μ x. T`, while
  rule `μ-<:` will conclude that some type `μ x. T <: T`, assuming certain
  premises.

For each typing rule (say, `T_All_E_p`), there can be multiple versions,
distinguished by corresponding prefixes; not all rules need exist in all
versions.
- Prefix `i` (for inductive) is used for syntactic typing rules, such as
  `iT_All_E_p`. Some rules appear in multiple inductive types, and are only
  distinguished through the name of the defining module.
- Prefix `u` is used for semantic typing lemmas about the _unstamped_ typing
  judgments, such as `uT_All_E_p`.
- No prefix is used for semantic lemmas for the _stamped_ semantic typing
  judgment, such as `T_All_E_p`.
- Prefix `s` is used for purely _semantic_ lemmas (such as `sT_All_E_p`),
  and can be combined with the already described prefix `u` for purely
  semantic lemmas about _unstamped_ typing (such as `suT_All_E_p`). Such
  lemmas are not discussed in the paper, but "purely semantic" means that the
  statement does not mention syntactic types, but only their semantic
  version; these lemmas are more generally applicable.

Hence, rule `iT_All_E_p` is a syntactic rule for expression typing (the
dependent function application rule), called `T-∀-E_p` in the paper, while
`sStp_Sel` is a semantic typing lemma corresponding to `<:-Sel`.

For some rules (such as `T-Path`), we only state the purely semantic typing
lemmas (such as `sT_Path` and `suT_Path`).

Legacy typing judgments use the same conventions, except that they use `Sub`
instead of `Stp` for the old-style subtyping judgment, with two indexes.
Sometimes, the old-style subtyping judgment is called "indexed" and the new
one is called "delayed".

# Directory Layout

* [`theories/Dot`](theories/Dot): guarded DOT.
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
  - [`defs_lr.v`](theories/Dot/semtyp_lemmas/defs_lr.v): definition typing;
  - [`sub_lr.v`](theories/Dot/semtyp_lemmas/sub_lr.v): subtyping;
  - [`path_repl_lr.v`](theories/Dot/semtyp_lemmas/path_repl_lr.v): lemmas about
    path replacement and path typing;
  - [`prims_lr.v`](theories/Dot/semtyp_lemmas/prims_lr.v): typing lemmas about
    primitive operations;
  - [`examples_lr.v`](theories/Dot/semtyp_lemmas/examples_lr.v): other lemmas,
    only needed for examples
* [`typing`](theories/Dot/typing): syntactic typing and auxiliary lemmas about it
* [`fundamental.v`](theories/Dot/fundamental.v): prove fundamental theorem, adequacy and type safety.
* [`examples`](theories/Dot/examples): various gDOT examples, including ones in
  the paper, together with legacy code they use (from earlier versions of our
  approach).

