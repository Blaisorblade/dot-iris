---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

layout: home
---

This is the homepage for the **guarded DOT** project. We extend the
the DOT calculus, that is, the formal foundations of the _Scala_ programming language,
using step-indexed logical relations and the Iris framework; the result is
the *guarded DOT(gDOT)* calculus.

Our first paper, **Scala Step-by-Step**, corresponds to gDOT 1.0.

## Publications
  - _Scala Step-by-Step: Soundness for DOT with Step-Indexed Logical Relations in Iris_.
    Paolo G. Giarrusso, Léo Stefanesco, Amin Timany, Lars Birkedal and Robbert
    Krebbers. ICFP 2020.

    **Abstract**: The metatheory of Scala's core type system---the *Dependent Object Types
    (DOT)* calculus---is hard to extend, like the metatheory of other type systems
    combining subtyping and dependent types. Soundness of important Scala features
    therefore remains an open problem in theory and in practice. To address some
    of these problems, we use a _semantics-first_ approach to develop a logical
    relations model for a new version of DOT, called **guarded DOT (gDOT)**. Our
    logical relations model makes use of an abstract form of *step-indexing*, as
    supported by the Iris framework, to model various forms of recursion in gDOT.
    To demonstrate the expressiveness of gDOT, we show that it handles Scala
    examples that could not be handled by previous versions of DOT, and prove
    using our logical relations model that gDOT provides the desired data
    abstraction. The gDOT type system, its semantic model, its soundness proofs,
    and all examples in the paper have been mechanized in Coq.

    - [Official ACM Version](https://dl.acm.org/doi/10.1145/3408996)
    - [Author Version](gdot-icfp20-1.02.pdf).
    - [Extended Version](gdot-icfp20-w-appendix-1.03.pdf).
      The appendix lists omitted typing rules.
    - [Coq Formalization](https://github.com/Blaisorblade/dot-iris)
    - [coqdoc](coqdoc/).
    - Artifact: [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.3926703.svg)](https://doi.org/10.5281/zenodo.3926703).


## Trivia

- Q: Why "Scala Step-by-Step"?
- A: Because Scala is named after the Italian word for "staircase". And because
  we use _step-indexing_.

## News

- 2020-08-01: Added extended version.
- 2020-08-01: Updated author version (with minor changes from camera-ready).
- 2020-07-05: Added link to artifact on Zenodo
- 2020-07-04: Author version online
- 2020-07-03: Website online
- 2014-06-24: AEC submission accepted.
- 2020-06-19: _Scala Step-by-Step: Soundness for DOT with Step-Indexed Logical
  Relations in Iris_ unconditionally accepted at ICFP 2020.

## Contacts
For any question or suggestion, feel free to contact me, Paolo G. Giarrusso, at
p !dot! giarrusso (at) gmail !dot! com.
