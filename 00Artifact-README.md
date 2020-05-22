# Type Soundness for DOT via logical relations

Mechanization accompanying the paper "Scala Step-by-Step: Soundness for
DOT with Step-Indexed Logical Relations in Iris".

This README is specific to our artifact submission.

## Tarballs

We provide a tarball with:
- this source code;
- generated HTML in `golden-html` - start browsing from
  [`golden-html/coqdoc/index.html`](golden-html/coqdoc/index.html);
- a slightly updated version of the paper, in
  [`gdot-icfp20-artifact-eval-icfp20.pdf`](gdot-icfp20-artifact-eval-icfp20.pdf),
  matching some changes to the formalization in the artifact.

Proceed browsing with [`README.md`](README.md).

## Virtual machine

SSH into the virtual machine per standard instructions, as user `artifact`; the
sources are in `~/dot-iris`, as a checkout of the branch `aec-artifact-cleanup`. 

We have already compiled them with `make html`, and saved the generated HTML as
`golden-html`.
