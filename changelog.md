This file lists few significant changes to the dot-iris repository.

More details can be found by browsing merged pull requests tagged as "major":
https://github.com/Blaisorblade/dot-iris/pulls?q=is%3Apr+is%3Amerged+label%3Amajor

# master (Not yet released)

- Prepend basic update modality to all judgments:
https://github.com/Blaisorblade/dot-iris/pull/303

This enables updating ghost state to establish typing judgments;
in our setting, that means only extending ghost state, since we ensure all our
judgments are persistent.

- Support for sound type projections, in the style of Scala 2:
https://github.com/Blaisorblade/dot-iris/pull/250
https://github.com/Blaisorblade/dot-iris/pull/304

- (Preliminary) support for higher-kinded types in the semantics (too many PRs to count):
  in short, semantic kinds are modeled as predicates on semantic types, and type
  constructors as functions from values to types.

# v1.0

Release accompanying the ICFP'20 paper.

# v0.5 / submit-icfp20-aec-revised

Revised AEC submission for ICFP'20, with significant changes to the theory.

Among other things, this revamped the shape of the subtyping judgment and
replaced the old syntactic stamping with a semantic version (saving lots of
code). The old typing rules are still syntactically admissible, and are used in
examples.

# v0.2 / submit-icfp20-aec

AEC submission for ICFP'20; lots of code cleanups.

# v0.1.1 submit-icfp20-anon

Minor updates for submission (anonymizing code, trim experiments, etc.).

# v0.1 / submit-icfp20

Release accompanying the original ICFP'20 submission.
