(** * Type soundness for Dependent Object Types.

We are modeling multiple languages of the D* family, including (variants of)
both D<:> and DOT, and higher-kinded variants of both.
Our modifications are significant, and we will motivate them in upcoming work.

BEWARE: This document is currently unfinished and not in sync with the development.
*)

(** * Preliminaries. *)
(** ** Saved semantic pretypes.
We extend Iris with dependently-typed saved predicates,
to store in ghost state mappings from gnames (ghost names)
to saved predicates (that function as semantic (pre)types. *)
From D Require saved_interp_dep.

(** ** Language interface.
A language must supply
- an operational semantics, defined using Iris interfaces
- support substituting values for variables throughout its syntax,
through an extension of the Autosubst 1 interface.

Autosubst 1 is based on infinite substitutions, but we extend it with
some support for:
- finite substitutions;
- closed syntax.
*)

From D Require asubst_intf asubst_base.

(** ** Stamping *)
(** Objects contain IDs (called stamps) pointing to semantic types; as a sanity check, we prove that stamps cannot affect execution. *)
From D.Dot Require skeleton.

(**
In actual DOT programs, object contain syntactic types, but we assume
those programs are elaborated to programs containing stamps, together
with a map from stamps to syntactic types.
We formalize (part of) the translation process, externally to Iris.
Typing derivations then are defined relative to a stamp-type mapping,
which we call a stamp table.
*)
From D.Dot Require typeExtractionSyn typing_stamped.

(**
Semantic typing does not depend on a map from stamps to syntactic types
(or on the existence of syntactic types at all).
Instead, it depends on a map from stamps to semantic types, stored
in Iris ghost state.

For technical reason, this mapping is implemented through *two* mappings:
- A first map translates stamps (allocated ahead-of-time) to gnames
(picked by the Iris gname allocator).
- A second map [saved_interp_dep] translates gnames to saved predicates.

Entries in both mappings are immutable after allocation.

We prove that a stamp table (stamp-syntactic type mapping) can be translated
to such a 2-layer stamp-semantic type mapping, by induction
on the stamp table. *)

From D Require gen_iheap dlang.
From D.Dot Require typeExtractionSem.

(**
For each language, we (will) prove typing lemmas purely semantically.
*)

From D.Dot Require lr_lemmas (* ... *).

(**
Finally, we prove the fundamental lemma: syntactially well-typed terms are
semantically well-typed, and similarly for subtyping, etc.
And by adequacy, semantically well-typed terms are safe.
*)
From D.Dot Require fundamental.
