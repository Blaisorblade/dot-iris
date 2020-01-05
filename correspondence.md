# Correspondence between paper and Coq dev

- gDOT syntax and operational semantics are defined in `theories/Dot/syn/syn.v`.
- Unstamped typing is defined in `theories/Dot/typing/typing_unstamped.v`.
- Stamped typing is defined in `theories/Dot/typing/typing_stamped.v`.

- Derived rule `(<:-Later-Shift)` is called `Sub_later_shift` in Coq.

## Differences between our paper (and technical appendix) and our Coq development.

- Unlike in the appendix, our saved predicates support an additional argument
  `args : vec n vl` for some `n`. We always set `n = 0` to ignore this, but our
  implementation has additional flexibility.

- Compared to the paper, and even to the appendix, we describe (in
  `theories/Dot/typing/typing.v`) an additional "storeless" typing judgment, a
  strict generalization of stamped typing.
  Storeless typing generalizes some rules of stamped typing to allow arbitrary
  values in paths, and not just variables. This is not at all necessary to our
  proof technique, but it simply allows typing more programs.
