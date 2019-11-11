Differences between our paper (and technical appendix) and our Coq development.

- Unlike in the appendix, our saved predicates support an additional argument
  `args : vec n vl` for some `n`. We always set `n = 0` to ignore this, but our
  implementation has additional flexibility.
