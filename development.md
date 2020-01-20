## Development Instructions

### Additional developments, not used in the paper
Inside the `Dot` folder:
* `misc_unused`: misc stuff, not used elsewhere or relevant to the paper.

* `theories/DSub`: guarded D<:, incomplete, used for prototyping.
* `theories/DSubSyn`: guarded D<:, where type members are represented by
  storing syntactic types in values, and interpreting them recursively. Used for
  prototyping but mostly complete. Shares code from `theories/DSub`.

### Bumping Iris

Find the version name on top of
https://gitlab.mpi-sws.org/iris/opam/commits/master/packages/coq-iris, then
modify `opam`, *commit*, and reinstall with `opam install .`
