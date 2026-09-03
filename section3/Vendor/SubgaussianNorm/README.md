# Reused subgaussian operator-norm proof

Source: the same author's published
[`Section9/BernoulliSection9/SubgaussianOperatorNorm.lean`](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/blob/42c26b672faec82a8ea7999a9cd0778c31618495/Section9/BernoulliSection9/SubgaussianOperatorNorm.lean).
Original source SHA-256:
`8de1f4ff8fcb53889ef4d7fa2f0ae9b0c2fa12d8e20fc999d5db72239caf1978`.
The local source was compared byte-for-byte with GitHub before adaptation.

`OperatorNorm.lean` changes only the namespace, import path, and provenance
comment. `Data.lean` extracts the IID model definitions, square restriction,
and raw matrix from the source `ExternalInputs.lean`. **No Cook or Nguyen
estimate is copied or assumed.** Both files use the enclosing project's MIT
license and the same Lean 4.33.0/mathlib pin.

The proof constructs a finite sphere net, proves bilinear subgaussian tails,
takes a union bound, and passes from real to complex operator norms. It
proves failure at most `exp(-W)` above `40 sqrt(c+1) sqrt(W)`, together with
measurable normalized bad events. This is used in Proposition 3.8 only when
the number of blocks is bounded; a sum-of-block-norms bound is sufficient.

Local adaptations are recompiled and audited in
`ShortRingAnchor/Proposition38/Audit.lean`. The source's existing GitHub
verification is provenance, not a substitute for checking these adaptations.
