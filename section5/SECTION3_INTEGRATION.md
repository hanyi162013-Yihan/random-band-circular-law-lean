# Direct integration of the checked Section 3 package

The Section 6 development branch reuses the exact `section3/` source tree
from main commit `42c26b672faec82a8ea7999a9cd0778c31618495`.
All 230 Lean files are byte-identical to the proof-source checkpoint
`79798346f1cc9dda9cfd0c5bf2c3044aea5162a9`, verified by
[Section 3 run 33702782802](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33702782802).
The 257 imported files were copied from an existing local publication and
checked against GitHub blob hashes. No toolchain or dependency cache was downloaded.

The root Lake project now owns `ShortRingAnchor` and its `Vendor` dependencies
from `section3/`. The older `vendor/short-ring-analysis` snapshot is preserved
for historical provenance, but is not the active library. There is exactly
one owner of each imported Lean module.

The new adapter calls the actual published Proposition 3.6 theorems. Their
least-singular-value and counting conclusions are proved internally, not
passed again as assumptions. The planar branch retains BBV and the two BC12
inputs. The real-density branch additionally retains the published geometric
Brascamp--Lieb premise. These are ordinary hypotheses, not new axioms.

The existing broad Section 5 interfaces remain available for other source
models. A direct published-theorem interface must not be confused with an
unconditional circular law or with a theorem for arbitrary size-dependent
atom laws: the published Section 3 endpoint uses fixed atom laws.

Integration status: source alignment is checked; the new adapters and the
combined Section 3/4/5/6 dependency graph require their own cloud verification.
The earlier isolated Section 3 success does not certify this new integration.
Per the user's request, no Lean compilation is run locally.
