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

The first integration passed combined cloud verification at commit
`f817f1391500e7a12efa90792cd8f901fe5744cd`,
[run 33711286942](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33711286942).
The new `PublishedSection3Source` compiled in 2.9 seconds, all 4403 build jobs
completed, and the existing Section 6 audit/regressions passed. The already
running Section 5 verification also passed (run 33711286974).

The subsequent masked-anchor transport, finite matrix identity, and final
Section 5/6 source-facing endpoints require their own incremental check.
The isolated Section 3 success does not certify those later additions.
Per the user's request, no Lean compilation is run locally. Further integration
uses the Section 6 cloud check and a narrow new-adapter audit, without running
the already verified Section 5 full suite again on this development branch.
