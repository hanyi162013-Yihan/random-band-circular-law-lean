# Direct integration of the checked Section 3 package

## Gaussian-source migration checkpoint — verified 2026-09-03

The current concrete endpoints no longer take `BC12GinibreInput`.
`CircularLawSections56.Section5.VerifiedGinibreSources` identifies the actual
reference with Section 3's Gaussian law and constructs its log limit and
negative-moment tightness (the latter from BBV). The additional taper adapter
constructs nonsingularity, negative moments, log limits and row moments;
its remaining analytic fields concern only the taper matrix.
See [the cross-chapter status](../GAUSSIAN_INPUT_MIGRATION.md).
These changes passed the Section 5 job of
[run 33815655602](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33815655602/job/100847217827)
at `c4e807877fefef8339a6ff01ec4ed75bc08ded81`: normal public-target build,
224 existing and 16 migration axiom reports, plus the printed signatures.
`TaperVerifiedGinibre` compiled in 2.6 seconds. Only the three standard
foundations were reported. Artifact SHA-256:
`e3a359ff3097b43f179e67cbd61bcf2afbbacb85e2001ce403c365595f6744ac`.
The whole run had a separate root audit-import failure; this is a Section 5
certificate, not a claim that every matrix job of that run succeeded.

**Later source-record migration also passed at `d7d732c`:**
`PublishedSection3Model.Sources` now replaces its old Gaussian conclusion
fields by the exact normalized Ginibre law, with dense BBV available at all
positive heights. The negative moment and full-log limit are proved methods,
and the concrete source constructor proves the Gaussian law internally.
The later check covers the normal public target, 1109 axiom reports and six
module kernel replays. See [the exact certificate](../GAUSSIAN_MIGRATION_VERIFICATION.md).

## Historical concrete interface — verified 2026-09-03

The actual fixed-law short-ring/calibration construction and both real/complex
Section 5 endpoints passed [run 33725000131](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33725000131)
at `c992bff30e9af6ddabcba04f113447cd48c27f20`, including the transitive audit
of all 93 new concrete Section 5 declarations. No finite model, sampling or
anchor certificate remains in those endpoint inputs. See
[CONCRETE_SECTION3_INTERFACE.md](CONCRETE_SECTION3_INTERFACE.md) for the exact
fixed-atom/uniform-profile scope and retained Section 4/literature assumptions.
The shared density definition is already corrected on main; this publication
does not modify Section 3 or any unrelated chapter/library configuration.

## Historical source-facing integration

**2026-09-03 integration correction:** the historical exact-copy statements
below describe the initial import. The current development branch corrects
Section 3's auto-implicit `top` density-bound field to explicit ENNReal top,
with the user's approval. See `../section3/INTEGRATION_CORRECTIONS.md`.
The previous green conditional proof did not test whether this density
premise was inhabitable; the new actual Gaussian constructor does. Fresh
cloud verification of the corrected dependency passed in the targeted
[Section 6 run 33719510129](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33719510129).
This checks the new source-facing calls and their actual dependencies, not a
fresh independent full Section 5 suite. Finite short-ring/calibration model
and sampling data remain explicit inputs; their complete automatic
instantiation at the concrete final entrance is not yet claimed.

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

The subsequent masked-anchor transport, finite matrix/normalization identities,
iid sampling adapter, and final Section 5/6 source-facing endpoints passed
[combined run 33714847892](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33714847892)
at commit `5301196f97a7de515d3602df4dc6a20924296f95`.
All 122 Section 6 modules and 119 regressions passed. The narrow integration
audit checked 126 new adapter declarations and their transitive foundations.
This verifies the actual published theorem calls, not merely the imports.
Finite source model/sampling identities and literature premises remain visible.
Per the user's request, no Lean compilation is run locally. Further integration
uses the Section 6 cloud check and a narrow new-adapter audit, without running
the already verified Section 5 full suite again on this development branch.
