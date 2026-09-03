# Section 8 uses the concrete Section 3.8 proof

The public Bernoulli and general real-subgaussian Section 8 theorems now
construct their high-band anchor by calling
`ShortRingAnchor.Proposition38.proposition38_withoutBC12` in
[`section3/ShortRingAnchor/Proposition38/VerifiedGinibre.lean`](../section3/ShortRingAnchor/Proposition38/VerifiedGinibre.lean).
The former negative-moment, projection and correlation fields are removed
from the public upstream structure. No Gaussian-law field replaces them:
the law of the existing explicit reference array is proved internally.
**BC12-free migration: PASS.** Proof-source commit
`8d9dbc26f820f7056b37108c980501cecb951203` passed
[cloud run 33812017163](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33812017163)
on 2026-09-03 at 22:16:54 UTC. Both normal Section 8 targets, all 61 exact
axiom reports and both compiled public-signature audits passed.
The scoped build took 36 seconds and the audit step 13 seconds after setup.
The report artifact SHA-256 is
`9e989af6583e77f3cb4d17b39f9f16aff5cd117c63be470abd0aae96f8956d5c`.
This is a Section 8 certificate, not a certificate for the subsequent
Section 5/6/10 migration.
The later extraction of Gaussian normalization into a shared Section 3 lemma
is awaiting its own cloud check and increases the audit count to 62.

**Historical conditional integration:** proof-source commit `b6c379836fcc6cf166881768d1a0ad6782c5c552`
passed [cloud run 33720016599](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33720016599/job/100537065421)
on 2026-09-03. [PR #2](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/pull/2)
integrates it into the root project. The [audit excerpt](SECTION3_CLOUD_AUDIT.txt)
records the normal target builds and all 56 strict axiom reports.

## Exact public boundary

The Bernoulli endpoints take `RademacherSection3UpstreamInputs`; the general
endpoints take `SubgaussianSection8.Section3UpstreamInputs A`. Both specialize
`BernoulliSection8.Section3Bridge.UpstreamInputs`, containing:

- Proposition 3.2 for the fixed real atom and each fixed complex shift;
- Cook (2018) Theorem 1.12 with its norm guard;
- canonical BBV comparisons for the literal ring and dense Gaussian models.

The comparison constant is shared across dimensions. The negative-moment
exponent `1/128` is constructed inside the proved Section 3 endpoint.
The Section 8 square-deformation Cook and Nguyen inputs remain separate, with
their existing quantitative ranges. No density, symmetry or support restriction
is added to the atom. Gaussian moments, IID laws and matrix identities are
proved here; they are not additional public assumptions.

The old `Section3SubgaussianHighBandInput` / `Section3Input` remains an internal
interface in the pressure proof. `Section3Bridge.highBandInput` constructs it
from the concrete Section 3.8 theorem. Public endpoints no longer require
callers to supply the high-band log-potential conclusion.

## Proof map

| File | Role |
| --- | --- |
| `BernoulliSection8/Section3Gaussian.lean` | Prove the Gaussian pair's mean, second moment and finite third moment. |
| `BernoulliSection8/Section3Model.lean` | Construct IID arrays; identify cyclic successors, coefficients, ring matrices and the actual Gaussian reference. |
| `BernoulliSection8/Section3GaussianLaw.lean` | Prove the normalized real-pair entry law, independent-entry matrix law, and equality with the Section 3 Gaussian-column model. |
| `BernoulliSection8/Section3Integration.lean` | Specialize BBV through separate model-conversion lemmas, invoke Proposition 3.8, and transfer its probability limit to the original real IID sequence. |
| `../SubgaussianSection8/Section3Integration.lean` | Instantiate the adapter at the general Section 8 atom. |

Both ring constructions use the existing `squareIIDFromSequence` coordinates,
dimension `N=(s+3)W`, and coefficient `1/sqrt(3W)`.

## Dependencies and verification

The root Lake project resolves `ShortRingAnchor` and `Vendor` directly from
`section3/`; the older `vendor/short-ring-analysis` snapshot is retained for
provenance. The standalone Section 3 package and workflow remain available.

Cloud verification selects `SubgaussianSection8` and `BernoulliSection8`,
with zero Section 4 modules. It reuses available artifacts, serializes a
cold import closure including the pinned Ginibre proof dependency, and runs
both normal explicit Lake targets.
When the integration cache is available, only the seven bridge/endpoint entry
points receive separate serial commands; Lake still validates their imports
and the two complete Section 8 targets normally.
No local Lean compilation or whole-repository build is used.

The gate includes the existing 13-report general and 28-report Bernoulli audits,
a 21-report integration audit, and both public-signature audits. The new
audit includes the BC12-free Proposition 3.8, the Gaussian-law constructors,
the shared normalization lemma, and the four final Section 8 endpoints. A source regression check requires
exactly the five upstream fields (one comparison constant and four theorem
premises), and rejects returning the former BC12 fields. Only
`propext`, `Classical.choice`, and `Quot.sound` are allowed.

The historical conditional integration passed all gates, including scans of 59 Bernoulli and 35 general Section 8
Lean files and both compiled public-signature audits. The final run restored
the integration cache and completed the normal
`lake build SubgaussianSection8 BernoulliSection8` target.

The adapter uses the default heartbeat and recursion-depth limits, with no
reducibility override. The model conversions are separate proved lemmas;
the final bridge module compiled in 2.9 seconds. Documentation-only commits
after the proof-source commit do not alter its Lean sources or build configuration.
