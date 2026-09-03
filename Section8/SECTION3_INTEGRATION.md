# Section 8 uses the concrete Section 3.8 proof

The public Bernoulli and general real-subgaussian Section 8 theorems now
construct their high-band anchor by calling
`ShortRingAnchor.Proposition38.proposition38` in
[`section3/ShortRingAnchor/Proposition38/Assembly.lean`](../section3/ShortRingAnchor/Proposition38/Assembly.lean).
The new adapter is undergoing cloud verification in
[PR #2](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/pull/2),
[run 33715622981](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33715622981).
The older Section 8 and Section 3 certificates do not by themselves certify it.

## Exact public boundary

The Bernoulli endpoints take `RademacherSection3UpstreamInputs`; the general
endpoints take `SubgaussianSection8.Section3UpstreamInputs A`. Both specialize
`BernoulliSection8.Section3Bridge.UpstreamInputs`, containing:

- Proposition 3.2 for the fixed real atom and each fixed complex shift;
- Cook (2018) Theorem 1.12 with its norm guard;
- canonical BBV comparisons for the literal ring and dense Gaussian models;
- named BC12 negative-moment tightness for the actual Ginibre array;
- finite Ginibre projection and correlation formulas.

The comparison constant is shared across dimensions. The positive
negative-moment exponent is chosen for each dimension sequence and fixed shift.
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
| `BernoulliSection8/Section3Integration.lean` | Invoke Proposition 3.8 and transfer its probability limit to the original real IID sequence. |
| `../SubgaussianSection8/Section3Integration.lean` | Instantiate the adapter at the general Section 8 atom. |

Both ring constructions use the existing `squareIIDFromSequence` coordinates,
dimension `N=(s+3)W`, and coefficient `1/sqrt(3W)`.

## Dependencies and verification

The root Lake project resolves `ShortRingAnchor` and `Vendor` directly from
`section3/`; the older `vendor/short-ring-analysis` snapshot is retained for
provenance. The standalone Section 3 package and workflow remain available.

Cloud verification selects `SubgaussianSection8` and `BernoulliSection8`:
420 project modules, zero Section 4 modules. It reuses available artifacts,
serializes a cold import closure, and runs both normal explicit Lake targets.
When the integration cache is available, only the six bridge/endpoint entry
points receive separate serial commands; Lake still validates their imports
and the two complete Section 8 targets normally.
No local Lean compilation or whole-repository build is used.

The gate includes the existing 13-report general and 28-report Bernoulli audits,
a new 15-report integration audit, and both public-signature audits. The new
audit includes Proposition 3.8 and the four final Section 8 endpoints. Only
`propext`, `Classical.choice`, and `Quot.sound` are allowed.
