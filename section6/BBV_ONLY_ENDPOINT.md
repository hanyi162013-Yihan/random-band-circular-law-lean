# Verified BBV-only Ginibre and concrete profile endpoint

## Preferred endpoint: no caller-supplied pressure estimates

`NoncompactProfile.gaussian_profile_circular_law_of_bbv`, in
`CircularLawSection6/VerifiedCorePressure.lean`, constructs both compact-core
pressure estimates from the proved Section 4/5 theorems. Only uniform BBV and
the model's profile/bandwidth assumptions remain. The real-density Section 5
and taper routes are not premises of this Gaussian endpoint.

At `0b33ba4`, the ordinary build, all 841 axiom reports, three regression files
and seventeen module kernel replays passed
[run 33831340031](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33831340031).
See [the exact certificate](../PRESSURE_INPUT_MIGRATION.md).

## Preserved earlier source API

**Current migration verified:** both `GaussianProfileBBVSources` and
`GaussianProfileBBVCoreSources` now have exactly the two fields below.
The core route uses the shared proved Section 5 Gaussian reference; the
independent BBV-only derivation remains available. The finite-formula and
log-potential records also have proved constructors with no premise.
The legacy concrete/reduced routes still expose the separate classical
squared-singular-law input, but no longer expose BC12, raw-log, negative
moment or spectral-limit fields. See
[the cross-chapter status](../GAUSSIAN_INPUT_MIGRATION.md) and
[completed verification](../GAUSSIAN_MIGRATION_VERIFICATION.md).

The earlier independent BBV-only chain passed
[run 33740349647](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33740349647)
at `9d98ca87d112a240fc5b596d1a27801450b15cbe` on
`codex/section6-formalization`, tree `9007110012caebaf30a10e2d1a3cc30efb44fe9b`.

## Earlier result and exact source-record fields

`NoncompactProfile.gaussian_profile_circular_law_of_bbv_sources`, in
`CircularLawSection6/BBVOnlyProfileEndpoint.lean`, proves convergence in
probability of the actual normalized Gaussian cyclic profile matrices
against every continuous compactly supported real test, to `circularMeasure`.
The profile is strictly positive, continuous, integrable, of bounded
variation and integral one. The bandwidth is positive and tends to infinity;
no limit of bandwidth divided by dimension is assumed.

`GaussianProfileBBVSources` has exactly two fields:

| Field | Retained mathematical input |
| --- | --- |
| `bbv` | Uniform published BBV comparison from the existing concrete Section 3 interface |
| `coreSection4` | Two finite quantitative Section 4 pressure estimates for each compact core |

These are explicit hypotheses of this older API. The preferred endpoint above
supplies `coreSection4` using `CoreRadiusBounds.verifiedConcreteSection4Input`;
the record itself is preserved for compatibility. The BBV literature theorem
is not reproved. The axiom audit does
not turn hypotheses into theorems. There is no Han, BC12, separate Ginibre
raw-log/spectral, or limiting squared-singular-test field in this bundle.
Section 3 model, sample, density and anchor constructions use repository-root
`section3/` via Section 5, not an alternative nested checkout.

## Ginibre proof without eigenvalue correlation formulas

`ginibreLogPotential_of_bbv` proves the original `GinibreLogPotentialInput`
for every fixed complex shift and every growing positive dimension sequence
on the actual common Gaussian array. The finite cyclic version is also proved.

1. The actual Gaussian law and root Section 3 small-ball estimate give
   every-shift nonsingularity. BBV gives tight negative moments at `1/128`
   and fixed-height Stieltjes limits.
2. The scalar Dyson equation identifies its imaginary-axis solution and
   logarithmic primitive. Its zero-height endpoint is the circular potential;
   its large-height difference from `log t` tends to zero.
3. Finite-matrix differentiation, dominated differentiation and interval DCT
   give differences of regularized expected potentials. Energy bounds fix
   the additive constant at large height.
4. Negative-moment tightness, energy and Gaussian centered concentration
   give tight raw logarithms and uniform second moments BEFORE their mean
   limit is known. This proves non-circular iterated lower-cutoff L1 control.
5. Removing regularization identifies the raw mean; concentration gives its
   probability limit. Exact coordinate and measure-preserving maps transport
   the result to the original common-array Ginibre input.

`GinibreBBVConsequences.lean` exposes `bc12_of_bbv` and the actual
`ginibre_spectral_of_bbv`, using Section 5's proved disk-reference/replacement
argument. Negative moments are tight in probability; no uniform expected
negative-moment bound is assumed.

## Removing the squared-singular-law source

`UnequalGinibreComparison` and `UnequalGinibreCutoff` compare dimensions
tending independently to infinity, without a relative-growth restriction.
`MovingGinibreCore` subtracts the ambient Ginibre mean inside each block;
the exact dimension weights sum to one. `BBVCoreSources` constructs actual
local models from BBV. `BBVProfileEndpoint` joins the sparse and root-Section-3
dense branches. The original two-field endpoint supplied its Ginibre log input
using the theorem above; the migrated core interface constructs this input
from Section 5's proved reference instead. No global high-bandwidth theorem is applied to
the entire sparse core.

This proves the circular-law chain without constructing a separate limiting
singular-value measure. Historical limiting-law/hard-edge interfaces remain
available with their classical-source hypotheses; those are not hidden
inputs of this new endpoint. This is not a line-by-line proof of every
intermediate manuscript statement using its original route.

## Historical verification scope

- Strict final-target/import build: 4467 dependency-inclusive jobs, mostly cached.
- `BBVGinibreAudit.lean`: 203 declarations checked transitively, allowing only
  `propext`, `Classical.choice` and `Quot.sound`.
- `BBVOnlyRegression.lean`: all seven concrete/source signatures passed.
- Selected source-token scan: 196 Lean files passed.

No local Lean/lake build, toolchain or mathlib/cache download was used.
Old full Section 5 and historical Section 6 regression suites were not rerun.
Section 5 remains unchanged on main. This work is now also published on main,
with the verified proof files preserved; see [MAIN_INTEGRATION.md](MAIN_INTEGRATION.md).
