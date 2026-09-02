# Section 9 dependencies required by Section 8

Audit date: 2026-09-02. Audited baseline:
`d6c29a1e3f125da59c3da47f68848797259e2cf7`.
Reference: Yi Han, [arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1).
The source statements checked are `part2_block.tex`, Section 8
(`sec:gb-global-proof`), and the local statements and Section 9 proofs.
This is a source/signature audit; it is not a replacement for the final
integrated build, actual `#print axioms` run, or final-signature audit.

## Finding and subsequently authorized trust boundary

After this audit identified the two explicit dependencies, the user
authorized Nguyen and Cook to remain external mathematical inputs in this
task. The user also clarified that no Section 4 paper assumption is part
of this task. The final external-input list is **Section 3, Cook, and
Nguyen**; already proved source code may still be reused normally.
Cook and Nguyen are therefore **permitted external estimates**. Concrete
Rademacher model instantiations and the Section 8 assembly have now been
written; their integrated Lean verification is still in progress. The earlier Section
3/4-only boundary is superseded. No
reset, seam, pressure, reference, or replacement assumption is authorized
by this change.

The Section 9 probability development does **not** discharge Section 8
inputs (L1) and (L2) from the atom-law assumptions alone. Its public definitions
still take `NguyenBottomSingularInput` and/or
`CookDeformedSquareInput`. A whole-repository search of Lean sources found
133 references to these structures, all declarations or uses of parameters;
no constructor, existence theorem, or Rademacher-specific proof discharging
the required estimates was found in the audited baseline.

Those parameters are stronger than the random-atom model assumptions, and
they were not among the task's original Section 3/4 proposition inputs.
They do not appear in `#print axioms`: they are ordinary parameters of
proofs. A clean logical-axiom report therefore does not by itself establish
the requested final trust boundary.

Their independent proofs remain absent from the audited formal source.
The user's explicit authorization now permits using their precise types
below. The current source signatures in `Section8Results.lean` retain Cook,
Nguyen, and `Section3SubgaussianHighBandInput rademacherLaw 1` visibly.
The model, packet, parameter-range, conditioning, endpoint, pressure,
and terminal callers have been written internally. Their presence is a
source-level finding, pending the complete build and final axiom audit.
Moving additional unproved conclusions into a
reset, seam, pressure, or frame record would still violate the boundary.

## Exact external-input types

Source: `Section9/BernoulliSection9/ExternalInputs.lean`.

The underlying `IidSubgaussianSquare Ω μ n` carries measurable real entries,
`iIndepFun`, identical distributions, integral mean zero, second moment one,
and `HasSubgaussianMGF` with a fixed `ℝ≥0` parameter.
`IidSubgaussianFamily` provides the same properties on a general label
type; its injective restrictions construct the complete iid squares.

### Cook

`CookDeformedSquareInput` fixes:

- a subgaussian bound at least one;
- a positive weight interval containing one;
- positive `beta L`, nonnegative `cookC L`, and positive `cookc L`.

Its `unconditional` field asserts, for every probability space, every
admissible iid square and profile in those fixed ranges, every `n ≥ 2`,
`L ≥ 0`, and deterministic complex deformation with
`‖D‖ ≤ n ^ L`,

```text
P{s_min(profiledMatrix S a + D) ≤ n ^ (-beta L)}
  ≤ cookC L * sqrt(log n / n) + exp(-cookc L * n).
```

Its `conditional` field asserts the corresponding almost-everywhere
conditional-expectation bound for a matrix deformation measurable with
respect to a sigma-field independent of the fresh-entry sigma-field,
under an almost-everywhere polynomial norm bound. It also supplies
measurability of the actual bad event.

The direct calls are in `ConditionalCook.lean` and
`CoordinateConditionalCook.lean`. The public local proof actually needs
the conditional estimate. A deterministic-deformation estimate alone
would still require a conditioning/lifting proof.

The structure quantifies over all atom laws in its fixed subgaussian range
and all profiles in its interval; a theorem for Rademacher squares alone
does not literally construct this universal structure. A narrower internal
implementation can use a proved law-specific estimate, but cannot leave
that estimate as a new final-theorem parameter.

### Nguyen

`NguyenBottomSingularInput` fixes the subgaussian range, numbers
`0 < theta < 1`, `gamma0 > 0`, positive `nguyenc, nguyenC`, and
an integer cutoff `k0`. Its two estimate fields are:

```text
fixedIndex:
  1 ≤ k ≤ k0, k ≤ n, ε ≥ 0
  => P{s_(n-k)(rawMatrix S) ≤ ε / sqrt n}
       ≤ nguyenC ^ k * ε ^ (k ^ 2) + exp(-nguyenc * n)

overcrowding:
  k0 < k < gamma0 * n, k ≤ n, ε ≥ 0
  => P{s_(n-k)(rawMatrix S) ≤ k * ε / sqrt n}
       ≤ (nguyenC * ε) ^ ((1-theta) * k^2)
           + exp(-nguyenc * n).
```

The singular values are zero-indexed, so `s_(n-k)` is the source's
`s_{n-k+1}`. Each invocation requires the square's subgaussian parameter
to be below the input's bound. The direct invocations occur in
`InterfaceControl.lean`, in the bad-index probability estimate.

The existing Section 3 repaired full-block least-singular-value statement
concerns the cyclic full matrix, a scalar shift, and an error of order
`W^(-1/2)`. Its statement does not immediately give these exponentially
small square-interface events or arbitrary complex deformations. The
baseline `Section10.SourceInputs.Section3Inputs` is additionally
specialized to `IsBoundedDensityAtom`, so it cannot be instantiated with
Rademacher as written. The new `Section8/BernoulliSection8/Section3HighBand.lean` instead
defines `Section3SubgaussianHighBandInput` for the real subgaussian law
class, retains the actual Proposition 3.8 high-band logarithmic-potential
conclusion, and supplies `rademacherLaw_isRealSubgaussianAtom` internally.

## Section 8 input-by-input mapping

| Section 8 requirement | Existing entry point | Exact reusable scope and inputs |
|---|---|---|
| (L1), `eq:gb-one-site-failure`, determinant/inverse/norm bounds | `interfaceCanonicalDetUpperLowerInverseControl` | Already uses the literal `1 / sqrt(3W)` normalization. Operator-norm tail is proved internally from the MGF hypothesis. Determinant/inverse probability still requires Nguyen. |
| Two good endpoints | `interfacePairProbabilityAndPaperEndpointGoodCanonical` | Width threshold is constructed internally. Gives bad probability at most `2 exp(-(interfaceCombinedRate I / 2) W)`; no independence between the two endpoints is required for this union bound. |
| Diagonal-block norm contribution to the one-site event | `normalizedRawComplexMatrix_opNorm_tail` | No literature-estimate parameter; can be unioned with the two interface bad events. |
| (L2), terminal coefficient-relative cap and zero event | `section9TerminalSmallBall` | Unit-entry-weight packet; explicit Cook parameter; positive coefficient norm, all positive caps, zero probability, reverse estimate, Parseval. |
| Predictable outside complex deformation | `section9TerminalSmallBallConditional` | Outside sigma-field measurability and independence are explicit ordinary model conditions; not valid for arbitrary dependent substitution. Cook remains. |
| Physical terminal normalization | `section9PhysicalTerminalSmallBall` | Exact nonzero common-scaling identity; applies the raw theorem at `sigma * z` and `sigma • Q`. Cook remains. |
| Fixed exterior degree and arbitrary orthonormal frames | `section9ArbitraryFrameSmallBall` | Cook plus `PaperEndpointGood`; latter contains concrete endpoint norm and positive determinant lower bounds. |
| Predictable random endpoints/frames | `section9ArbitraryFrameSmallBallConditional` | Endpoint goodness for every outside parameter, measurable frames/endpoints, and fresh/outside independence are required. |
| Combined interface and frame result | `section9InterfaceAndArbitraryFrameSmallBall` | Constructs endpoint data on the good event and explicitly takes Nguyen and Cook. The additional actual Section 8 reset callers are now written in `RademacherFrameSmallBall`, `ConditionalCappedReset`, and `IntervalResetLoss`, pending their integrated check. |

The public terminal choice is `t = W`. Its exact bad probability is

```text
exp(-W)
 + uniformCookFailureBound (cookC L1) (cookc L1) W
 + uniformCookFailureBound (cookC L2) (cookc L2) W,

uniformCookFailureBound C c W
 = C * sqrt(9 * log(3W) / W) + exp(-c * W / 4).
```

The deformation exponents `L1,L2` are fixed functions of the shift
exponent and Cook's fixed constants; they do not depend on the outside
matrix or random RRQR rank. These finite formulas have the strength
needed for `p_W = O(sqrt(log W / W))`. The new `CookRates.lean`,
`RademacherTerminalRates.lean`, and `AveragedRates.lean` contain the
fixed-constant bounds and scalar limits used by the actual capped-reset
assembly. This is internal asymptotic work, not an additional external
small-ball input; the integrated caller remains under verification.

The base loss is the explicit sum
`log threeBlockConcreteComparisonConstant + terminalUniformValueLoss +
terminalReverseLoss`. Its value-loss factors are powers of `2W`,
`3W`, and the canonical polynomial threshold; hence the fixed-exponent
RRQR variant is adequate for an `O(W log W)` argument. The published
RRQR exponent is four; the proved exponent is sixteen. The rank,
skeleton, pivot, and CUR identities are exact. Exponent sixteen increases
fixed constants and does not obstruct Section 8's polynomial-size cells.

## Deterministic identities that are already available

| Source formula / purpose | Entry point | Hypotheses and interpretation |
|---|---|---|
| Cleared one-step exterior operator | `clearedStepCompound`, `clearedStepCompound_eq_det_smul_compound_companion` | Defined by complementary minors at every interface, including singular ones; equals `det B • compound r T` on `IsUnit B.det`. |
| Chronological products | `polynomialClearedCompoundProduct` | Later steps multiply on the left; no inverses in the definition. |
| Full Fock, `eq:gb-full-fock` | `polynomialClearedSignedCompoundTrace_listOfFn_eq_physical` | Arbitrary complex block arrays, including singular interfaces; `m+1` sites and `0 < m`. The sum over all finite subsets is the degree-by-degree signed trace. The Floquet sign has norm one. |
| Actual normalized cyclic matrix | `densityShiftedCyclicMatrix`, `densityShiftedCyclicMatrix_eq_sub_scalar` | Despite the name, these are deterministic definitions and identities with no density hypothesis. Site convention is `s+3`; Section 8 `m ≥ 4` is covered by `s ≥ 1`. |
| Physical log determinant versus cleared trace | `densityCyclicLogDet_eq_polynomial_trace` | No density or invertibility assumption. This is an identity of Lean's total real logarithms, not a proof of nonsingularity. |
| Boundary complete coefficient norm / Gram comparison | `globalBoundaryCoefficientNorm_bounds_fullyInstantiated`, `globalBoundaryCoefficientNorm_bounds_of_hodgeBounds_fullyInstantiated` | Requires invertible endpoint blocks and invertible boundary relation; no `Theta_11` invertibility condition, mask certificate, or elimination certificate. |
| Gram volume versus maximal exterior operator norm | `gramVolume_operatorCompound_two_sided_twoBlock_two_pow` | Already gives factor `2^W`, sufficient for the pressure comparison. |
| Hodge control from interface good data | `literalBoundaryHodgeComparisonConstant` and `literalArtificialCoefficientNorm_scaled_bounds_of_endpointGood` | Forward Frobenius compound bounds are derived from Euclidean operator bounds; norms must not be conflated. |

The raw unit-entry-weight finite constants have been improved elsewhere
in the integrated repository. In particular,
`Section10/BernoulliSection10/PacketComparisonGrowth.lean` proves, with
**no density assumption**,

```text
log_threeBlockConcreteComparisonConstant_fin_le_W_log_eW:
  log (threeBlockConcreteComparisonConstant z)
    ≤ packetDeterministicLogConstant z * W * log(exp 1 * W).
```

Thus the Section 9 README's original local-library limitation about
unsynthesized finite constants must not be repeated as a whole-repository
absence. This theorem is for fixed `z`; the physical row-scaling
substitution produces `sqrt(3W) * z`. The new `WidthLog.lean` and
`RademacherBoundaryGrowth.lean` instead use the exact translation logarithm
`3W log(1 + sqrt(3W) norm(z))` to retain one width logarithm. The scalar
module has passed Lean checks; the endpoint caller is awaiting its
normal dependency-ordered build.

The endpoint comparison is already explicit through
`endpointCompoundCrudeBound W B =
(2 * max 1 ((2W)^2 * B))^(2W)` and the inverse determinant bound.
For fixed `B` and determinants at least `exp(-CW)`, this has the
needed `exp(O(W log W))` size. The Section 9 public interface supplies
these finite constants; the new Section 8 endpoint-good wrapper and
two-sided normalized coefficient/Gram comparison are written in
`RademacherBoundaryGrowth.lean`, pending integrated verification.

The main full-block model has unit raw weights and uniform physical
normalization. A general theorem for independently weighted entries
`a_e` in a fixed positive interval is still not supplied by the
deterministic coefficient-norm library. This general weighted extension
is not required to instantiate the stated unit-weight Bernoulli target.
Uniform physical row scaling alone should not be described as a proof of
the general weighted-profile theorem.

## Discrete zero events and final assembly requirements

`cappedLogLoss T c w` explicitly equals `T` when `w = 0`.
The local theorem proves a small **positive** bound on the zero event;
it does not claim almost-sure invertibility. This is appropriate for
Rademacher.

The cleared Fock identity remains valid at zero determinants, while
`Real.log 0 = 0` in Lean. The current source now includes
`rademacherCyclicFock_zero_probability_tendsto_zero` and the corresponding
seam comparison in `RademacherSeamLimit.lean`. Together with the clipped
good-event identities, these are the intended explicit treatment of the
exceptional zero event. Their integrated verification is pending; no
almost-sure invertibility conclusion is imported from the density model.

The previously missing assembly steps now have the following source
declarations. This table records written implementations, not a release
or successful integrated-build claim.

| Assembly step | Current Section 8 source |
|---|---|
| Literal iid coordinates and fresh packet/outside restrictions | `RademacherIID.lean`, `RademacherIntervalIID.lean`, `CellCoordinates.lean`, `CellResetLoss.lean` |
| All-interface event, local restrictions, and bandwidth limit | `FiniteSupport.lean`, `BandwidthLedger.lean`, `RademacherInterface.lean` |
| Actual frame coefficient, conditional capped reset, and interval integral | `RademacherFrameSmallBall.lean`, `ConditionalCappedReset.lean`, `ResetAveraging.lean`, `IntervalResetLoss.lean` |
| Clipped core concentration, pathwise pressure sandwich, and summed Markov estimate | `CellPressureLimit.lean`, `CellPressureSandwich.lean`, `CellResetRates.lean`, `CompleteCellPressureLimit.lean` |
| Actual terminal seam and incomplete-cell removal | `RademacherSeam.lean`, `RademacherSeamLimit.lean`, `RademacherRemainder.lean`, `RademacherRemainderLimit.lean` |
| Many-cell anchor calibration, permitted Section 3 branch, and arbitrary branch alternation | `Section3HighBand.lean`, `HighBandTransport.lean`, `AnchorBandwidth.lean`, `PressureCalibration.lean`, `RademacherLogPotential.lean` |
| Literal matrix energy and density-free circular-law reduction | `RademacherEnergy.lean`, `RademacherCircularReduction.lean`, `Section8Results.lean` |

`section8_bernoulli_log_potential` and
`section8_bernoulli_circular_law` are now written in `Section8Results.lean`.
Their inspected source signatures take the named Cook, Nguyen, and
Section 3 inputs; the Nguyen parameter-range condition; positive widths
and outside-site counts; and `W → ∞`, `W/log N → ∞`, where
`N=(s+3)W`. They do not take pressure convergence, a reset estimate, a seam
estimate, a frame/endpoint certificate, an energy certificate, a
replacement theorem, or a Section 4 paper assumption. The long-branch
and calibration helpers accept reusable intermediate comparison
hypotheses in some declarations, but `RademacherLogPotential.lean` passes
the newly written actual comparisons to them.

The remaining gate is verification: complete the normal dependency-ordered
Lake build and its final integrated `lake build`, fix any elaboration or
proof failures, then perform the placeholder scan, actual logical-axiom
audit, and compiled public-signature audit. The current source signature
inspection alone does not certify that the final declarations elaborate
or that their proof dependencies contain no placeholder axioms.

## Concrete Section 8 implementations added during this task

The baseline absence above is distinct from the new callers written in
this task. `BandwidthLedger.lean`, `FiniteSupport.lean`, `WidthLog.lean`, and
`RademacherIntervalIID.lean` have passed direct Lean checks. They prove, respectively, the original
bandwidth-ratio equivalence (under `N >= 4W`) and finite-union exponential
limit; the measurable finite-support construction and its exact probability
identities; the pure scalar width-logarithm bounds; and the literal interval
iid-square instances. The remaining modules below are
under dependency-ordered checking; their presence alone is not a build
claim.

- `RademacherIntervalIID.lean` builds all three physical block squares
  from the literal product of the two-point measure. There is no
  user-supplied iid or subgaussian certificate.
- `FiniteSupport.lean` realizes arbitrary predicates as finite measurable
  events on the local interval sign support, with unchanged probability.
  `RademacherInterface.lean` then constructs measurable interval and
  subinterval good events, normalized block controls, and their union
  bounds and bandwidth limits.
- `RademacherEndpointInterface.lean` constructs a measurable event on
  the independent endpoint-pair law itself. Its complement is bounded
  by `9 exp(-(interfaceCombinedRate I / 2) W)` by transport from the
  actual physical three-site interval; endpoint goodness is not left as
  an almost-sure premise.
- `RademacherTransferBounds.lean` derives forward, inverse Hodge, and
  chronological-product losses on that actual good event. It includes
  every exterior degree, nonzero operator norms, and agreement of
  clipped and ordinary logarithms on the event. The three-site packet
  cap has the explicit `constant * W * log(eW)` scale.
- `WidthLog.lean`, `BoundaryGrowthCore.lean`, and
  `RademacherBoundaryGrowth.lean` separate the exact raw-shift
  `3W log(1 + sqrt(3W) norm(z))` and row-normalization cost from the
  fixed-unit-weight coefficient comparison. This gives an endpoint-good
  bound for the actual normalized inverse comparison coefficient using
  a constant depending only on the fixed Nguyen input and `z`, and the
  two-sided absolute log comparison with the Gram volume.
- `RademacherRemainderLimit.lean` compares the outside prefix with its
  complete cells on the same `IntervalRows W (s+3)` sample, dividing by
  the actual full dimension `(s+3)W`. The global interface event restricts
  to every selected subinterval. The incomplete-cell length is bounded
  by the single-cell scale `BernoulliSection10.densityAnchorSize`, while
  the long-branch hypothesis uses the larger Section 8 full-anchor size;
  these two definitions are not identified. The deterministic error
  vanishes by the proved Section 10 remainder scale, and its exceptional
  probability vanishes by the actual Nguyen union estimate.

These callers add no reset, seam, pressure, reference, replacement,
weighted-profile, or Section 4 assumption. The finite-support argument
is specific to the literal Rademacher law; it does not establish local
measurability for every general subgaussian atom law.
