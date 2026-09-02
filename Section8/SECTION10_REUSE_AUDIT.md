# Section 10 and vendored analysis: reuse audit for discrete atoms

Audited against published commit `d6c29a1e3f125da59c3da47f68848797259e2cf7`.
The prefix `density` on an object name does not itself impose a density
hypothesis. Its declaration and the theorem's complete type determine reuse.

| Modules / declarations | Exact boundary for Section 8 |
|---|---|
| `PhysicalModel`: `IntervalRows`, `intervalRowsLaw`, `blockNormalization`, `intervalSiteBlocks`, `intervalClearedProduct` | Definitions for arbitrary real atoms and arbitrary measures. The normalization is precisely `(sqrt (3W))⁻¹`. No density premise. |
| `CyclicPhysicalModel`: `densityCyclicMatrix`, `densityShiftedCyclicMatrix_eq_sub_scalar`, `densityCyclicLogDet_eq_polynomial_trace` | Literal cyclic matrix and denominator-free trace identity. The matrix has `(s+3)W` rows; Section 8 uses `s≥1` to obtain `m≥4`. The polynomial trace identity does not require invertibility. `Real.log 0 = 0` is the library's totalized real logarithm, so log-limit proofs still need a vanishing bad event or a truncation argument. |
| `CyclicEntryGeometry`, `PhysicalIIDEmbedding`, `PhysicalProfile`, `PhysicalMatrixEntries` | Deterministic entry geometry, IID marginal transports for any probability law, doubly stochastic squared profile and exact energy identities. Distinct displayed atoms occupy distinct entries. These apply to symmetric Bernoulli unchanged. |
| `PhysicalProbabilityInstances` | Probability normalization of the inner and outer finite product measures; only `[IsProbabilityMeasure μ]`. |
| `PhysicalAtomEnergy` | Definitions, flattening identities and `intervalAtom_measurePreserving` are general. Its integrability, expectation and limit wrappers are stated using `IsBoundedDensityAtom`; use the later second-moment generalization or the new exact Bernoulli proof instead. |
| `FiniteIIDLawOfLargeNumbers` | General finite-IID law of large numbers from measurability and integrability. No density premise. |
| `DensityEnergyLimit.intervalMeanAtomSquare_tendsto_of_second_moment`, `density_ring_energy_limit_of_second_moment` | General probability law, integrable square, second moment one. The energy limit asks only for `W→∞`; this is an energy statement, not an improvement of the Section 8 bandwidth condition for logarithmic potentials or the circular law. |
| `ProbabilityLimits`, `ProbabilityTransport`, `ProductMarginal`, `FiniteIIDCoordinates` | Generic probability, product and triangular-array arguments. Their supplied comparison/error hypotheses must still be proved for the actual Section 8 objects. |
| `IntervalTransfer.intervalClearedProduct_eq_clearing_smul_compound` | Deterministic transfer representation under explicit nonzero determinants. Safe on the Section 8 good event. The later `intervalTransfer_representation_ae` uses bounded density and cannot be specialized to Bernoulli. |
| Algebraic portions of `MultiAffine`, `PhysicalAffinity`, `RademacherTensor`, `SquarefreeRademacher`, `PacketTensorScaling` | The tensor representations, coefficient identities and existence of a sign assignment are deterministic. `RademacherTensor` is not a probability-law construction. Quantitative probabilistic conclusions in neighboring modules must be checked separately. |
| `BoundedDensity`, `AffineLog`, density-based nonvanishing/log-integrability results and probabilistic portions of `PacketReset`, `ConditionalReset`, `PhysicalPacketReset`, endpoint/seam/long-pressure density assemblies | Their density premises are essential for those proved statements. In particular a nonzero polynomial may vanish on a positive-mass set of Bernoulli configurations. These results cannot discharge the Section 8 good-event/reset/truncated-pressure bounds. Deterministic identities in the same modules remain reusable. |
| `SourceInputs.Section3Inputs` | **Not a usable Bernoulli input package.** Each of its four fields starts with `IsBoundedDensityAtom μ L → …`. Supplying this structure alone says nothing about a discrete `μ`. The new `Section3HighBand.Section3SubgaussianHighBandInput` instead states Proposition 3.8 for real sub-Gaussian atoms; its Bernoulli atom certificate is proved in `RademacherEnergy`. The authorized external set is Section 3, Cook and Nguyen; Section 4 is not used. |
| `Section3HardEdge`, `Section3Counting`, `Section3Bulk`, `FullBlockHighBandProfile`, `TargetRingLimit`, `DensityCircularLaw` | These Section 10 wrappers thread the density package. Generic analysis inside them can be reused after separating that premise, but their published caller-facing statements do not prove the discrete branch. |
| `vendor/short-ring-analysis` | The singular-value logarithmic truncation, counting, upper-edge and disk-potential calculations are proved analysis. `ExternalInputs` is a collection of proposition interfaces, not proved random-matrix estimates. Do not treat instances of `Theorem31LeastSingularValueInput`, `BC12GinibreFullLogInput`, etc. as available without constructing them from allowed inputs or proved results. |
| `vendor/tao-vu-replacement`, `DimensionReplacement`, `PhysicalReplacement` | Proved Tao–Vu replacement and arbitrary diverging dimension adapter. The replacement implication itself is not an additional assumption. Its integrability, tightness/energy and log-difference hypotheses must be supplied. |
| `DiskReferenceLaw`, `DiagonalDiskReference` | Actual uniform-disk probability law, IID diagonal comparison matrices, log-potential and ESD limits, and uniform expected energy are all constructed internally. No extra Ginibre/BC12/reference-ensemble input is needed for this final comparison. |
| `CircularLawFromPotential.physical_circularLaw_of_logPotential` | Requires entry measurability, diverging positive dimensions, uniform expected normalized energy, and the target matrix's circular log-potential limit for Lebesgue-a.e. shift. It constructs and removes its auxiliary reference randomness. Applicable to Bernoulli once its target log-limit is proved. |
| `PositiveMatrixIndex`, `WeakCircularLaw` | Generic index reparametrization and upgrade from compactly supported spectral tests to bounded continuous tests. No density or invertibility premise. |
| `PacketMultiaffine`, `PacketFrame`, `PacketFrameProbability`, `PacketPhysicalIdentification` | The literal boundary determinant, coefficientwise artificial-frame limit, normalized Gram-volume limit, comparison constants and identification with the displayed physical cleared transfer coefficient are deterministic. They support a new capped passage using Section 9's Cook theorem, without calling the density-based uncapped-log bounds. |

## Concrete Bernoulli source now present

`BernoulliSection8/RademacherEnergy.lean` defines the two-point real measure
`rademacherLaw = (1/2) • δ₁ + (1/2) • δ₋₁`, computes its atoms and all real
integrals, proves mean zero, second moment one and `HasSubgaussianMGF id 1`,
then transports the sign support to every physical coordinate. On each sign
configuration with positive `W`, the actual cyclic matrix satisfies

```
(sum i, sum j, ‖X i j‖²) / ((s + 3) W) = 1.
```

The corresponding almost-sure identity supplies integrability, expectation
one and the triangular-array energy limit without an asymptotic assumption.
This energy theorem makes no assertion that finite-size determinants are
almost surely nonzero. Reset, pressure and seam statements are implemented
in the separate modules listed below.

The new Section 3 interface is mapped to Proposition 3.8,
`prop:subgaussian-block-high-band`, equations (3.18)–(3.19). Its bandwidth
condition is the stated high-band condition `W ≥ N^(8/9 + ω)`. This branch
does not settle the full `W / log N → ∞` regime by itself.

| New Section 8 modules | Implemented statement and dependency boundary |
|---|---|
| `RademacherIID`, `PhysicalBoundaryScaling` | Actual finite product Rademacher families and exact physical row scaling. No density, terminal or independence certificate is supplied by the caller. |
| `RademacherBoundarySmallBall`, `RademacherFrameSmallBall` | Cook's Section 9 terminal theorem is transported to the actual normalized boundary evaluation and exterior coefficient. The latter has the exact fresh-packet Parseval identity and capped-loss/zero-probability bounds. Endpoint invertibility is an explicit deterministic premise at this local stage. |
| `CookRates`, `RademacherTerminalRates` | The explicit terminal base loss is bounded by `(160 + 6β₁ + 6β₂) W log(eW)`. The actual Cook failure probability multiplied by `log(eW)` tends to zero. These rates are proved internally rather than retained as external assumptions. |
| `RademacherInterface`, `RademacherEndpointInterface`, `RademacherBoundaryGrowth` | The actual Nguyen good events supply nonzero endpoint/interface determinants and the explicit logarithmic coefficient comparison bound. |
| `ConditionalCappedReset`, `ResetAveraging`, `IntervalResetLoss` | The singular frame is chosen with core, past and endpoints fixed. The fresh-packet estimate is integrated over the literal endpoint/fresh and core/past/reset product laws. `intervalResetLoss_integral_le` discharges the intermediate coefficient-bound hypothesis using `RademacherBoundaryGrowth`. |
| `RademacherSeam`, `RademacherSeamLimit` | The exceptional event includes zero cyclic Fock values. On the actual long branch `anchorSize W ≤ N`, `rademacherCyclicSeamDifference_tendsto` states that the normalized seam tends to zero under Cook, Nguyen, `W → ∞` and `log N / W → 0`. The zero-Fock probability limit is included separately. |
| `MesoscopicScales`, `CellCoordinates`, `CellConcentration`, `HighBandTransport`, `PressureCalibration`, `RademacherLogPotential` | The source contains the exact Section 8 core/reset/anchor coordinates, concentration, pressure calibration and direct/long-branch assembly. `rademacher_log_potential` uses the permitted Section 3, Cook and Nguyen inputs; the target logarithmic-potential limit is not a caller assumption. |
| `RademacherCircularReduction`, `Section8Results` | The former discharges physical measurability and energy and applies the proved disk-reference replacement. The source of `section8_bernoulli_circular_law` supplies its internal logarithmic-potential premise via the preceding assembly and concludes convergence for every bounded continuous spectral test. |

## Verification status

`RademacherEnergy`, `RademacherIID`, `PhysicalBoundaryScaling`,
`RademacherCircularReduction` and `Section3HighBand` have each passed an
independent Lean check and produced an `.olean`. These checks establish
those modules only; they do not certify the remaining integration chain.

The complete source chain through `Section8Results` is present. Normal
serialized Lake verification is in progress, including dependencies and
the final whole-project build. The boundary/frame, terminal-rate, reset,
seam and final-assembly modules still require that verification to finish.
This audit does not claim a completed release or a successful final build.
