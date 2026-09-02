# Section 10 proof architecture

This file retains its historical name for existing links. The continuation's
mathematical proof chain is complete in the stated real-IID scope and has
passed the clean full-release build and axiom audits. The exact verification
record belongs to [AUDIT.md](AUDIT.md).

Source: [arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1),
Proposition 10.1 and Sections 10.4–10.6. There are no further numbered
propositions after 10.10 in this section: the remaining claims are
(10.30)–(10.57) and their assembly into Theorem 2.10.
Section 10.7 supplies the technical proofs of the preceding local results.

## Module boundaries and order

| Stage | Mathematical role | Main modules |
|---|---|---|
| 1 | Exact ceiling scales, finite argmax, cell division, and power-log limits | `AsymptoticScales`, `AsymptoticErrors`, `FinitePressure`, `CellDimensionLimit` |
| 2 | Actual core mean family and whole-interval concentration | `ConcretePressure`, `ConcentrationScale` |
| 3 | Pointwise exterior singular frames and decomposable scalar tests | `SingularFrames`, `ExteriorSingularFrames`, `ExteriorFrameRelabel`, `SingularCoefficient`, `ClearedSingularTest` |
| 4 | Exact IID coordinate selection, packet laws, and chronological concatenation | `FiniteIIDCoordinates`, `PacketLawTransport`, `PacketPhysicalIdentification`, `IntervalConcatenation` |
| 5 | Actual reset integrability and frozen-core/past fiber integration | `PhysicalPacketReset`, `SandwichIntegrability`, `ResetSandwichLaw`, `ConditionalReset` |
| 6 | Mean induction, maximizing-degree pressure, and global L1/Markov bounds | `IntervalMeanHodge`, `MeanStitching`, `StitchedPressure` |
| 7 | Exact cyclic determinant, random outside arc, and integrated terminal seam | `CyclicPhysicalModel`, `PhysicalBoundaryExpression`, `OutsidePressureIdentification`, `PhysicalSeam`, `CyclicSeamAssembly` |
| 8 | Remainder product, simultaneous Hodge envelope, and normalized error | `RemainderControl`, `RemainderProbability`, `RemainderL1`, `CyclicStitchedPressure`, `LongPressureError` |
| 9 | Literal variance profiles and the four exact permitted Section 3 inputs | `PhysicalProfile`, `ScalarBandGeometry`, `ScalarReferenceProfile`, `VarianceProfiles`, `Section3Inputs` |
| 10 | Source-to-model moment, hard-edge, counting, and bulk adapters | `ProfileMoments`, `CutoffRemoval`, `Section3HardEdge`, `Section3Counting`, `Section3Bulk` |
| 11 | Genuine scalar reference, full-block high-band limit, and pressure calibration | `ReferenceTruncation`, `FullBlockHighBandProfile`, `PhysicalInputLaw`, `PressureCalibration`, `DensityPressureLimit` |
| 12 | Long/direct branch assembly for every bandwidth sequence | `LongRingLimit`, `TargetRingLimit` |
| 13 | Displayed-atom energy identity and minimal-second-moment weak law | `PhysicalAtomEnergy`, `PhysicalMatrixEntries`, `DensityEnergyLimit` |
| 14 | Proved Tao–Vu adaptation, internally constructed disk reference, and weak spectral limit | `DimensionReplacement`, `PhysicalReplacement`, `DiagonalDiskReference`, `CircularLawFromPotential`, `WeakCircularLaw`, `DensityCircularLaw` |

## Why no intermediate certificate remains

The reset proof freezes actual core and past operators, constructs singular
frames pointwise, and integrates a measurable operator-norm statistic.
No measurable random-frame selector is assumed. Independent products and
seams use explicit measure-preserving coordinate maps and proved
almost-sure invertibility of the concrete matrices.

Proposition 10.1 is deduced, not supplied as an input. The scalar-indicator
anchor of 3.5 is used only for its actual scalar profile. Two applications
of 3.4 cancel their common Ginibre reference. The original 3.1 norm cutoff
is retained in the permitted input and then removed using actual energy.

The final replacement step imports proved Tao–Vu source. It constructs a
diagonal IID uniform-disk comparison matrix, proves its log/energy/spectral
limits, handles the actual dimension sequence and normalization, removes
the auxiliary sample, and upgrades compact tests to all bounded continuous
real tests.

Only the paper's original real-IID model conditions and the exact Section 3
statements remain. Section 4 inputs are permitted but are not needed as
additional parameters. Details and scope qualifications are in
[ASSUMPTIONS.md](ASSUMPTIONS.md) and [FORMALIZATION_MAP.md](FORMALIZATION_MAP.md).
