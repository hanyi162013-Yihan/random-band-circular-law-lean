# BernoulliSection10 — the real-IID bounded-density circular law

Lean 4 formalization of the real IID bounded-density branch of Section 10 in
Yi Han's [arXiv:2609.01295v1](https://arxiv.org/abs/2609.01295v1).
It covers Proposition 10.1, the nine local results 10.2–10.10, equations
10.30–10.57, and their assembly into the circular-law conclusion of
Theorem 2.10.

The complete development proof chain has compiled. The completion audit's
343 actual compiler reports satisfy the standard logical-axiom allowlist.
Whole-release build and audit status is recorded separately in [AUDIT.md](AUDIT.md);
a successful development check is not presented as a fresh whole-repository run.

## Public endpoints

All names below are in `BernoulliSection10`.

| Entry point | Conclusion | Source |
|---|---|---|
| `density_high_band_ring_log_limit` | Actual full-block high-band log limit | Proposition 10.1 |
| `densityCorePressureDensity_limit` | Deterministic core pressure calibration | (10.35) |
| `density_long_ring_log_limit` | Actual long-ring log-determinant limit | (10.53) |
| `density_ring_log_limit` | Log limit for every growing-bandwidth sequence | (10.56) |
| `density_ring_energy_limit_of_second_moment` | Actual normalized matrix energy tends to one | (10.57) |
| `density_circular_law` | Circular empirical spectral limit against every bounded continuous real test function | Theorem 2.10, real-IID branch |

The final statement is in
[DensityCircularLaw.lean](BernoulliSection10/DensityCircularLaw.lean).
It uses the literal normalized cyclic matrix `densityCyclicMatrix`, not an
abstract model certificate. Matrix dimensions are `N_n=(s_n+3)W_n`, and the
entries are selected from one infinite IID real sequence. The finite
physical-row marginals are proved to be exactly the paper's product laws.
No independence between different matrix sizes is required.

## Exactly what remains as input

- A real probability law with mean zero, second moment one, and density
  bounded by `L`, encoded by `IsBoundedDensityAtom μ L`.
- Finite third moment.
- Positive integer bandwidths `W_n→∞`; the number of block sites may vary.
- `SourceInputs.Section3Inputs μ L`: the exact specialized statements of
  Theorem 3.1, Proposition 3.3, Lemma 3.4, and Proposition 3.5.

There is no assumed Proposition 10.1, pressure calibration, reset or seam
bound, remainder estimate, reference spectral limit, or Tao–Vu principle.
The permitted Section 3 statements are ordinary theorem parameters, not
custom axioms. No additional Section 4 parameter is needed.

See [ASSUMPTIONS.md](ASSUMPTIONS.md) for the full trust boundary and
[FORMALIZATION_MAP.md](FORMALIZATION_MAP.md) for each source statement,
its hypotheses, Lean representation, dependencies, and coverage status.

## Module boundaries

The chapter contains 111 Lean files: 107 mathematical modules, three audit
modules, and the public umbrella. The main groups follow mathematical roles:

| Role | Main modules |
|---|---|
| Density and measure theory | `BoundedDensity`, `AffineLog`, `MultiAffine`, `MultiAffineSecondMoment`, `ProductMarginal` |
| Physical rows and deterministic exterior algebra | `PhysicalRows`, `PhysicalModel`, `IntegratedHodge`, `SingularFrames`, `ExteriorSingularFrames`, `ClearedSingularTest` |
| Concentration, Hodge control, and packets | `RowConcentration`, `HodgeFamilyGrowth`, `IntervalHodge`, `PacketComparisonGrowth`, `PacketReset`, `PhysicalPacketReset` |
| Concrete probability laws and stitching | `FiniteIIDCoordinates`, `PacketLawTransport`, `IntervalConcatenation`, `ConditionalReset`, `MeanStitching`, `StitchedPressure` |
| Cyclic seam and remainder | `CyclicPhysicalModel`, `PhysicalSeam`, `CyclicSeamAssembly`, `RemainderControl`, `RemainderL1`, `CyclicStitchedPressure` |
| High-band input and pressure limits | `Section3Inputs`, `VarianceProfiles`, `Section3HardEdge`, `Section3Counting`, `Section3Bulk`, `ReferenceTruncation`, `FullBlockHighBandProfile`, `DensityPressureLimit` |
| Arbitrary bandwidth and spectral closure | `LongRingLimit`, `TargetRingLimit`, `DensityEnergyLimit`, `DimensionReplacement`, `DiagonalDiskReference`, `WeakCircularLaw`, `DensityCircularLaw` |

The stable `BernoulliLinearAlgebra` library is imported from `Section9/`.
The user's proved Tao–Vu library and 30 generic analysis modules are included
under `vendor/`, with provenance and SHA-256 manifests. The original
external projects were not edited. No machine-specific dependency path is
required. See [PROVENANCE.md](PROVENANCE.md).

## Precise scope boundaries

The atom law is real and IID. Planar-complex atoms, directional conditional
density alternatives, and the heterogeneous-law generality of 10.2–10.3
are not asserted. Complex matrix coefficients, complex shifts, and complex
eigenvalues are already included.

The final conclusion is the bounded-continuous-test formulation of weak
convergence in probability, not just compactly supported tests. The
implementation also permits three block sites, whereas the paper assumes
at least four. Coordinate changes, explicit constants, and pointwise singular
frames are representation choices, not additional hypotheses or proof gaps.

## Reproduce the verification

Use the repository root, Lean `v4.33.0`, the committed mathlib manifest,
and Python 3.11 or newer:

```sh
# On a fresh machine:
lake exe cache get

# Full memory-bounded build, including the final default lake build:
python3 scripts/build_serial.py
python3 scripts/check_placeholders.py
python3 scripts/check_axioms.py

# Chapter-only entry:
lake build BernoulliSection10
```

The public import is `import BernoulliSection10`. The three chapter audit
files are `AxiomAudit.lean`, `AsymptoticAxiomAudit.lean`, and
`CompletionAxiomAudit.lean`, all under `Section10/BernoulliSection10/`.
The completion audit also checks the full explicit types of the principal
caller-facing theorems.
