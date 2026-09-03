# Random band circular law — Lean formalization

Lean 4 formalization accompanying Yi Han's paper
[*The circular law for non-Hermitian random band matrices: optimal bandwidth,
periodic profile and discrete law*](https://arxiv.org/abs/2609.01295).

This repository contains checked proof chains for the paper's high-band
estimates, transfer and small-ball tools, and several circular-law conclusions.
The guide below follows the paper's section order and describes the public
interfaces on `main`. It does **not** claim a complete formalization of every
statement in the paper. Exact hypotheses, quantitative variants and coverage
are recorded in the linked theorem maps and Lean declarations. Several endpoints
remain conditional on the [explicit mathematical inputs listed below](#inputs-still-assumed-at-public-interfaces).

## Results in paper order

### Section 3 — High-band estimates and logarithmic-potential anchors

[`section3/`](section3/README.md) contains the concrete density endpoints for
Proposition 3.6 and the real-subgaussian full-block endpoint for Proposition 3.8.
The density proof connects the proved Theorem 3.1 to the actual cyclic matrix;
Hermitization counting and local bulk comparison are constructed from the
stated BBV input. Callers do not supply a least-singular-value or counting
conclusion in place of these proofs.

- Proposition 3.6: real or planar-complex bounded-density atoms with the stated
  moment assumptions; high-band regime `W ≥ M^(8/9 + ω)`, `0 < ω < 1/9`.
- Proposition 3.8: fixed real centered, variance-one subgaussian atoms,
  including discrete laws, for the three-neighbor full-block ring.
- Both give the normalized shifted log-determinant limit for every fixed
  complex shift, subject to their explicit inputs below.

See the [density endpoint map](section3/HIGH_BAND_INTEGRATION.md) and
[Proposition 3.8 statement and assumptions](section3/PROPOSITION38.md).
These are not proofs of every Section 3 result: in particular, Proposition 3.2
remains an input to the subgaussian endpoint.

### Section 4 — Exterior transfer and local density tools

[`Section4/`](Section4/README.md) supplies checked proof chains for all nine
named results: row-linearity, the periodic determinant identity,
singleton-domain words, isolated full monomials, multiaffine small-ball bounds,
fresh closure, projective observability, operator-affine logarithmic estimates,
and pressure concentration.

The paper-specific determinant identity and the real, planar and directional
density constructions are proved from their stated model hypotheses.
The final pressure specializations derive the required integrability internally.
See the [declaration-level coverage and assumption map](Section4/FORMALIZATION_MAP.md).

### Section 5 — Calibration, pressure lifting and spectral limits

[`section5/`](section5/README.md) proves the calibration and pressure-lifting
chain, logarithmic-potential limits, energy tightness, and empirical spectral
convergence against bounded continuous real tests.

For fixed centered, unit-second-moment real or planar-complex atom laws with
bounded density and finite third absolute moment, and centered indicator-band
profiles with fixed positive lower and upper bounds, the
public endpoints construct the sampled matrices and invoke Section 3 internally.
Import `CircularLawSections56.Section5.PublishedSection3ConcreteEndpoint` and
use `indicator_real_full_of_published_literature` or
`indicator_complex_full_of_published_literature` in the namespace
`CircularLawSections56.Section5.PublishedSection3Concrete`.

These endpoints retain two quantitative Section 4 pressure inputs as well as
the named literature inputs; these pressure hypotheses have not been eliminated
merely because Section 4 source is present in this repository.
Broader taper and varying-atom results are available with their documented
Section 3/4 interfaces. The concrete fixed-law integration does not automatically
cover taper profiles whose lower bounds vanish. See the
[concrete interface](section5/CONCRETE_SECTION3_INTERFACE.md) and
[full Section 5 coverage](section5/SECTION5_COVERAGE.md).

### Section 6 — Gaussian noncompact profiles

[`section6/`](section6/BBV_ONLY_ENDPOINT.md) proves the circular-law endpoint
for the actual normalized Gaussian cyclic matrices with a strictly positive,
continuous, integrable profile of bounded variation and integral one.
The bandwidth is positive and tends to infinity; its ratio to the dimension
need not converge. The public statement uses every continuous compactly
supported real test function on the complex plane.

Import `CircularLawSection6.BBVOnlyProfileEndpoint`. The endpoint is
`CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law_of_bbv_sources`.
Its source record contains only BBV and the two finite Section 4 pressure
estimates for each compact core. Ginibre negative-moment tightness,
logarithmic-potential and spectral limits are derived internally from BBV;
there is no independent BC12, Ginibre correlation-formula or Han premise.
See the [exact input boundary and proof route](section6/BBV_ONLY_ENDPOINT.md).

### Section 7 — Local estimates used by the block argument

There is no separate `Section7/` package. The formalized local estimates are
organized with their proofs in Section 9 and their applications in Section 8.
They include interface control, terminal and arbitrary-frame small-ball
constructions, Floquet identities, boundary comparison and exterior-operator
comparison. Coverage and quantitative qualifications are given in the
[deterministic reference map](Section9/PAPER_REFERENCES.md) and
[small-ball reference map](Section9/SMALL_BALL_REFERENCE_MAP.md);
this is not a separate claim that all of Section 7 is complete.

### Section 8 — Real subgaussian and Bernoulli block rings

[`SubgaussianSection8/`](SubgaussianSection8/README.md) proves the logarithmic
potential and circular law for every fixed real IID law with mean zero,
second moment one, and a finite subgaussian MGF parameter. The conditions are
`W → ∞` and `W / log N → ∞`, with `N = (s + 3)W` and positive widths and
core-site counts. No density, symmetry or bounded-support assumption is imposed.

The public results are `SubgaussianSection8.section8_subgaussian_log_potential`
and `SubgaussianSection8.section8_subgaussian_circular_law`.
The [Rademacher specialization](Section8/README.md) is available in
`BernoulliSection8`.

Both construct their high-band anchor by calling the concrete Proposition 3.8
proof. Cook and Nguyen inputs remain, together with Proposition 3.8's upstream
assumptions. No separate pressure, reset or high-band convergence certificate
is requested by the final endpoints. See the
[Section 3 connection and exact public inputs](Section8/SECTION3_INTEGRATION.md)
and [general proof map](SubgaussianSection8/STATUS.md).

### Section 9 — Deterministic algebra and local small-ball proofs

[`BernoulliLinearAlgebra`](Section9/README.md) proves the terminal polynomial
constructions, Block Floquet identity, Proposition 9.3, Corollary 9.4,
Jacobi/Hodge identities, deterministic boundary comparison, and the exterior
operator comparison used in Lemma 7.8. These results do not assume Cook,
Nguyen or an RRQR theorem.

[`BernoulliSection9`](Section9/SMALL_BALL_README.md) provides the terminal,
conditional and arbitrary-frame small-ball deductions, together with interface
probability control. Cook and Nguyen estimates are explicit inputs with fixed
subgaussian ranges; Cook also fixes the profile range. RRQR selection and
CUR/Schur constructions are proved internally.

The scope is quantitative and specific: the terminal packet uses unit-entry
weights; general entrywise-weighted coefficient comparisons and all printed
uniform `exp(C W log W)` bounds are not claimed. The proved RRQR exponent is
16 rather than the paper's 4, and the small-ball statements expose finite
loss/failure expressions. See the [algebra map](Section9/FORMALIZATION_MAP.md)
and [small-ball map](Section9/SMALL_BALL_FORMALIZATION_MAP.md).

### Section 10 — Real and complex bounded-density block rings

[`Section10/`](Section10/README.md) covers the real and planar-complex IID
bounded-density, finite-third-moment branches of results 10.1–10.10 and the
circular-law conclusion of Theorem 2.10. The matrix is the actual normalized
three-neighbor full-block ring, with `N = (s + 3)W` and positive `W → ∞`.
Both atom laws are centered and have unit second moment.

Use `import BernoulliSection10Source`. The final results are
`real_density_circular_law`, `planar_density_circular_law`,
`real_density_ring_log_limit` and `planar_density_ring_log_limit`, all in
`BernoulliSection10Source`. The circular laws use every bounded continuous
real test function. Complex density means the joint planar density; independent
real/imaginary parts and circular symmetry are not assumed.

Actual matrix laws, Section 3 applications, counting, Gaussian reference,
pressure and replacement steps are connected internally. BBV and BC12 remain
explicit inputs, with geometric Brascamp–Lieb additionally required for real
atoms. Directional conditional-density, heterogeneous-law and general
finite-`(2+α)`-moment extensions are not included in these endpoints.
See the [real map](Section10/FORMALIZATION_MAP.md),
[complex map](Section10/COMPLEX_FORMALIZATION_MAP.md), and
[source-connection audit](Section10/SOURCE_CONNECTION_AUDIT.md).

## Inputs still assumed at public interfaces

The following are mathematical hypotheses, not custom Lean axioms.
Ordinary model conditions—independence, normalization, moments, density,
profile bounds and bandwidth growth—remain explicit as well, but are not
external theorem inputs.

| Undischarged input | Where it is required |
| --- | --- |
| BBV canonical Gaussian/free comparison | Section 3 anchors and the public Section 5, 6, 8 and 10 endpoints. |
| BC12 shifted-Ginibre negative-moment tightness and full normalized log-determinant limit | Proposition 3.6 density endpoints and the concrete Section 5 and Section 10 endpoints. |
| BC12 negative-moment tightness, plus finite Ginibre correlation/projection formulas | Proposition 3.8 and Section 8. The full Ginibre log limit is derived from those formulas, not separately assumed there. |
| Real geometric Brascamp–Lieb inequality | Real-density branches of Proposition 3.6, Section 5 and Section 10; not the planar or discrete-subgaussian branches. |
| Cook (2018), Theorem 1.12, with its norm guard | Proposition 3.8 and, through that anchor, Section 8. |
| Cook deformed-square least-singular-value estimates, including conditional versions | Section 9 terminal/frame small-ball results and Section 8. |
| Nguyen bottom-singular-value fixed-index and overcrowding estimates | Section 9 interface control and Section 8. |
| Paper Proposition 3.2, full-block least-singular-value estimate | Proposition 3.8 and, through it, Section 8. This is a retained result of this paper, not an external-paper citation. |
| Two finite quantitative Section 4 pressure estimates, for calibration and the final ring | Concrete Section 5 endpoints; Section 6 requires them for each compact core. These remain endpoint hypotheses, not yet supplied by a closed Section 4-to-caller adapter. |

The table concerns the concrete endpoints described above; more general
conditional APIs may expose additional intermediate inputs, as recorded in
their chapter maps. A result proved elsewhere in the repository does not
automatically remove a parameter from an endpoint: Section 6's BBV-only Ginibre
route does not, by itself, remove the BC12/formula parameters still present
in Sections 3, 5, 8 and 10.

Tao–Vu replacement is a [proved source dependency](vendor/tao-vu-replacement/),
not a remaining literature hypothesis. The standard Lean foundations
`propext`, `Classical.choice` and `Quot.sound` are separate from all the
mathematical inputs above. An axiom audit checks logical dependencies;
it does not prove a theorem's explicit hypotheses or certify that its statement
matches every detail of the manuscript.

## Build

Lean is pinned to `leanprover/lean4:v4.33.0`, with mathlib fixed by the committed
manifests. Use `elan` and keep those manifests unchanged for reproduction.

```sh
git clone --branch main https://github.com/hanyi162013-Yihan/random-band-circular-law-lean.git
cd random-band-circular-law-lean
lake exe cache get
```

The cache command is only needed when matching compiled dependencies are
unavailable; it can download a large amount of data. Reading the source does
not require Lean or a cache download. Do not run `lake update` for routine
verification.

Choose the relevant target below, from the indicated directory. Each build
checks that target and its actual imports; a whole-repository build is not
required for a chapter change.

| Area | Working directory | Build command |
| --- | --- | --- |
| Section 3 | repository root | `lake build ShortRingAnchor` |
| Section 4 | repository root | `lake build CircularLawSection4` |
| Section 5 concrete endpoints | `section5/` | `lake build CircularLawSections56.Section5.PublishedSection3ConcreteEndpoint` |
| Section 6 BBV-only endpoint | `section6/` | `lake build CircularLawSection6.BBVOnlyProfileEndpoint` |
| Section 8, general and Rademacher | repository root | `lake build SubgaussianSection8 BernoulliSection8` |
| Section 9, algebra and small ball | repository root | `lake build BernoulliLinearAlgebra BernoulliSection9` |
| Section 10, real and complex endpoints | repository root | `lake build BernoulliSection10Source` |

The root Lake project loads Section 3 from `section3/` and the other root
libraries from their chapter directories. Section 5 depends on the root
project; Section 6 depends on Section 5. These two subprojects share the root
`.lake/packages` directory. Their explicit endpoint targets above are important:
building an umbrella alone need not include every separately published module.

## Verification and scope

Published verification records include target/import builds, placeholder
scans, kernel axiom audits and, where provided, public-signature checks and
regression proofs. Released proofs contain no `sorry`, `admit` or custom
mathematical axioms. Audits allow only the three standard Lean foundations
listed above; the explicit mathematical hypotheses remain visible.

For precise checked source revisions and reproducible audit commands, see:

- Section 3: [density integration](section3/HIGH_BAND_INTEGRATION.md) and
  [Proposition 3.8](section3/PROPOSITION38.md).
- Section 4: [coverage and audit commands](Section4/FORMALIZATION_MAP.md).
- Section 5: [concrete integration](section5/CONCRETE_SECTION3_INTERFACE.md).
- Section 6: [endpoint verification and main integration](section6/MAIN_INTEGRATION.md).
- Section 8: [Section 3 integration verification](Section8/SECTION3_INTEGRATION.md).
- Section 9: [deterministic map](Section9/FORMALIZATION_MAP.md) and
  [small-ball audit](Section9/SMALL_BALL_AUDIT.md).
- Section 10: [source, signatures and axiom audit](Section10/SOURCE_CONNECTION_AUDIT.md).

A successful scoped run certifies its recorded source and checked statements,
not all chapters at every later `main` commit. Historical logs and development
details remain in the chapter documentation rather than serving as a global
completion claim.

## Citation and licensing

Please cite the [paper](https://arxiv.org/abs/2609.01295) for its mathematical
results and record the repository commit when citing a formalization snapshot.

No repository-wide license has been selected. Lean and mathlib retain their
own licenses. Copied proof dependencies retain the license/provenance notices
in their source directories, including the Apache-2.0 notice for
`vendor/tao-vu-replacement/`.
