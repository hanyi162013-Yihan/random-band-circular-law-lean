# Random band circular law — Lean formalization

Lean 4 formalization accompanying Yi Han's paper
[*The circular law for non-Hermitian random band matrices: optimal bandwidth,
periodic profile and discrete law*](https://arxiv.org/abs/2609.01295).

This repository contains checked proof chains for the paper's high-band
estimates, transfer and small-ball tools, and several circular-law conclusions.
The guide below follows the paper's section order and describes the public
interfaces in this checkout, subject to the migration status below.
It does **not** claim a complete formalization of every
statement in the paper. Exact hypotheses, quantitative variants and coverage
are recorded in the linked theorem maps and Lean declarations. Several endpoints
remain conditional on the [explicit mathematical inputs listed below](#inputs-still-assumed-at-public-interfaces).

**Verified Gaussian-source migration:** removal of external Gaussian inputs from
Sections 5, 6, 8 and 10 is tracked in
[GAUSSIAN_INPUT_MIGRATION.md](GAUSSIAN_INPUT_MIGRATION.md).
Section 3 and the later root/Section 5/Section 6 source-record reductions have
passed their cloud checks, including the Section 8/10 endpoints: 3327 axiom
reports, public-call regressions and 29 module kernel replays. See the
[exact commits and verification evidence](GAUSSIAN_MIGRATION_VERIFICATION.md).
The later [pressure-input construction](PRESSURE_INPUT_MIGRATION.md) has its own
verification evidence. It removes both finite pressure hypotheses from the
complex-density Section 5 endpoint and the Gaussian-profile Section 6 endpoint;
the earlier Gaussian-migration certificate retains its original scope.
The subsequent [fixed-shift verification](POINTWISE_Z_VERIFICATION.md) records
the everywhere-`z` logarithmic-potential endpoints, their exact remaining
interface, and the final cross-project build, axiom-audit and kernel-replay
evidence.

## Results in paper order

### Section 3 — High-band estimates and logarithmic-potential anchors

[`section3/`](section3/README.md) contains the concrete density endpoints for
Proposition 3.6 and the real-subgaussian full-block endpoint for Proposition 3.8.
The density proof connects the proved Theorem 3.1 to the actual cyclic matrix;
Hermitization counting and local bulk comparison are constructed from the
Gaussian-to-free comparison of
[Bandeira, Boedihardjo and van Handel (2023)][bandeira-2023].
Callers do not supply a least-singular-value or counting
conclusion in place of these proofs.

- Proposition 3.6: real or planar-complex bounded-density atoms with the stated
  moment assumptions; high-band regime `W ≥ M^(8/9 + ω)`, `0 < ω < 1/9`.
- Proposition 3.8: fixed real centered, variance-one subgaussian atoms,
  including discrete laws, for the three-neighbor full-block ring.
- Both give the normalized shifted log-determinant limit for every fixed
  complex shift, subject to their explicit inputs below. Their
  `proposition36_cyclicShortRing_withoutBC12` and
  `Proposition38.proposition38_withoutBC12` endpoints construct the Gaussian
  negative moment and log limit from the proved Ginibre source and BBV.

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
For complex atoms, import
`CircularLawSections56.Section5.VerifiedComplexSection5Endpoint` and use
`indicator_complex_logPotential_at_of_bbv` for the logarithmic-potential
statement at an arbitrary prescribed `z : ℂ`, or `indicator_complex_full_of_bbv` for
the full spectral conclusion, in
`CircularLawSections56.Section5.PublishedSection3Concrete`. Its finite
determinant/pressure and concentration contracts are constructed from the proved
Section 4 estimates on the actual matrix sample space. BBV is its only external
literature premise; constants may depend on any fixed complex shift.

The real endpoint `indicator_real_full_of_published_literature` remains in
`PublishedSection3ConcreteEndpoint`. It still retains two finite pressure
inputs and real geometric Brascamp–Lieb, in addition to BBV. Both branches
construct their Gaussian reference estimates internally.
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

Import `CircularLawSection6.VerifiedPointwiseProfileEndpoint`. The preferred
logarithmic-potential endpoint is
`CircularLawSection6.NoncompactProfile.gaussian_profile_logPotential_of_bbv`:
for every prescribed `z : ℂ`, the normalized shifted log determinant converges
in probability to the circular potential. The corresponding spectral endpoint is
`gaussian_profile_circular_law_of_pointwise_bbv`.
The comparison of
[Bandeira, Boedihardjo and van Handel (2023)][bandeira-2023] is its only external
literature premise, besides the stated profile and bandwidth assumptions.
Both finite Section 4 pressure estimates are constructed for each actual
clamped Gaussian core. Ginibre negative-moment tightness, logarithmic-potential
and spectral limits are derived internally; no separate Gaussian limit,
correlation-formula or pressure certificate is requested. The older two-field
`gaussian_profile_circular_law_of_bbv_sources` API remains available.
See the [exact input boundary and proof route](section6/BBV_ONLY_ENDPOINT.md).

Here and in Sections 3, 8 and 10, “every prescribed `z`” means a pointwise
theorem whose caller may choose any finite complex shift. It is stronger than
an almost-everywhere-in-`z` endpoint, but it does not assert one probability-one
sample event that works simultaneously for the uncountable set `ℂ`. The general
Tao--Vu replacement interface still asks for an almost-everywhere family; the
pointwise theorem supplies it there via `ae_of_all`.

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
proof. The estimates of [Cook (2018)][cook-2018] and
[Nguyen (2018)][nguyen-2018] remain inputs, together with Proposition 3.8's upstream
assumptions. No separate pressure, reset or high-band convergence certificate
is requested by the final endpoints. See the
[Section 3 connection and exact public inputs](Section8/SECTION3_INTEGRATION.md)
and [general proof map](SubgaussianSection8/STATUS.md).

### Section 9 — Deterministic algebra and local small-ball proofs

[`BernoulliLinearAlgebra`](Section9/README.md) proves the terminal polynomial
constructions, Block Floquet identity, Proposition 9.3, Corollary 9.4,
Jacobi/Hodge identities, deterministic boundary comparison, and the exterior
operator comparison used in Lemma 7.8. These results do not assume the
probabilistic estimates of [Cook (2018)][cook-2018] or
[Nguyen (2018)][nguyen-2018], or an RRQR theorem.

[`BernoulliSection9`](Section9/SMALL_BALL_README.md) provides the terminal,
conditional and arbitrary-frame small-ball deductions, together with interface
probability control. The estimates of [Cook (2018)][cook-2018] and
[Nguyen (2018)][nguyen-2018] are explicit inputs with fixed subgaussian ranges;
the structured-matrix estimate also fixes the profile range. RRQR selection and
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
pressure and replacement steps are connected internally. The comparison of
[Bandeira, Boedihardjo and van Handel (2023)][bandeira-2023] remains
an explicit input. The literal Gaussian law, negative moment and log limit
are constructed internally, without a BC12 premise. Real atoms additionally require the geometric form of the
[Brascamp–Lieb inequality (1976)][brascamp-1976].
Directional conditional-density, heterogeneous-law and general
finite-`(2+α)`-moment extensions are not included in these endpoints.
See the [real map](Section10/FORMALIZATION_MAP.md),
[complex map](Section10/COMPLEX_FORMALIZATION_MAP.md), and
[source-connection audit](Section10/SOURCE_CONNECTION_AUDIT.md).

## Inputs still assumed at public interfaces

The following are mathematical hypotheses, not custom Lean axioms.
Ordinary model conditions—independence, normalization, moments, density,
profile bounds and bandwidth growth—remain explicit as well, but are not
external theorem inputs.

Author–year citations link to the literature; full bibliographic details appear
in [References](#references). Lean module and theorem identifiers are preserved
verbatim so that the documented imports and commands remain executable.

| Undischarged input | Where it is required |
| --- | --- |
| Canonical Gaussian/free comparison: [Bandeira, Boedihardjo and van Handel (2023)][bandeira-2023], Theorem 2.8 | Section 3 anchors and the public Section 5, 6, 8 and 10 endpoints. |
| Real geometric Brascamp–Lieb inequality: [Brascamp and Lieb (1976)][brascamp-1976] | Real-density branches of Proposition 3.6, Section 5 and Section 10; not the planar or discrete-subgaussian branches. |
| Structured-matrix least-singular-value estimate: [Cook (2018)][cook-2018], Theorem 1.12, with its norm guard | Proposition 3.8 and, through that anchor, Section 8. |
| Deformed-square least-singular-value estimates: [Cook (2018)][cook-2018], Theorem 1.24, including the conditional versions used in the manuscript | Section 9 terminal/frame small-ball results and Section 8. |
| Bottom-singular-value fixed-index and overcrowding estimates: [Nguyen (2018)][nguyen-2018], Theorem 1.4 | Section 9 interface control and Section 8. |
| Paper Proposition 3.2, full-block least-singular-value estimate | Proposition 3.8 and, through it, Section 8. This is a retained result of this paper, not an external-paper citation. |
| Two finite quantitative Section 4 pressure estimates, for calibration and the final ring | Still explicit at the real-density Section 5 and generic conditional interfaces. Constructed internally at the preferred complex-density Section 5 and Gaussian-profile Section 6 endpoints. |

The table concerns the concrete endpoints described above; more general
conditional APIs may expose additional intermediate inputs, as recorded in
their chapter maps. The former BC12/Ginibre parameters are now constructed
at concrete call sites from the pinned
[Ginibre proof dependency](https://github.com/hanyi162013-Yihan/ginibre-correlation-identities-lean)
and BBV. The migration includes the adapters, not just an unused import;
chapter-by-chapter verification status is in the migration notice above.
Historical conditional APIs for squared-singular-law tests and Han's dense
Gaussian theorem remain available, but are not required by the preferred
Section 6 BBV-only endpoint. The full limiting squared-singular law is not
claimed as a new theorem of this migration.

The replacement principle of [Tao and Vu (2010)][tao-vu-2010], Theorem 2.1,
is a [proved source dependency](vendor/tao-vu-replacement/), not a remaining
literature hypothesis. The standard Lean foundations
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
| Section 5 concrete endpoints | `section5/` | `lake build CircularLawSections56.Section5.VerifiedComplexSection5Endpoint` |
| Section 6 Gaussian-profile endpoint | `section6/` | `lake build CircularLawSection6.VerifiedCorePressure` |
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

## References

- Bandeira, A. S., Boedihardjo, M. T., and van Handel, R. (2023).
  [Matrix concentration inequalities and free probability][bandeira-2023].
  *Inventiones Mathematicae* 234, 419–487.
  [arXiv:2108.06312](https://arxiv.org/abs/2108.06312).
- Bordenave, C., and Chafaï, D. (2012).
  [Around the circular law][bordenave-2012].
  *Probability Surveys* 9, 1–89.
  [arXiv:1109.3343](https://arxiv.org/abs/1109.3343).
- Brascamp, H. J., and Lieb, E. H. (1976).
  [Best constants in Young's inequality, its converse, and its generalization
  to more than three functions][brascamp-1976].
  *Advances in Mathematics* 20(2), 151–173.
- Cook, N. A. (2018).
  [Lower bounds for the smallest singular value of structured random matrices][cook-2018].
  *The Annals of Probability* 46(6), 3442–3500.
  [arXiv:1608.07347](https://arxiv.org/abs/1608.07347).
- Nguyen, H. H. (2018).
  [Random matrices: overcrowding estimates for the spectrum][nguyen-2018].
  *Journal of Functional Analysis* 275(8), 2197–2224.
  [arXiv:1709.06682](https://arxiv.org/abs/1709.06682).
- Tao, T., and Vu, V. (2010), with an appendix by M. Krishnapur.
  [Random matrices: Universality of ESDs and the circular law][tao-vu-2010].
  *The Annals of Probability* 38(5), 2023–2065.
  [arXiv:0807.4898](https://arxiv.org/abs/0807.4898).

[bandeira-2023]: https://doi.org/10.1007/s00222-023-01204-6
[bordenave-2012]: https://doi.org/10.1214/11-PS183
[brascamp-1976]: https://doi.org/10.1016/0001-8708%2876%2990184-5
[cook-2018]: https://doi.org/10.1214/17-AOP1251
[nguyen-2018]: https://doi.org/10.1016/j.jfa.2018.06.010
[tao-vu-2010]: https://doi.org/10.1214/10-AOP534

## Citation and licensing

Please cite the [paper](https://arxiv.org/abs/2609.01295) for its mathematical
results and record the repository commit when citing a formalization snapshot.

No repository-wide license has been selected. Lean and mathlib retain their
own licenses. Copied proof dependencies retain the license/provenance notices
in their source directories, including the Apache-2.0 notice for
`vendor/tao-vu-replacement/`.
