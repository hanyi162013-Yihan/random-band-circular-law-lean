# Section 5: calibration, pressure lifting and circular-law conclusions

This package formalizes calibration, pressure lifting, logarithmic-potential
limits, energy tightness and empirical spectral convergence for band profiles.
It depends on the repository's Section 3 and Section 4 proofs.

## Concrete endpoints

For a fixed centered complex atom law with unit second moment, bounded planar
density and finite third absolute moment, use:

```lean
import CircularLawSections56.Section5.VerifiedComplexSection5Endpoint
```

The results are in `CircularLawSections56.Section5.PublishedSection3Concrete`:

| Theorem | Conclusion |
| --- | --- |
| `indicator_complex_logPotential_at_of_bbv` | Normalized shifted log-determinant convergence in probability for every prescribed `z : ℂ` |
| `indicator_complex_full_of_bbv` | Empirical spectral convergence against every bounded continuous real test function |

These endpoints use centered indicator-band profiles with fixed positive lower
and upper bounds, under the stated bandwidth assumptions. The matrices and
sample laws are constructed explicitly. The proof applies Section 3 internally
and derives both finite pressure estimates from Section 4 on the actual sample
space. The BBV Gaussian/free comparison is the only external literature input.

Convergence in probability holds separately for each fixed complex shift, with
constants allowed to depend on it. The statement does not assert a common
probability-one sample event for all shifts.

For real atoms, use
`PublishedSection3Concrete.indicator_real_full_of_published_literature` from
`CircularLawSections56.Section5.PublishedSection3ConcreteEndpoint`.
This endpoint takes BBV, real geometric Brascamp–Lieb, and two finite Section 4
pressure estimates, in addition to the model and bandwidth assumptions.
Both atom branches construct their Gaussian reference estimates internally.

The [concrete interface map](CONCRETE_SECTION3_INTERFACE.md) and
[coverage map](SECTION5_COVERAGE.md) give the exact declarations and assumptions.

## Proof coverage

- Real atoms on their IID sample spaces and complex atoms with bounded planar
  density; indicator profiles and sampled, normalized polynomial taper profiles.
- Complementary exterior-power operator-norm identities, including degree zero
  and top degree, and uniform forward/inverse row costs.
- Uniform mesoscopic calibration, pressure lifting for all cell counts,
  remainder control, normalization and inactive-branch removal.
- Logarithmic-potential limits, Hilbert–Schmidt tightness and empirical spectral
  convergence against bounded continuous real tests.
- Convergence of differences of spectral test integrals under the specified
  whole-sequence marginal coupling, including independent product realization.

The disk-diagonal comparison model's energy and potential limits are proved
internally. Taper and varying-atom theorems use the Section 3/4 hypotheses stated
in their declarations; the concrete indicator-profile endpoints do not cover
tapers whose lower bounds vanish.

## Build and verification

The subproject uses the pinned Lean 4.33.0/mathlib dependencies and shares the
root `.lake/packages` directory. With those dependencies available:

```sh
cd section5
lake build CircularLawSections56.Section5.VerifiedComplexSection5Endpoint
bash verify_section5.sh audit
```

For the full package and extended verification:

```sh
lake build CircularLawSections56
bash verify_section5.sh all
```

[GitHub Actions](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/workflows/section5.yml)
checks the repository layout, source integrity, public signatures and axioms.
The [verification certificate](../POINTWISE_Z_VERIFICATION.md) records build,
audit and kernel-replay coverage. Axiom reports permit only `propext`,
`Classical.choice` and `Quot.sound`; the mathematical inputs above are explicit
theorem hypotheses.

[DEPENDENCIES.md](DEPENDENCIES.md) describes the dependency layout and support
modules. The Gaussian noncompact-profile result is in the separate
[Section 6 package](../section6/README.md).
