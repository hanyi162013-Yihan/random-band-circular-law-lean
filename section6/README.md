# Section 6: Gaussian noncompact profiles

This package proves logarithmic-potential convergence and the circular law
for normalized Gaussian cyclic matrices with a strictly positive, continuous,
integrable profile of bounded variation and integral one. Bandwidths are
positive and tend to infinity; their ratio to the matrix dimension need not
converge.

## Public endpoints

```lean
import CircularLawSection6.VerifiedPointwiseProfileEndpoint
```

The results are in `CircularLawSection6.NoncompactProfile`:

| Theorem | Conclusion |
| --- | --- |
| `gaussian_profile_logPotential_of_bbv` | The normalized shifted log determinant converges in probability to the circular potential for every prescribed `z : ℂ` |
| `gaussian_profile_circular_law_of_pointwise_bbv` | The empirical spectral integrals converge in probability to the circular law for every continuous compactly supported real test function |

The theorem uses the actual profile matrix and its Gaussian sample law.
Convergence holds separately for each fixed shift. There is no excluded set of
spectral parameters; a common probability-one event for all complex shifts is
not asserted. The circular-law proof supplies the general Tao–Vu theorem's
almost-everywhere hypothesis through `ae_of_all`.

## Mathematical input

The sole external literature premise of these endpoints is the explicit
`BBVComparisonInput` Gaussian/free comparison argument. The deterministic
profile and bandwidth conditions are ordinary model assumptions.

Both finite Section 4 pressure estimates are constructed for each clamped
Gaussian core. The Section 5 core models, sample-law transports, negative-moment
bounds and Gaussian reference limits are proved within the dependency chain.
Real-density and taper interfaces in Section 5 are separate conditional results.

## Proof route

1. Construct the Gaussian profile matrix, core/tail decomposition, normalization,
   mesh limits and variance bounds.
2. Prove determinant nonvanishing for each fixed shift, logarithmic
   integrability, concentration and exact energy identities.
3. Apply the Section 5 result to the actual compact core, with its finite
   pressure estimates and sample-law identifications.
4. Prove finite-CDF comparison, cutoff stability, inverse-moment lower-tail
   control and expectation comparison at each prescribed shift.
5. Transport through the finite prefix and reconstruct the sparse-profile
   mean and convergence in probability.
6. Combine sparse and dense subsequences for arbitrary bandwidth growth,
   then apply the proved Tao–Vu replacement principle.

The source includes reusable conditional comparison and limiting-law theorems
with their own explicit premises. The assumptions of the public endpoints above
are determined by their Lean signatures.

## Build and verification

This project depends on `section5/` and shares the root package directory.
Use the committed Lean 4.33.0 toolchain and dependency manifests:

```sh
cd section6
lake build CircularLawSection6.VerifiedPointwiseProfileEndpoint
lake env lean -DwarningAsError=true PointwiseAxiomAudit.lean
lake env lean -DwarningAsError=true PointwiseRegression.lean
```

The full library target is `lake build CircularLawSection6`.
[GitHub Actions](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/workflows/section6.yml)
runs the endpoint build, source checks, axiom audits and public-call regressions.
The [verification certificate](../POINTWISE_Z_VERIFICATION.md) specifies the
cross-project audit and kernel-replay coverage.

Public proofs contain no placeholders or custom axioms. Transitive axiom reports
permit only `propext`, `Classical.choice` and `Quot.sound`; the BBV comparison
remains a theorem hypothesis.
