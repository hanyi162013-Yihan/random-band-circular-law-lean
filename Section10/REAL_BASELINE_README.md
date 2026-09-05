# Section 10: reusable real-density proof layer

`BernoulliSection10` contains the real-IID density proofs and the deterministic,
asymptotic and replacement lemmas used by the Section 10 endpoints.
Its generic assembly takes an explicit `SourceInputs.Section3Inputs μ L`
argument. The concrete real and planar entry points, which construct that
argument from the repository's Section 3 proofs, are documented in
[README.md](README.md).

The generic real results include `density_high_band_ring_log_limit`,
`density_long_ring_log_limit`, `density_ring_log_limit`,
`density_ring_energy_limit_of_second_moment` and `density_circular_law`.
They use the actual normalized cyclic matrix with dimension `N = (s + 3)W`,
a centered unit-second-moment real atom law with bounded density and finite
third absolute moment, and positive bandwidths tending to infinity.
The circular-law statement covers every bounded continuous real test function.

The [proof map](FORMALIZATION_MAP.md) describes the high-band anchor,
pressure calibration, reset and seam estimates, remainder control, energy
bound and spectral closure. Deterministic exterior algebra is supplied by
`BernoulliLinearAlgebra`; Tao–Vu replacement is a proved source dependency.

From the repository root:

```sh
lake build BernoulliSection10
```

The public umbrella is `import BernoulliSection10`. The audit modules are
`AxiomAudit.lean`, `AsymptoticAxiomAudit.lean` and `CompletionAxiomAudit.lean`
under `BernoulliSection10/`. Mathematical inputs are explicit theorem
parameters, and the logical axiom allowlist is `propext`, `Classical.choice`
and `Quot.sound`.
