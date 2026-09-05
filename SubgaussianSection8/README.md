# General subgaussian Section 8

This library proves logarithmic-potential convergence and the circular law for
every fixed real IID atom law with mean zero, second moment one and a finite
subgaussian MGF parameter. Bounded support, symmetry and density are not required.

## Public endpoints and assumptions

Import `SubgaussianSection8`. The results in [Results.lean](Results.lean) are:

| Theorem | Conclusion |
| --- | --- |
| `section8_subgaussian_log_potential` | Normalized log-determinant convergence in probability for every fixed complex shift |
| `section8_subgaussian_circular_law` | Circular empirical spectral convergence against every bounded continuous real test function |

The actual normalized full-block ring has dimension `N = (s + 3)W`.
The assumptions include positive widths and core-site counts, `W → ∞` and
`W / log N → ∞`.

The external estimates are Cook's deformed-square least-singular-value bounds
and Nguyen's bottom-singular-value bounds, with quantitative ranges covering
the fixed atom parameter. The high-band anchor is proved by the concrete
Section 3 Proposition 3.8, using its Proposition 3.2, Cook Theorem 1.12 and BBV
comparison inputs. The proof constructs the Gaussian reference law, pressure,
reset, seam and energy estimates internally.

See the [proof map](STATUS.md), the
[Section 3 connection](../Section8/SECTION3_INTEGRATION.md), and the
[Rademacher specialization](../Section8/README.md).

## Build and verification

This is a library in the root Lake project. With the pinned dependencies
available, run from the repository root:

```sh
lake build SubgaussianSection8 BernoulliSection8
python3 scripts/check_axioms.py --audit-file SubgaussianSection8/AxiomAudit.lean
lake env lean SubgaussianSection8/PublicSignatureAudit.lean
python3 scripts/check_placeholders.py --path SubgaussianSection8
```

[GitHub Actions](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/workflows/lean.yml)
builds the two Section 8 targets and their actual imports, then audits the
public conclusions and Section 3 connection. The
[verification certificate](../POINTWISE_Z_VERIFICATION.md) records the
cross-project checks. Transitive axiom reports permit only `propext`,
`Classical.choice` and `Quot.sound`.
