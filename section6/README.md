# Section 6: Gaussian noncompact profiles

This continuation lives on `codex/section6-formalization`, imports the
verified `section5/` package, and shares the pinned Lean 4.33.0/mathlib
dependencies. No second mathlib checkout or large local download is needed.

## Main endpoint and verification status

The newest integration is pending fresh cloud verification. A concrete
Gaussian density constructor exposed an auto-implicit `top` in the imported
Section 3 density record. The user-approved correction is documented in
[Section 3 integration corrections](../section3/INTEGRATION_CORRECTIONS.md).
The 122-module checkpoint below predates that correction and verifies
conditional proofs, not satisfiability of the former density premise.

The target declaration is
`CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law_of_published_section3`
in [PublishedSection3GaussianProfile.lean](CircularLawSection6/PublishedSection3GaussianProfile.lean).
For a strictly positive continuous integrable BV profile of integral one
and positive bandwidths tending to infinity, it gives the circular law in
probability for the actual normalized Gaussian cyclic matrix. It does not
assume that the bandwidth/dimension ratio has a limit.

The complete 122-module checkpoint and 119 strict regression examples passed
[cloud verification](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33714847892)
at commit `5301196f97a7de515d3602df4dc6a20924296f95`.
The transitive audit checked 1167 Section 6 declarations, including 987 theorems,
and separately checked 126 newly added Section 3-to-5 adapter declarations.
See [VERIFICATION.md](VERIFICATION.md) for the exact scope.

This theorem is conditional on explicitly stated mathematical sources.
[SOURCE_BOUNDARIES.md](SOURCE_BOUNDARIES.md) lists their exact content:
finite Section 4 estimates and published Section 3 model/literature data for the internally called Section 5 theorem, local Section 3 singular-value comparison,
classical Ginibre inputs, and Han's Gaussian dense-bandwidth theorem.
No full-profile convergence or full-matrix cutoff comparison is assumed.
The axiom audit checks for forbidden axioms; it does not discharge hypotheses.

## What the continuation proves

- The actual Gaussian atom and matrix laws, core/tail decomposition,
  normalization, mesh and mass limits, and variance comparability.
- Gaussian determinant nonvanishing, logarithmic integrability and
  concentration, with all positive dimensions and the original sample laws.
- Jensen lower comparison, singular-value cutoff stability, exact energy
  identities, and upper/core/full expectation bounds.
- Concrete balanced periodicization, exact single-block equality in the
  short-dimension branch, weighted spectral averaging, and the boundary error.
- Local finite-CDF comparison to cutoff expectation convergence, uniformity
  over admissible block lengths, and the full normalized-core comparison.
- Finite-prefix transport of the literal Section 5 core result, inverse-moment
  lower-cutoff control, the iterated L1 estimate, and full-profile mean and
  probability convergence in the sparse regime.
- Actual profile/Ginibre replacement with both normalized mean energies
  exactly one, dimension-preserving subsequence fillers, the dense-source
  threshold, and sparse/dense recombination.

The 122-module checkpoint also verifies the direct published Section 3 calls,
sample-law and finite matrix adapters, and exact logarithmic layer-cake identity
with integrability and cutoff convergence derived from a linear CDF bound.
Subsequent limiting-law/model instantiations require their own verification.

## Boundaries not concealed by the endpoint

The cited Han, BC12 and classical Ginibre results are not reproved here.
Section 5 and the newly verified Section 3 density endpoints are called inside
the proof. The new source-facing endpoint takes finite model/sampling identities
and the published BBV/BC12 literature premises, not the short-ring probability
limit again. Real-density sources additionally retain geometric Brascamp--Lieb.
The broad older interfaces remain available for other source models.

The circular-law chain uses an inverse-moment/uniform-L2 route. The separate
hard-edge modules prove that a bounded Poisson transform implies a linear CDF
bound, then derive the exact logarithmic layer-cake identity, logarithmic
integrability and cutoff limit. Identification of that transform bound for the
actual limiting law is subsequent work, not covered by the 122-module run.
Thus the conditional main endpoint is not a claim that
every intermediate statement of Section 6 has been formalized line by line.

## Reproduce verification

```sh
cd section6
LEAN_NUM_THREADS=1 lake --no-cache build CircularLawSection6
lake --no-cache env lean -DwarningAsError=true AxiomAudit.lean
lake --no-cache env lean -DwarningAsError=true Regression.lean
```

`AxiomAudit.lean` checks every declaration in the new Section 6 namespace
and permits only `propext`, `Classical.choice`, and `Quot.sound` transitively.
Section 6 compiler warnings are errors. GitHub retains build, audit and
regression logs, and saves completed dependency builds even after a failed
new-module check.
