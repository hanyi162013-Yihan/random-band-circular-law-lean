# Section 6: Gaussian noncompact profiles

This continuation lives on `codex/section6-formalization`, imports the
verified `section5/` package, and shares the pinned Lean 4.33.0/mathlib
dependencies. No second mathlib checkout or large local download is needed.

## Main endpoint and verification status

The target declaration is
`CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law`
in [GaussianProfileTheorem.lean](CircularLawSection6/GaussianProfileTheorem.lean).
For a strictly positive continuous integrable BV profile of integral one
and positive bandwidths tending to infinity, it gives the circular law in
probability for the actual normalized Gaussian cyclic matrix. It does not
assume that the bandwidth/dimension ratio has a limit.

The complete 110-module source and 107 strict regression examples have been
submitted for cloud verification. Submission is not verification: the
latest fully successful historical checkpoint remains 80 modules and 93
regressions until a newer success is recorded in
[VERIFICATION.md](VERIFICATION.md).

This theorem is conditional on explicitly stated mathematical sources.
[SOURCE_BOUNDARIES.md](SOURCE_BOUNDARIES.md) lists their exact content:
Section 5's literal core endpoint, local Section 3 singular-value comparison,
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

These describe the mathematical content of the submitted source; the
verification ledger distinguishes complete green checkpoints from individual
modules compiled during development.

## Boundaries not concealed by the endpoint

The cited Han, BC12 and classical Ginibre results are not reproved here.
Section 3 is not silently implemented by declaring its input. The Section 5
endpoint remains an explicit manuscript-boundary input, rather than a final
parameter-free call to a bundled Section 3/4/5 instance.

The circular-law chain uses an inverse-moment/uniform-L2 route. The separate
`StieltjesHardEdge` module proves that a bounded Poisson transform implies
a linear hard-edge mass bound. It does not yet identify that transform bound
for the actual limiting singular law or prove the manuscript's logarithmic
layer-cake identity. Thus the conditional main endpoint is not a claim that
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
