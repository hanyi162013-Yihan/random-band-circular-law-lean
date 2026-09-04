# Section 5: calibration, pressure lifting and circular-law conclusions

## Complex-density endpoint without pressure inputs — verified 2026-09-04 UTC

Import `CircularLawSections56.Section5.VerifiedComplexSection5Endpoint` and use
`PublishedSection3Concrete.indicator_complex_full_of_bbv`. Both finite pressure
contracts are now constructed from Section 4 on the actual matrix sample space;
BBV is the only external literature premise, besides the stated density,
moment, profile and bandwidth assumptions. The shift may be any fixed complex
number, with constants depending on it.

At `7136329`, the public target, 1118 axiom reports (all 874 public source
theorems included), the pressure-free calling example and eight module kernel
replays passed. See the [separate evidence and remaining scope](../PRESSURE_INPUT_MIGRATION.md).
The real-density endpoint and generic taper interfaces retain their documented
inputs. Earlier conditional endpoints remain available unchanged.

## Gaussian-source migration — verified 2026-09-04 UTC

The concrete endpoints and general source record no longer request either
BC12 estimate. The actual Gaussian law and both estimates are constructed
internally, with BBV retained for the negative moment. The whole public target,
1109 axiom reports (including all 865 named public source theorems) and six
module kernel replays passed at `d7d732c`. See the
[exact certificate](../GAUSSIAN_MIGRATION_VERIFICATION.md) and
[remaining-input map](../GAUSSIAN_INPUT_MIGRATION.md).
The two finite Section 4 pressure inputs still remain at this checkpoint.

## New concrete Section 3 integration — verified 2026-09-03

The actual fixed-atom short/calibration matrices, sample maps and both real/complex
Section 5 endpoints now call the checked Section 3 theorem internally. Their
[cloud build and transitive audit passed](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33725000131).
Import `CircularLawSections56.Section5.PublishedSection3ConcreteEndpoint`.
See [CONCRETE_SECTION3_INTERFACE.md](CONCRETE_SECTION3_INTERFACE.md) for the exact
uniformly positive indicator-profile scope and retained Section 4/literature
inputs. The broader taper/varying-atom interfaces below keep their documented
source boundary; they are not claimed to be automatically instantiated here.

## Original Section 5 package

This directory contains the checked Section 5 formalization for the combined
circular-law manuscript. The agreed Section 3 results, finite Section 4
estimates, and explicit model assumptions remain ordinary theorem hypotheses.
There are no new mathematical axioms or placeholder proofs.

See [SECTION5_COVERAGE.md](SECTION5_COVERAGE.md) for the declaration-level
coverage and exact input boundary.

[Section 5 verification on GitHub Actions](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/workflows/section5.yml)
builds this repository layout and runs the final audits. The original local
mathematical snapshot passed all checks below; the extra publication-layout
check was moved to GitHub at the user's request. See
[VERIFICATION.md](VERIFICATION.md) for the distinction and actual CI status.

## What is proved

- Real atoms on their original IID sample spaces, as well as complex atoms
  with bounded planar density.
- Indicator profiles and actual sampled, normalized polynomial taper profiles.
- Exact complementary exterior-power operator-norm identities, including
  degrees zero and the top degree, and uniform forward/inverse row costs.
- Uniform mesoscopic calibration, all-cell-count pressure lifting, remainder
  control, normalization and inactive-branch removal.
- Actual logarithmic-potential limits, Hilbert–Schmidt tightness, and ESD
  convergence against every bounded continuous real test function.
- Differences of the two models' spectral test integrals tend to zero under
  the specified whole-sequence marginal coupling; independent product
  realization is included. This is not total-variation convergence.

The comparison disk-diagonal model's energy and potential limits are proved
internally, not supplied as convergence assumptions.

## Build from this repository

The subproject depends on the parent repository and reuses its shared mathlib
package directory. It does not alter the parent's targets or existing chapters.

```sh
cd section5
LEAN_NUM_THREADS=1 lake --no-cache build CircularLawSections56
bash verify_section5.sh audit
```

With compatible local dependencies already available, the full extended check is:

```sh
bash verify_section5.sh all
```

For routine changes, keep the checkout, Lake configuration, and `.lake` caches
in place and use the first two commands above. Lake rebuilds affected dependency
chains; a changed upstream module can still cause many downstream rebuilds.
Replacing an accepted Section 3 input with a proved theorem through the same
interface is intended to isolate the mathematical changes in the adapter.
The `all` phase also repeats strict re-elaboration and the extra kernel replay;
it is a full verification option, not a requirement for every incremental edit.

The original local snapshot passed the 4079-job integrated build, strict
re-elaboration of all 65 extension modules, 15 regression proofs, selected and
exhaustive axiom audits (1561 declarations, 1215 theorems), and kernel replay of
all 118 Section 5 modules. The repository-layout build is recorded separately
in [DEPENDENCIES.md](DEPENDENCIES.md). Only the standard Lean foundations
`propext`, `Classical.choice`, and `Quot.sound` occur in the audit.

No mathlib, toolchain, compiled cache, or scratch files are included in this
directory. Do not run `lake update` merely to reuse an existing installation.

## Upstream boundary

[DEPENDENCIES.md](DEPENDENCIES.md) records repository paths, versions, and the
five small support modules under `upstream/`. [UPSTREAM_INPUTS.md](UPSTREAM_INPUTS.md)
distinguishes the existing Theorem 3.1 LSV project from the other accepted
Section 3 inputs. The presence of support code does not claim that all of
Section 3 has been proved.

The namespace `CircularLawSections56.Section6` contains earlier helper modules
required by this project. The Gaussian-profile continuation is the separate
[`section6/`](../section6/README.md) package; its endpoint and verification
scope are documented there, not inferred from these helper imports.
