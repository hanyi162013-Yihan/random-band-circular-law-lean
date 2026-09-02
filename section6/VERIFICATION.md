# Section 6 continuation checkpoint — 2026-09-02

## Verified sixty-three-module checkpoint

Commit: `a70292fe16ee856c49d1de272798ecacf8a2cf2b`.
[Dedicated GitHub run 33695166043](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33695166043),
job `100462369108`: **success** on 2026-09-02.

- All 63 modules plus umbrella compiled: 4107 dependency-inclusive jobs.
- The transitive audit passed: 743 declarations, 652 theorem declarations;
  only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
- All 74 strict regressions, the 596-file source-token scan, cache saving,
  and verification-log retention passed. Section 6 warnings are errors.

The new verified layer contains exact positive cutoff scaling, uniform
block-length averaging, and the explicit full-route identification with
the Section 4/5 matrix and its finite IID law. It constructs block
orthonormal singular bases and proves the exact dimension-weighted cutoff
identity. The actual periodicized matrix has that block decomposition;
finite atom second moment implies shifted cutoff integrability, and
sample-law transport gives the exact expected block average. The scaled
periodicization error is `r * sqrt(8H/m0) / a`, for every positive scale
and cutoff and planar-a.e. spectral parameter.

This is still a partial Section 6 result. Genuine compact squared-singular-law
comparison and fixed-cutoff convergence, the shifted-Ginibre limiting-law
hard-edge estimate, source-input/finite-prefix assembly, and the final
dense/sparse replacement endpoint remain unfinished. The six-hour continuation
was paused at its agreed deadline; that does not assert mathematical completion.

## Verified fifty-seven-module checkpoint

Commit: `7aac27608ac3c01df69267834182a31a8d549c46`.
[Dedicated GitHub run 33692718717](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33692718717),
job `100454825726`: **success** on 2026-09-02.

- All 57 modules plus umbrella compiled: 4101 dependency-inclusive jobs.
- The transitive audit passed: 680 declarations, 594 theorem declarations;
  only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
- All 64 strict regressions, source scanning, cache saving and log retention passed.

The contiguous full/block cyclic routes, balanced block partition, arbitrary
finite-index parameter nonvanishing, actual block IID marginal law, and
the normalized `8H/m0` energy / `sqrt(8H/m0)/a` cutoff errors are checked.
The subsequent scaling, uniform averaging, physical route-identification,
spectral block averaging and expected cutoff modules are covered by the
newer 63-module checkpoint above, not by this historical run. Compact cutoff
comparison/limit, hard-edge control, and final assembly remain unfinished.

## Verified fifty-four-module checkpoint

Commit: `fd5a513c6cf229c467bf3f37415e8270ebcf609a`.
[Dedicated GitHub run 33690819600](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33690819600),
job `100448909669`: **success** on 2026-09-02.

- All 54 modules plus umbrella compiled: 4098 dependency-inclusive jobs.
- The transitive audit passed: 622 declarations, 541 theorem declarations;
  only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
- All 59 strict regressions, source scanning, cache saving and log retention
  passed, with warnings as errors in Section 6.

This checks the canonical finite-band geometry and weights, actual fixed
positive scaling of the Section 5 probability-to-mean result, the varying
raw core mean with the actual limiting mass, cutoff normalization transport,
and the common-atom boundary routing energy. Section 5's literal probability
conclusion and the genuine fixed compact-cutoff limit remain explicit input
boundaries; no final Section 6 circular law is claimed.

The three subsequent modules, `ContiguousBlockRouting`,
`MatrixParameterNonvanishing`, and `PeriodicizationEnergy`, and the expanded
64-example regression suite are covered by the newer 57-module checkpoint above.

## Verified fifty-module checkpoint

Commit: `e177c08ea43c85343d80fc68ab260b54734b9423`.
[Dedicated GitHub run 33689098945](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33689098945),
job `100443457688`: **success** on 2026-09-02.

- All 50 modules and the umbrella compiled: 4094 dependency-inclusive jobs.
- The transitive audit passed: 584 declarations, 507 theorem declarations;
  only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
- All 53 strict regression examples, source scanning, cache saving, and
  verification-log retention passed. Warnings are errors in Section 6.

This adds actual expected cutoff stability and integrability, the Gaussian
tail-energy error, exact raw-potential scaling, and the expected raw-core /
raw-full / cutoff-core sandwich. The actual radial Gaussian mean is proved
monotone using rotation invariance and Jensen; varying-scale cutoff errors
are proved from the unit-core energy, including zero comparison scales.

Four subsequent modules, `CanonicalCoreBand`, `FixedScaleCoreBridge`,
`CanonicalCoreLimits`, and `RoutedBandCoupling`, and the 59-example regression
suite are now covered by the newer 54-module checkpoint above. They are not
part of this historical 50-module run. The full Section 6 theorem is still incomplete.

## Verified forty-three-module checkpoint

Commit: `f7ddb8382fda21a3e5697013e082a97ceab29bc7`.
[Dedicated GitHub run 33686124314](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33686124314),
job `100433942111`: **success** on 2026-09-02.

- All 43 modules and the umbrella compiled: 4079 jobs including dependencies.
- The transitive audit passed: 517 declarations, 443 theorem declarations
  including generated declarations, with only `propext`, `Classical.choice`,
  and `Quot.sound` permitted.
- All 46 strict regression examples passed. Section 6 warnings are errors.
- The source scan, dependency-cache save, and verification-log retention passed.

New verified results include the all-positive-dimension Gaussian estimate,
literal Section 5 probability-to-core-mean transport, actual Hermitian and
singular frame-overlap energy bounds, the `1/a` cutoff comparison on actual
shifted/scaled matrices, and cutoff measurability on the nonsingular event.
The latter uses the entrywise Borel structure, without a measurable choice
of singular vectors. A small local matrix-Borel/subtraction probe also passed.

The following seven modules were subsequent to this historical checkpoint:
`ExpectedCutoffComparison`, `CutoffIntegrability`, `GaussianTailCutoff`,
`RawPotentialScaling`, `GaussianUpperCutoff`, `VaryingCoreCutoff`, and
`GaussianRadialMean`. They and the 53-example regression suite are now covered
by the fifty-module checkpoint above, not by this historical 43-module run.
The full Section 6 theorem remains incomplete; see the README boundaries.

## Verified thirty-three-module checkpoint

Commit: `62b56b1a99377faf9e2a671c7c87b05d0f3a780a`.
[Dedicated GitHub run 33678501518](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33678501518),
job `100409067426`: **success** on 2026-09-02.

- All 33 modules and the umbrella compiled: 4067 jobs including dependencies.
- The transitive audit passed: 433 declarations, 367 theorem declarations
  including generated declarations; only `propext`, `Classical.choice`, and
  `Quot.sound` are permitted.
- All 40 strict regression examples passed, as did the source scan and
  verification-log retention. Section 6 warnings are errors.
- Dependency caches were saved successfully on GitHub. No large local
  dependency download was performed.

This extends the earlier checkpoint with exact Section 5 core identification,
Gaussian density/atom-log control, actual determinant cofactor fibers,
automatic global L², the uniform N log²(eN) variance estimate, cyclic-to-row
law transport, and normalized L¹/probability concentration for the full,
truncated, and normalized-core profile models. The dimension-at-least-two
restriction on this finite uniform estimate is harmless for these limits.

The one-dimensional extension, compact-core raw-mean bridge, and subsequent
spectral coupling work are not included in this checkpoint. In particular,
this is not a proof of the complete Section 6 circular-law theorem.

## Verified twenty-two-module checkpoint

Commit: `38f265785c8639566a5ab48e6c2079265012650a`.
[Dedicated GitHub run 33673278846](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33673278846),
job `100391788123`: **success** on 2026-09-02.

- All 22 modules and their entry point compiled in the publication layout:
  3996 build jobs including dependencies, with Section 6 warnings as errors.
- The transitive audit passed: 306 declarations, 259 theorem declarations
  (including generated declarations), with only `propext`, `Classical.choice`,
  and `Quot.sound` permitted.
- All 26 strict regression examples passed.
- The source-token scan and verification-log retention passed.
- Completed dependency builds were successfully cached on GitHub; the new
  restore/save split also retains useful compiled dependencies after a later
  failure without changing the validation result.

This adds actual sparse Riemann-mass limits and radius exhaustion, uniform
weight comparisons, exact limiting core/tail identities, invariant angular
averaging, and the expected Gaussian tail Jensen inequality. The latter's
log-integrability and nonvanishing premises are proved from the previously
available Section 5 / replacement estimates. The spectral parameter is
planar-a.e., not every `z`, which is sufficient for the final replacement step.

The model-identification and row-concentration batch was not covered by this
historical run; it is included in the thirty-three-module checkpoint above.

## Verified fourteen-module checkpoint

Commit: `0dce34d3de176151db96ee1da21bb18b57a7dfb6`.
[Dedicated GitHub run 33667008094](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33667008094),
job `100371135774`: **success** on 2026-09-02.

- All 14 Section 6 modules and the combined entry point compiled in the actual
  publication layout. Lean reported 3244 build jobs, including dependencies.
- New Section 6 modules treat warnings as errors.
- The transitive audit passed: 215 declarations, 173 theorem declarations
  (including generated declarations). Only `propext`, `Classical.choice`,
  and `Quot.sound` are allowed.
- All 20 strict regression examples passed, including even-size offset ties,
  the one-dimensional core, empty tails, Gaussian normalization, actual matrix
  independence, and zero-length quadrature.
- The repository placeholder-proof scanner passed.

This checkpoint now includes the literal Gaussian/profile model, finite
normalization and energy identities, product independence, tail rotations,
centered mesh identification, and actual BV quadrature estimates. It does not
yet prove the compact-core analytic inputs or the noncompact circular law.

The eight modules subsequently added to this historical checkpoint are now
included in the verified twenty-two-module checkpoint above.
These extend the mass-limit/comparability work with literal limiting mass
identities and the expected Gaussian tail Jensen inequality. The latter
reuses Section 5 / replacement's a.e.-parameter nonvanishing and local L²
estimates instead of postulating logarithmic integrability. The generic
`InvariantPhaseAverage` module has independently passed a strict local check.

No large local dependency download was performed; the cloud job uses its own
runner and cache. Local checks reused existing pinned dependencies.

## Earlier verified checkpoint

This record concerns the five new modules in `CircularLawSection6`, not all of
the manuscript's Section 6. See `README.md` for the remaining mathematical inputs.

Local checks against the existing pinned Lean 4.33.0/mathlib installation:

- All five modules elaborated successfully with `warningAsError=true`.
- Their combined `CircularLawSection6.lean` entry point passed the same check.
- The transitive axiom audit passed: 21 declarations, 19 theorems (including
  generated declarations). Only `propext`, `Classical.choice`, and `Quot.sound`
  are allowed. `verification/axioms.txt` now records the newer checkpoint.
- All seven regression examples passed with warnings treated as errors.
- The repository source-token scanner passed on all 538 current Lean files.
- The child manifest uses relative paths and reuses `../.lake/packages`.

These were targeted checks reusing local dependencies and compiled inputs, not
a fresh local rebuild of the whole Section 5 dependency tree. No large local
download was performed. The separate **Section 6 verification** GitHub workflow
builds this publication layout and repeats the axiom/regression checks; its
actual run conclusion must be consulted before claiming remote CI success.

The new lemmas use honest ordinary hypotheses for their external finite-size
and limiting inputs. Passing an axiom audit does not prove those hypotheses or
complete the Gaussian-profile circular-law theorem.
