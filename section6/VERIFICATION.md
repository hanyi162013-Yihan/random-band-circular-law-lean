# Section 6 continuation checkpoints — 2026-09-03

## Verified Han-free dense and actual Ginibre adapters

Commit: `ccdfb4c52fffd96f6facd4042529c6eb796ae590`.
[Run 33731702204](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33731702204),
job `100572881243`: success. Tree `833b43a71040e1661dcdafea37446ad9f5e24b1a`.

The narrow target `CircularLawSection6.GinibreFiniteFormulaSources` and its
transitive imports compiled successfully (4448 dependency-inclusive jobs,
mostly restored/replayed). The final `DenseProfileEndpoint` compiled in
2.8 seconds and `GinibreFiniteFormulaSources` in 2.3 seconds. The source-token
scan passed for 170 selected Lean files. `DenseGinibreAudit.lean` passed
for 145 declarations, allowing only `propext`, `Classical.choice`, and
`Quot.sound` transitively.

The checked chain constructs the actual dense profile V3/planar models,
its Section 3 least-value/counting/bulk/Proposition 3.6 inputs, and the
Han-free sparse/dense endpoint. It also identifies the actual scalar
Gaussian array with the imported Gaussian small-ball law, derives the
negative moment at `p=1/128` from BBV, and transports raw/negative/spectral
sources to the original Section 6 probability spaces. The finite-formula
adapter calls the existing root Section 3 logarithmic-limit theorem.

The new endpoint still has explicit BBV, actual Ginibre logarithmic and
squared-test sources, and finite Section 4 pressure hypotheses. Exact
Gaussian eigenvalue correlation formulas are not independently proved by
the finite-formula adapter. The identified BBV-only alternative remains
future work. See [DENSE_GINIBRE_ADAPTERS.md](DENSE_GINIBRE_ADAPTERS.md).

Only the development branch was updated. The root full-library workflow,
old independent Section 5 suite, and historical Section 6 full regression
suite were not rerun. No local Lean build or large local download was used.

## Verified concrete Section 3 interfaces — 2026-09-03

Commit: `c992bff30e9af6ddabcba04f113447cd48c27f20`.
[Run 33725000131](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33725000131),
job `100551912095`: success. Tree `1007e290b1dcb2d5cb054882bef2b40de5e19622`.
The targeted concrete Section 5 and Section 6 proof roots compiled, with
93 and 35 declarations respectively passing their transitive axiom audits.
The old full Section 5 suite and root full-library build were intentionally
not rerun. Core finite sampling, normalized matrices, ring and calibration
models are constructed by the concrete sources.

The newer Han-free/Ginibre-reuse modules passed their own targeted cloud
verification described above; that is separate from this older checkpoint.

## Verified 136-module integration with the shared density correction

Commit: `3ccc69511387b2e923c38f2184b140d3536a1c09`.
[Targeted run 33719510129](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33719510129),
job `100535572202`: success on 2026-09-03 UTC.
Exact tree: `365303dd85e171ba0cea47a6a48a4e6ed5195e8a`.

All 136 modules, 126 strict regression examples and both transitive audits
passed. There were 4430 dependency-inclusive build jobs. The Section 6 audit
checked 1305 declarations/1103 theorems, and the new Section 3-to-5 adapter
audit checked 126 declarations. Only the three standard foundations are allowed.
The root full-library workflow and independent Section 5 suite were not run.

The new `gaussian_profile_circular_law_of_published_sources` endpoint derives
the actual local CDF comparison internally. Exact Gaussian density, model and
sample laws, core weights and polynomial scales, limiting Ginibre hard edge,
logarithmic-potential identification and variance-scaled estimates are checked.
Finite Section 5 anchor-source records and the named literature hypotheses
remain explicit; this is not a claim of fully automatic concrete instantiation.

Concrete Gaussian instantiation exposed an incorrectly auto-implicit `top`
in Section 3's bounded-density record. The field is now the intended
`bound < (⊤ : ENNReal)`, with auto-implicit variables disabled locally.
See `../section3/INTEGRATION_CORRECTIONS.md`. The prior 122-module success
checked conditional theorems with that old premise; it did not prove the
premise could be instantiated. The actual Gaussian constructor and corrected
Section 3 dependency compiled in run 33717315989. The shared minimal fix is
`5c7be7bf2bd843ccdbfb45fdc0144e3dc7163278`, now an ancestor of both development
branches; Section 6's merge is `68ba63d60a070b08df071e8f3d0fe3edc608746f`.
Its density source is byte-identical to the already-corrected file.

In run 33718531306, `GinibreLimitingHardEdge` compiled in 6.7 seconds and
`GinibreLimitingLogPotential` in 2.8 seconds. They derive the actual limiting
linear CDF bound and logarithmic-potential identity from the explicit BBV,
bounded-test Ginibre and BC12 sources. Later joint-model/scaling adapters
failed in that historical run; the failures were corrected before the green
136-module run above, including the concrete density regression's noncomputable modifier.
No local Lean compilation or large download is used.

## Verified 122-module published Section 3 integration

Commit: `5301196f97a7de515d3602df4dc6a20924296f95`.
[GitHub run 33714847892](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33714847892),
job `100521740539`: success on 2026-09-03 UTC.
Exact tree: `61b42c046bf5f74971e075168df1c95bed162200`.

All 122 modules, 119 strict regression examples, both transitive axiom audits
and the 890-file source-token scan passed. The build completed 4415 jobs.
The Section 6 audit checked 1167 declarations/987 theorems. The separate,
narrow new-adapter audit checked 126 Section 3 integration declarations.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted transitively.
The already verified Section 5 full suite was not rerun.

The new endpoint `gaussian_profile_circular_law_of_published_section3` calls
the actual published Section 3 density theorems through Section 5. Its finite
model, fixed-atom, sampling and literature hypotheses remain explicit.
Finite coordinate, matrix, normalization and iid sampling adapters passed.
No short-ring convergence conclusion is inserted as an independent premise
at this new entry point. The local Section 3 CDF/weak-law and classical
Ginibre/Han fields elsewhere in the Section 6 source bundle remain visible.

The exact lower-logarithmic layer-cake identity, its Fubini justification,
absence of nonpositive mass, linear cutoff error, and logarithmic integrability
and cutoff convergence from a second moment are verified conditional on a
linear CDF bound. Subsequent work deriving that bound for the actual limiting
Ginibre law is outside this checkpoint.

## Verified 116-module direct Section 5 checkpoint

Commit: `d37151b820b450007747b679390135ce205ed0b0`.
[GitHub run 33710633794](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33710633794),
job `100509133540`: success on 2026-09-03 UTC.
Exact source tree: `789b8c41671a719a4ff6024e4ce15aa9d3940d15`.

All 116 modules, 113 strict regression examples and the transitive audit passed.
The build completed 4181 jobs; the audit covered 1103 declarations and 938
theorems using only the three standard foundations. The clamped-subsequence
adapter compiled in 4.7 seconds and the new final theorem in 2.4 seconds.

`gaussian_profile_circular_law_of_section34` now calls Section 5 internally.
The Gaussian atom transfer, globally clamped core weights, small-index fillers
and all subsequence identifications are proved. The remaining Section 5
premises are two finite quantitative Section 4 estimates and the Section 3
short/calibration anchors, not an assumed Section 5 core-limit conclusion.
Local Section 3 singular-law comparison and the classical reference/Han
inputs remain explicit. Subsequent integration of the newly checked Section 3
package is not covered by this historical run.

## Verified 110-module conditional circular-law checkpoint

Commit: `b4106b56f5a5a79086194e5bb5181e514ebc9644`.
[Dedicated GitHub run 33708812493](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33708812493),
job `100503706438`: **success** on 2026-09-03 UTC.
Exact source tree: `33c88726977ef960f2c7ba3b532b097e26a4f001`.

- All 110 modules plus umbrella compiled: 4160 dependency-inclusive jobs.
- The transitive audit passed: 999 declarations, 873 theorem declarations;
  only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
- All 107 strict regressions, the 643-file source-token scan, cache saving
  and verification-log retention passed.
- `SubsequenceSourceEndpoint` compiled in 3.1 seconds and the final
  `GaussianProfileTheorem` in 1.8 seconds.

The actual noncompact Gaussian-profile circular law is now proved conditional
on the explicit source bundle, without assuming a limit of bandwidth/dimension.
The proof constructs the compact comparison, finite-prefix transport, iterated
cutoff squeeze, sparse probability limit, actual model replacement, dense
threshold, and sparse/dense subsequence closure. Numerical bad-event dimension
equalities avoid expensive transport of whole dependent sample spaces.

This does not discharge the ordinary source hypotheses: Section 5's literal
core result, local Section 3 CDF/Ginibre singular-law inputs, classical Ginibre
raw/negative-moment/spectral limits, and Han's dense theorem. These are listed
in [SOURCE_BOUNDARIES.md](SOURCE_BOUNDARIES.md). The generic Stieltjes-to-linear
hard-edge adapter is also checked, but the limiting-law transform identification
and logarithmic layer-cake identity are not claimed. Subsequent direct Section 5
source-instantiation work is outside this historical checkpoint.

## Verified eighty-module checkpoint

Commit: `bbb5d66a6b81121240e6b7d3bfa87588bf5af168`.
[Dedicated GitHub run 33701538973](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33701538973),
job `100481688321`: **success** on 2026-09-03 UTC.

- All 80 modules plus umbrella compiled: 4130 dependency-inclusive jobs.
- The transitive audit passed: 859 declarations, 758 theorem declarations;
  only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
- All 93 strict regressions, the 613-file source-token scan, cache saving and log retention passed.

The actual coordinate/sample-law cutoff adapters, positive-log and lower-
correction second moments, normalized circular Ginibre reference, triangular
negative-moment comparison, and size-before-cutoff L1 control are checked.
The reference-cutoff squeeze does not assume convergence of a limiting
singular law. It does retain the two explicit BC12 probability inputs;
the audit does not discharge these hypotheses. The final source-to-core
instantiation, noncompact-profile theorem and replacement endpoint are
still being assembled. The manuscript's separate linear limiting-density
hard-edge estimate is not claimed as proved by this alternative route.

Subsequent coupled-CDF, unit-core upper sandwich, normalization error and
noncompact mean modules are not covered by this historical green run.

## Verified seventy-module checkpoint

Commit: `6b58072c4a29ca59db24e8c22a61353cdf78d09f`.
[Dedicated GitHub run 33699458299](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33699458299),
job `100475384470`: **success** on 2026-09-03 UTC.

- All 70 modules plus umbrella compiled: 4117 dependency-inclusive jobs.
- The transitive audit passed: 797 declarations, 702 theorem declarations;
  only `propext`, `Classical.choice`, and `Quot.sound` are permitted.
- All 84 strict regressions, source scanning, cache saving and log retention passed.

The seven new modules prove bounded probability-to-mean transport, compact
logarithmic clipping and energy-controlled upper tails, actual matrix cutoff
limits from squared-singular tests, normalized routed Gaussian energy,
periodic/full-band cutoff limit transfer and finite-CDF-to-expected-cutoff
comparison. Neither a reference limiting singular law nor an expected cutoff
comparison is silently supplied by the axiom audit: the precise Section 3
comparison and reference-model hypotheses remain mathematical inputs to connect.

The lower-cutoff uniform-second-moment and coordinate-reindexing additions
are subsequent work, not covered by this historical green checkpoint. The
new minimum-three-hour continuation remains active; the full Section 6
circular law is not yet claimed.

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
was paused at its agreed deadline; a new minimum-three-hour continuation has
since resumed. Neither checkpoint asserts mathematical completion.

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
