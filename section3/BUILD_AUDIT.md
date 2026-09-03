# Build and axiom audits

The Proposition 3.8 extension **passed locally at 03:44 UTC and on GitHub
at 04:11 UTC on 2026-09-03**:
250 Lean files, the ordinary build, and 351 exact axiom reports covering
340 distinct declarations. Its audit includes the final conditional
`ShortRingAnchor.Proposition38.proposition38`; see
[the current summary](audit/verification/summary.json) and
[Proposition 3.8 report](PROPOSITION38.md). Only `propext`,
`Classical.choice`, and `Quot.sound` occur. Explicit literature hypotheses
remain theorem arguments.

The cloud-verified proof-source commit is
`af0e8e80eee5db88f811b972ea79c359b89a8cea`.
[Successful run](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33712613763),
[durable CI summary](audit/github-verification-2026-09-03-proposition38.json),
[complete job log](audit/github-verification-2026-09-03-proposition38.log).

The preceding Proposition 3.6 integration **passed on GitHub on 2026-09-03 UTC**:
all 230 Lean files in the selected closure, normal `lake build`, and
271 axiom reports covering 260 distinct declarations. The verified source
commit is `79798346f1cc9dda9cfd0c5bf2c3044aea5162a9`.
[Successful run](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33702782802).
The exact status and remaining mathematical premises are recorded in
[Hermitization counting and Theorem 3.1](HIGH_BAND_INTEGRATION.md).
Only standard `propext`, `Classical.choice`, and `Quot.sound` dependencies
occur in the reports. The checks below are historical checkpoints.

The preceding checkpoint is [Concrete models and Proposition 3.6 integration](CONCRETE_MODELS_AUDIT.md):
both commands passed with **3432 jobs**, and the audit covers **196 distinct
declarations**. It constructs the actual cyclic/dense v3 models and removes
the source-facing `hBulk` premise. The remaining-model-adapter note in the
historical checkpoint below is therefore superseded.

# Historical checkpoint: actual matrix trace and v3 probability integration

Checked on 2026-09-02; audit completed before 22:01 UTC.

## Actual commands and results

- `lake build`: exit 0, **3423 jobs**.
- `lake build ShortRingAnchor.Audit`: exit 0, **3423 jobs**.

The audit emitted **163 distinct declaration reports**, each using exactly
`propext`, `Classical.choice`, and `Quot.sound`. There were no unexpected
axioms. The audit covers the previous 129 declarations, all **31 new
theorems**, and three important upstream declarations: actual-model
McDiarmid, specialized BVH Remark 6.13, and the canonical Gaussian companion.

- [Full build output](audit/matrix-stieltjes-build-2026-09-02.log)
- [Full axiom-audit output](audit/matrix-stieltjes-2026-09-02.log)
- [Audited declarations](ShortRingAnchor/Audit.lean)

The earlier 129-declaration smoothing audit is preserved in
[audit/stieltjes-smoothing-2026-09-02.log](audit/stieltjes-smoothing-2026-09-02.log).

## All nine new Lean files

| File under `ShortRingAnchor/` | New theorems | Role |
| --- | ---: | --- |
| [HermitizationResolventBlocks.lean](ShortRingAnchor/HermitizationResolventBlocks.lean) | 5 | Inverse block equations, equal diagonal traces, Gram equation |
| [HermitizationSingularTrace.lean](ShortRingAnchor/HermitizationSingularTrace.lean) | 7 | Right singular-vector calculation and exact normalized trace |
| [MatrixStieltjesSmoothing.lean](ShortRingAnchor/MatrixStieltjesSmoothing.lean) | 2 | Actual inverse instantiation and matrix squared-CDF smoothing |
| [CompactStieltjesGoodEvent.lean](ShortRingAnchor/CompactStieltjesGoodEvent.lean) | 3 | Common finite-grid event, union bound, reference imaginary-part bound |
| [LocalBulkPolynomialScales.lean](ShortRingAnchor/LocalBulkPolynomialScales.lean) | 6 | One explicit exponent and height, scale arithmetic, rate convergence |
| [MatrixLocalBulk.lean](ShortRingAnchor/MatrixLocalBulk.lean) | 2 | Actual matrix Lipschitz estimate and CDF bound on the grid event |
| [V3PointwiseProbability.lean](ShortRingAnchor/V3PointwiseProbability.lean) | 3 | Canonical v3 (3.11) and actual McDiarmid failure probability |
| [V3MatrixLocalBulk.lean](ShortRingAnchor/V3MatrixLocalBulk.lean) | 1 | Actual-model probability of the common compact event |
| [Lemma35FromV3.lean](ShortRingAnchor/Lemma35FromV3.lean) | 2 | Vanishing failure budget and the exact named Lemma 3.5 interface |

Together these files contain 905 lines and 31 theorems. Each theorem has
a source/proof-step comment. The two log files above are also new.
Existing files updated are `ShortRingAnchor.lean`, `ShortRingAnchor/Audit.lean`,
`README.md`, `RADIUS_SHORTCUT.md`, `UPSTREAM.md`, and this report.

Five vendored files received only narrowed tactic imports:
`HermitianStieltjes`, `RowReplacement`, `ResolventPerturbation`,
`BVH/EntryResolvent`, and `BVH/ProductLindeberg`. Their theorem statements
and proof bodies were unchanged; all now compile in the integrated closure.
See [UPSTREAM.md](UPSTREAM.md) for provenance.

## Fully checked matrix identities and internal deductions

`matrix_stieltjesTrace_eq_symmetric_singularValues` proves the actual
Hermitization inverse trace equals the empirical transform of the symmetric
shifted-singular-value family. It assumes only a square complex matrix and
an upper-half-plane parameter. No SVD, trace formula, Gaussian law, or
nonsingularity conclusion is assumed.

The proof obtains equal diagonal inverse-block traces and diagonalizes the
lower block using the existing right singular-vector basis. It includes
zero singular values. The matrix smoothing theorem then specializes the
previous finite-spectrum theorem without a new spectral interface.

The compact event simultaneously yields transform comparison and the
reference empirical imaginary-part bound `3`. The latter comes from the
proved canonical free-transform norm bound and actual resolvent continuity,
not an assumed free-law density.

## Exactly which new theorems are conditional on BBV?

Four of the 31 new theorems explicitly accept the named BBV comparison:

- `v3_formula311_canonical_on_good`;
- `v3_pointwise_comparison_bad_le`;
- `matrixLocalBulkGood_bad_le`;
- `lemma35LocalBulkComparisonInput_of_v3_models`.

The other 27 new theorems have no external literature-comparison premise;
generic deterministic bounds and model data, where needed, remain explicit.

`CanonicalBBVAt` is an abbreviation of the existing centralized
`External.BBVTheorem28GaussianFreeHypothesis`, instantiated at the actual
canonical circularized matrix. It does not assert that BBV is proved.
As documented upstream, this specialized BBV interface also contains the
identification of its abstract free endpoint with the canonical scalar
Dyson solution.

The final constructor takes two actual v3 models, a common finite
third-moment budget, dimensions tending to infinity, and bandwidths
eventually at least `N^epsilon`, for `epsilon > 0`. The models need not
be independent of each other. With

```text
e = min(epsilon,1),   v = N^(-e/16),   zeta = e/64,
```

it proves the named local squared-CDF conclusion `O_P(N^(-zeta))`.
For each fixed `R >= 0`, its explicit common event has failure probability
at most `2(2R+4)N^(-8)`; eventually on this event the CDF distance is at most
`((8R+72)/pi)N^(-zeta)`. The exponent is common to all grid points.
There is no radius-five restriction and no bound on the arbitrary fixed shift.

McDiarmid, the specialized BVH comparison, Gaussian realization, diagonal
correction, net interpolation, smoothing and asymptotic probability
postprocessing are supplied by checked proofs, not additional interfaces.

## Remaining work and shortest next path

The requested actual-matrix trace and v3-model probability chain is
complete. This is not an unconditional proof of all Proposition 3.6.

The source-facing cyclic/dense theorem still accepts a generic `hBulk`.
The shortest next adapter is to package its specific atom arrays as v3
models, identify their matrices and bandwidths, and pass the new constructor
as `hBulk` (using the same positive exponent for each fixed cutoff).
No further smoothing theorem is needed.

The other previously documented work remains separate: completing the
published Theorem 3.1 model/cutoff adapter, connecting Gaussian least-value
and count bounds to the BC12 negative-moment route, and retaining the
explicit finite Ginibre formulas for its full-logdet route. The real-density
high-band branch's Brascamp--Lieb premise must also remain visible unless
separately discharged. See [README.md](README.md).

## Build hygiene

Source searches found no proof placeholder, `admit`, `unsafe`,
custom `axiom`, `native_decide`, or kernel-check bypass in project or
vendored Lean sources. The only matching `sorry` word is inside an
upstream documentation phrase. Resource-only heartbeat limits and
`-j 1` do not change soundness.

The build replays informational/style warnings; there are no final
build errors. No large dependency cache was downloaded, no project cache
was deleted, and neither the manuscript nor the original proof projects
was edited during this integration. Passing the axiom audit verifies
conditional deductions; it does not discharge their explicit BBV or
finite-formula parameters.
