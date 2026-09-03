# Proposition 3.6: finite-moment short-ring anchor

This is a standalone Lean 4 + mathlib reconstruction of Proposition 3.6 in
*The circular law for non-Hermitian random band matrices: optimal bandwidth,
periodic profile and discrete law* (the supplied combined manuscript,
Proposition 3.6 and formulas (3.7)--(3.14)).

The source result says that for the cyclic short-ring matrix `H_{M,W}`, an
atom satisfying Assumption 2.1, `0 < omega < 1/9`,

```text
M,W -> infinity,       W >= M^(8/9+omega),
```

and every fixed `z : ℂ`,

```text
(1/M) log |det(H_{M,W} - z I_M)| -> U_circ(z)
```

in probability.  There is no restriction such as `|z| <= 2.5` in this
formalization: `z` is arbitrary and fixed, and constants may depend on `z`.

## Main checked theorems

Both density endpoints have passed the complete build and kernel audit.
They remain conditional on BBV and the two named BC12 inputs. The real-density
branch also retains the copied theorem's geometric Brascamp--Lieb premise.
Neither a counting conclusion nor a least-singular-value conclusion is
supplied as an extra input to these endpoints.

`ShortRingAnchor.proposition36_cyclicShortRing_planar_from_published_theorem31`
is the most concrete checked planar-density theorem: its target matrix is exactly the
cyclic model (3.1), and its comparison matrix is exactly an entrywise
`M^(-1/2)` normalized dense process.  Its bandwidth exponent is definitionally
`8/9 + omega`, and it records `0 < omega < 1/9`.  It assumes the cited
random-matrix conclusions listed below and proves the determinant convergence
conclusion. It constructs the Hermitization counting event from the actual
v3 probability estimate, and constructs the least-value event by applying the
user's copied and checked Theorem 3.1. Neither `hCount` nor `hLSV` is an input.
Its Lemma 3.5 comparison is derived from the actual i.i.d. arrays and the
explicit BBV comparison, rather than assumed as `hBulk`.
The earlier `proposition36_cyclicShortRing_of_source_scales` remains available
as a more general assembly theorem. In particular the new endpoint discharges,
inside Lean:

- feasibility and exponent arithmetic in (3.9);
- the exact all-cutoff Hermitization count `6 M (2r)` above
  `B^(-1/8) M^tau`, on a common event with eventual failure probability
  at most `4 M^-8`;
- the planar Theorem 3.1 model/law adapter, numerical reindexing along
  arbitrary growing dimensions, exact substitution `t=M^-2`, and removal
  of the HS cutoff using second moments and Markov;
- the full v3 model of the actual cyclic and normalized dense arrays,
  including entry laws, independence of the deterministic off-band zeros,
  and both row and column variance normalization;
- exact bandwidths `(max q_s)^(-1)` and `M`, a common third-moment budget,
  and the eventual scale `M^(beta/2) <= B` from `W >= M^beta`;
- Lemma 3.5 for these concrete arrays, conditional only on the named BBV
  comparison, with one fixed CDF exponent `zeta = beta/128`, where
  `beta = 8/9 + omega`; no v3 model or local CDF conclusion is assumed;
- the complete finite-sum hard-edge deduction (3.10);
- the local, not global, CDF comparison postprocessing on `[0,R^2]` in
  (3.11)--(3.12);
- both the literal raw-tail inequality and the clipped-log correction needed
  for (3.13), including Markov and the iterated `M -> infinity`, then
  `R -> infinity` argument;
- the logarithm-versus-negative-power inequality and all of (3.14) after the
  named BC12 negative-moment premise;
- the low/middle/high logarithmic decomposition and final approximation
  argument;
- the determinant/product-of-singular-values bridge, including the null-set
  handling required by Lean's total convention `Real.log 0 = 0`;
- `sum_j s_j(A)^2 = sum_ij |A_ij|^2` and the exact centered-entry expectation
  `C + ||z||^2`, so no separate upper-edge random-matrix moment input remains;
- construction of those centered row-moment hypotheses for the genuine cyclic
  short-ring matrix and for a normalized dense matrix directly from the
  moment part of Assumption 2.1; in particular, finite third moment is proved
  to imply all first/second integrability used here (independence is not
  needed for this step);
- the cutoff comparison
  `b(H)^(-1/8) M^tau <= C0^(1/8) M^(tau-beta/8)` and the harmless eventual
  removal of the cap `min 1`;
- the Hermitization count bridge needed to use Corollary 3.5: a singular
  vector with `s <= r` supplies a linearly independent Hermitization
  eigenvector in `[-r,r]`, and the source-facing adapter turns a
  `C M (2r)` Hermitian count into a `(2C) M r` singular-value count;
- high-probability replacement of singular samples.  Theorem 3.1 itself
  forces the short-ring shift to be nonsingular on its good event, so the
  main theorem no longer assumes short-ring a.s. nonsingularity.  The dense
  comparison is proved a.e. nonsingular from independent atom copies and
  the real/complex density alternative of Assumption 2.1;
- the former geometric-measure interface: every nonzero multivariate
  complex polynomial has a null zero set for a finite product of
  sigma-finite nonatomic coordinate measures, in particular complex
  Lebesgue measure.  The proof uses one-variable finite root sets and
  finite-dimensional Fubini induction;
- bounded marginal densities imply absolute continuity, and independence
  turns marginal absolute continuity into joint absolute continuity.
  The real-density branch is handled separately and correctly: a real
  atom is not asserted to have a planar complex density.

## The geometric-measure proof

Write a nonzero polynomial in the last variable as `sum_k Q_k(x) t^k`,
and choose a nonzero coefficient polynomial `Q_k`.  By induction its zero
set in the remaining coordinates is null.  Away from that set, the
one-variable polynomial in `t` is nonzero and hence has finitely many roots.
Each such finite set has measure zero for a nonatomic marginal.  Fubini
then proves the product zero-set statement; coordinate equivalences handle
arbitrary finite index types.

For independent atoms their joint law is the product of their marginal
laws.  Either density alternative gives nonatomic complex marginal laws:
in the real-density case, a complex singleton is contained in a real-part
level set of measure zero.  The determinant polynomials for full matrices
and for the active cyclic-band coordinates are nonzero by explicit diagonal
witnesses.  This gives a.e. nonsingularity for **each fixed** `z`, not one
event on which the determinant is nonzero for all `z` simultaneously.

## Explicit literature inputs in the current main theorem

The most concrete endpoint has the following explicit literature-conclusion
parameters, not Lean axioms. The proved reductions below can supply some of
these from more primitive inputs:

1. the centralized BBV Gaussian-to-free comparison, instantiated for the
   canonical circularized cyclic and dense profiles. The cyclic comparison
   covers the vertical counting grid as well as horizontal smoothing lines;
   Lemma 3.5 itself is no longer an input;
2. the BC12 bounded negative singular-value moment; a proved shorter route
   now reduces it to a polynomial least-value bound and mesoscopic counts;
3. the BC12 full normalized Ginibre logarithmic-determinant convergence,
   retained in the generic assembly but now derivable from explicit finite
   formulas by the separate module described next.

The upper second-moment, Hermitization count, and planar Theorem 3.1 conclusions
are no longer on this list. The concrete theorem
asks for two fixed atom laws satisfying the moment part of Assumption 2.1
and measurable independent copies at each size. These are ordinary ensemble
data, not external probability estimates. The old marginal moment packages
are derived by equality of laws. One real/complex density assumption on the
dense source atom is transported to all entries. Lean then derives dense
a.e. nonsingularity, including the normalization by `sqrt M`.
No independence between matrix sizes or between the two ensembles is assumed.

The lower-level generic matrix theorem still accepts nonsingularity in
probability so that it can be reused beyond independent-density models.
The concrete source-facing theorem no longer asks for that premise.

## BC12 logdet from known finite Ginibre formulas

`BC12.ginibre_matrix_logdet_convergesInProbability_of_formulas` proves the
exact full matrix-logdet convergence for arbitrary fixed `z`, conditional
only on the named finite correlation and projection formulas in
`BC12/KnownFormulas.lean` (besides the underlying measure, matrix sequence,
and dimension growth).  It constructs an eigenvalue enumeration internally.
There is no assumed circular law, variance bound, logarithmic tail bound,
disk-potential identity, or nonsingularity conclusion in this theorem.

The internal deductions include uniform Gaussian domination of the finite
one-point densities, their a.e. circular limit, unbounded-test dominated
convergence, a `2/n` variance estimate, Chebyshev, Gaussian integrability of
the shifted logarithm and its square, the explicit disk-potential
calculation, and the determinant/eigenvalue bridge.  The first-moment
formula itself proves avoidance of a fixed eigenvalue.

This is a **conditional formula-based theorem**, not a derivation of the
Ginibre eigenvalue formulas from Gaussian entries.  The external boundary
contains exact first-/second-moment and kernel-projection identities with
their finite-integrability clauses, all as explicit theorem parameters.
See [BC12_PLAN.md](BC12_PLAN.md) for the full boundary, theorem map, and list
of all eleven new source files.  The theorem can be passed directly as
`hBC12Full` to the existing Proposition 3.6 assembly.

## Deliberately not claimed

Both density endpoints now discharge the Theorem 3.1 least-value input and
the Hermitization counting input. The real-density endpoint
`proposition36_cyclicShortRing_from_published_theorem31` has also passed its
local build and retains the upstream `RealFiniteGeometricBrascampLieb` premise;
see [HIGH_BAND_INTEGRATION.md](HIGH_BAND_INTEGRATION.md) for its verification status.
The shifted Ginibre negative-moment input is not yet discharged from its
most primitive model assumptions.
Lemma 3.5 is now supplied internally from atom data and the named BBV
comparison; BBV itself is not proved. The published planar Theorem 3.1 proof
is copied under `Vendor/` and applied to the actual cyclic matrix law.
See [UPSTREAM.md](UPSTREAM.md)
for all source paths, revisions, licenses, and compatibility changes. The logdet
BC12 target is now proved **from those exact formulas**, independently of
the negative-moment target.  Dense normalization and the moment-copy
package alone still do not assert Gaussianity or imply these formulas.

For the negative-moment target, the shorter route now has a deterministic
summation proof in `BC12/NegativeMomentCounting.lean`. A common lower bound
`ell` and the count `F(t) <= C t` for `a <= t <= 1` imply
`mean s^(-p) <= 1 + Cp/(1-p) + Ca ell^(-p)`. In particular, `ell=N^(-4)`
and `a=N^(-1/16)` admit the explicit exponent `p=1/128`. The conversion of
these bounds on high-probability events into tightness is also included.
The remaining work is to connect the actual shifted Gaussian law and the
vendored least-value/count theorems to those events. No unshifted Laguerre
density is substituted for the shifted singular-value distribution.

## Why the radius-five bound is not an obstacle

Lemma 3.5 needs a horizontal line at height `v_n`, not the old two-dimensional
radius-five net. The v3 pointwise estimate (3.11) has no real-part restriction.
`LocalStieltjesNet.lean` constructs a floor grid on every `[-R,R]`, proves its
cover and cardinality, Lipschitz interpolation, and the probability union bound.
`ExplicitStieltjesRate.lean` exposes the common exponent `c/32` in (3.11),
uniform in all admissible `B,v`; one must not extract an exponent separately
at each point of a dimension-dependent grid.

`HorizontalPolynomialNet.lean` specializes to spacing `N^(-2)`: at most
`(2R+2)N²` points and a union-bound cost `(2R+2)N^(-8)` for pointwise tails
`N^(-10)`. The manuscript height `v >= N^(-1/8)` bounds the Stieltjes
Lipschitz constant by `N`, so interpolation preserves every exponent
`0 < d <= 1`. This concerns each fixed `R`, not arbitrary growing radii.
`HorizontalComparisonProbability.lean` combines the pieces into the
explicit bound `Q(2R+2)N^(-8)` for the event that the compact comparison
exceeds `4N^(-d)`; `Q=2` accounts for two pointwise ensemble estimates.

The deterministic Stieltjes-to-CDF smoothing step and its actual-matrix v3
constructor are supplied by the modules below. The new concrete Proposition
3.6 endpoint supplies the generic assembly's `hBulk` internally, using the
proved cyclic/dense model constructions.
BBV is needed at the new grid points but is the same named external
comparison, not a new literature theorem.

## Compact Stieltjes control to the squared-singular-value CDF

`squaredCdfDistanceOn_le_of_stieltjes` proves the exact finite-spectrum bound

```text
sup_{0 <= x <= R²} |F_{s²}(x) - F_{t²}(x)|
  <= ((2R+10) E + (8C+8) sqrt(v)) / pi.
```

Its premises are `R >= 0`, `v > 0`, `3 sqrt(v) <= 1`, `E >= 0`, and on the
compact line segment `u in [-R-1,R+1]`:

- the Stieltjes transforms of the symmetric finite spectra `(+s,-s)` and
  `(+t,-t)` differ by at most `E`;
- the imaginary part of the second transform is at most `C`.

No density hypothesis, spectral-tail estimate, Gaussian formula, or
nonsingularity assumption is used. The proof includes the arctangent
primitive, both Poisson smoothing inequalities, finite-sum integration,
endpoint-window mass control from the empirical transform itself, and the
identity between the symmetric interval mass and the CDF of squared values.
Zero values and atoms exactly at the endpoints are included.

`lemma35LocalBulkComparisonInput_of_stieltjes` supplies the exact named
`Lemma35LocalBulkComparisonInput` from these estimates on events of probability
tending to one and deterministic bounds by a common rate for both `E_n` and
`sqrt(v_n)`. Thus the probability postprocessing is proved as well.

### Actual matrix trace and canonical v3 probability connection

`matrix_stieltjesTrace_eq_symmetric_singularValues` identifies the genuine
normalized resolvent trace with the symmetric shifted-singular-value
transform for every square complex matrix and every upper-half-plane
parameter. It uses block inverse identities and the right singular-vector
basis. It assumes neither an SVD interface nor invertibility of the
original matrix; zero singular values, including the zero-dimensional
identity, are covered. Only the probability/CDF estimates subsequently
restrict attention to eventually positive dimensions.

`lemma35LocalBulkComparisonInput_of_v3_models` produces the exact existing
`Lemma35LocalBulkComparisonInput` for two actual `RandomMatrixModelV3`
ensembles on a common probability space. They may be dependent on each
other. For dimensions `M_k -> infinity`, bandwidths eventually at least
`M_k^epsilon`, `epsilon > 0`, and a common finite third-moment budget, set

```text
e = min(epsilon,1),   v_k = M_k^(-e/16),   zeta = e/64.
```

The constructor obtains the local squared-CDF rate `O_P(M_k^(-zeta))`
for every fixed `R >= 0` and arbitrary fixed `z`. On its explicit grid
event it proves the deterministic bound

```text
CDF distance <= ((8R+72)/pi) M_k^(-zeta),
```

eventually in `k`; the complementary event has probability at most
`2(2R+4) M_k^(-8)`. The common exponent is chosen before the grid point.
The bound on the comparison ensemble's imaginary Stieltjes transform is
derived on the same event from the proved free-transform norm bound and
resolvent continuity; it is not a new density or probability assumption.

The **only external comparison conclusion in this constructor** is
`CanonicalBBVAt` for the two canonical circularized ensembles along the
chosen horizontal lines. This is a transparent specialization of
`External.BBVTheorem28GaussianFreeHypothesis` in the centralized vendored
`External/VanHandel.lean`. It includes the Gaussian-to-canonical-free
identification exactly as documented there. It is an explicit argument,
not a proved BBV theorem or an axiom. McDiarmid, the specialized BVH
Remark 6.13 comparison, Gaussian realization, diagonal correction,
compact interpolation, and smoothing are all supplied internally.

`lemma35LocalBulkComparisonInput_cyclic_dense` now specializes this result
directly to the actual atom arrays. It constructs `cyclicV3Model` and
`denseV3Model`, proves the bandwidth identities, and absorbs the fixed
weight-profile constant by taking `epsilon = beta/2`. Thus for
`0 < beta <= 2` the CDF exponent is exactly `beta/128`. It supplies `hBulk`
to `proposition36_cyclicShortRing_of_atom_copies_and_bbv` at every fixed
cutoff with this same exponent. These two BBV instances do not require
the ensembles to be independent.

The common comparison constant is the maximum of an arbitrary fixed
`comparisonConstant` and the explicit moment budget
`max 8 (max(E|atomA|³, E|atomG|³) + E|standard complex Gaussian|³)`.
Thus no numerical value is guessed for BBV's absolute constant, and no
additional uniform-third-moment hypothesis is imposed on the matrix sequence.

This does **not** remove the other Proposition 3.6 inputs. The published
planar Theorem 3.1 is now integrated; connecting the Gaussian least-value/count
inputs and retaining the stated finite Ginibre formulas remain distinct tasks. No unconditional
Proposition 3.6 or BBV formalization is claimed.

`HilbertSchmidtCutoffRemoval.lean` separately gives a short way to remove the
cutoff in the published Theorem 3.1: tightness plus convergence of every
fixed-cutoff bad probability suffices. Applying Markov to `HS²/N` needs only
the second moment already computed here, not an additional concentration law.
This Hilbert--Schmidt cutoff is distinct from the spectral radius in Lemma 3.5.

See [RADIUS_SHORTCUT.md](RADIUS_SHORTCUT.md) for the precise quantifier order,
the source formula used, and the proved Poisson-smoothing estimate.

The high-band project's **real-density** branch also exposes
`RealFiniteGeometricBrascampLieb`; its planar-density branch does not. It
would be incorrect to describe the real-atom assembly as depending
only on BBV without discharging or explicitly retaining that premise.

An underlying probability space and atom arrays are supplied by the caller;
the project does not construct a canonical joint Gaussian space across all
dimensions.  The independence-to-product-law and joint absolute-continuity
steps themselves are proved.  The abstract predicate
`HasNullMvPolynomialZeroSets` is retained for arbitrary reference measures,
but `hasNullMvPolynomialZeroSets_pi` and
`hasNullMvPolynomialZeroSets_volume` now prove it in all the intended
applications.  It is no longer an external geometric-measure input.

## Build and audit

The complete integration passed on GitHub on **2026-09-03 UTC**:
**230 Lean files**, the normal `lake build`, and **271 exact axiom reports
covering 260 distinct declarations**. All reported axioms belong to
`propext`, `Classical.choice`, and `Quot.sound`.
The verified proof-source commit is `79798346f1cc9dda9cfd0c5bf2c3044aea5162a9`.
See the [successful run](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33702782802)
and [integration report](HIGH_BAND_INTEGRATION.md) for the complete new-file
and theorem inventory, conditional-premise classification, and shortest
remaining BC12 route. The cached remote job took about 10 minutes 25 seconds.

The previous 2026-09-02 checkpoint's full build and **196-declaration audit** both passed
(3432 jobs each). See [CONCRETE_MODELS_AUDIT.md](CONCRETE_MODELS_AUDIT.md)
for all nine new concrete-model modules, all 27 new theorems, the remaining
external-input boundary, and captured build/audit output. The audit also
retains every declaration from the previous 163-declaration matrix/probability
checkpoint, including the 31 integration and 30 smoothing theorems.
The earlier checkpoint is preserved in [BUILD_AUDIT.md](BUILD_AUDIT.md).
These historical records do not certify the later high-band integration.
Its current status is tracked in [HIGH_BAND_INTEGRATION.md](HIGH_BAND_INTEGRATION.md).

The project is pinned to Lean `v4.33.0` and mathlib `v4.33.0`.

```bash
lake build
lake build ShortRingAnchor.Audit
lake build ShortRingAnchor.HighBandIntegrationAudit
```

In the paper-wide repository this independent package lives at `section3/`;
run the commands from that directory. It does not modify the root Lake project
or the existing `vendor/short-ring-analysis` snapshot. For a serial, resumable
build and a fail-closed audit (Node.js required):

```sh
node scripts/serial-upstream-build.mjs ShortRingAnchor.Audit ShortRingAnchor.HighBandIntegrationAudit
node scripts/verify-project.mjs
```

The dedicated `.github/workflows/section3.yml` runs these checks on GitHub,
with logs and a machine-readable `summary.json` artifact. It builds only this
subproject, downloads dependencies only on the remote runner, and checks that
every requested declaration has exactly one axiom report using only the three
standard foundations. Source scanning alone is not a verification certificate.

`ShortRingAnchor/Audit.lean` runs `#print axioms` on the main theorem and the
major internal bridges.  The reported dependencies are only mathlib's
standard `propext`, `Classical.choice`, and `Quot.sound`.  The verified modules
contain no `sorry`, `admit`, `unsafe`, custom `axiom`, or soundness-lowering
option.

The audit also covers the BC12 formula-to-convergence route.  Passing an
axiom audit verifies the conditional deduction; it does not discharge the
explicit external formula hypotheses.  No large replacement dependency
cache was downloaded and no project cache was deleted during this addition.
The package uses the resource-only weak Lean argument `-j 1` to reduce
per-process thread usage while other projects are compiling. This does not
weaken Lean's kernel checks or change theorem assumptions.

## Module guide

- `CyclicVarianceProfile`, `IndependentConstantExtension`: exact cyclic
  coefficients, row/column normalization, bandwidth, and independence after
  adding deterministic zero coordinates.
- `IndependentAtomCopies`, `AtomDensityTransport`: explicit i.i.d. data
  and derivation of marginal moments/densities from the source laws.
- `CyclicV3Model`, `DenseV3Model`: the actual ensembles as complete v3 models.
- `ConcreteBulkScales`, `Lemma35Concrete`, `Proposition36Concrete`: exact
  polynomial bandwidth scales, the concrete Lemma 3.5, and elimination of
  the source-facing `hBulk` premise.
- `HermitizationResolventBlocks`, `HermitizationSingularTrace`,
  `MatrixStieltjesSmoothing`: block inverse identities, the exact singular-value
  trace formula, and deterministic CDF smoothing for actual matrices.
- `V3PointwiseProbability`: the actual canonical v3 formula (3.11) and
  its `N^(-10)` failure bound, conditional only on the named BBV comparison.
- `CompactStieltjesGoodEvent`, `LocalBulkPolynomialScales`,
  `MatrixLocalBulk`, `V3MatrixLocalBulk`, `Lemma35FromV3`: the common event, explicit scales,
  actual matrix probability/CDF bounds, and the final Lemma 3.5 constructor.
- `SourceStatement`, `ShortRingModel`: source notation, conclusion, and cyclic
  band model.
- `ParameterArithmetic`, `SourceScales`, `CutoffDominance`: (3.7)--(3.10)
  deterministic scale bookkeeping.
- `ClippedLog`, `BulkClippedLog`, `BulkProbability`: exact layer-cake identity
  and local CDF postprocessing for (3.11)--(3.12).
- `HardEdge`, `GinibreLowerEdge`, `UpperEdge`, `UpperEdgeAssembly`: the lower
  and upper truncation bounds in (3.10), (3.13), and (3.14).
- `SecondMoment`: singular-value/Frobenius identity and centered-entry
  expectation calculation.
- `CyclicSecondMoment`, `NormalizedGinibre`, `AtomAssumption21`: derive the
  row moment packages for the two matrix models from the moment part of
  Assumption 2.1, including the third-moment integrability deductions.
- `LogDecomposition`, `Approximation`, `TruncationAssembly`: the final
  low/middle/high and two-limit assembly.
- `SingularValues`, `AEInputTransfer`: matrix determinant bridge and
  almost-everywhere transport of the literature inputs.
- `ExternalInputs`: the honest boundary containing structures/definitions of
  cited hypotheses.
- `LeastSingularValueAdapter`, `EventualInputAdapters`: reduce Theorem 3.1 to
  its actual minimum-singular-value output and handle asymptotic cutoff
  specializations without hiding finite initial segments.
- `HermitizationCounting`: construct Hermitization eigenvectors from right
  singular vectors and convert the v3 symmetric interval count into the
  all-cutoff singular-value input.
- `HighProbabilityTransfer`: prove stability of convergence, tightness,
  `O_P`, and the iterated upper correction under `o(1)` exceptional events;
  derive short-ring nonsingularity in probability from Theorem 3.1.
- `AlmostSureNonsingularity`: determinant-polynomial nonvanishing for full
  and cyclic matrices, proved product/Lebesgue zero-set instances, and the
  joint-density-to-a.e.-invertibility adapters.
- `PolynomialZeroSets`: the complete finite-dimensional Fubini induction
  proving nullity of nonzero complex polynomial zero sets.
- `AtomLawAbsoluteContinuity`: bounded density to absolute continuity and
  nonatomicity, finite-product absolute continuity, and independent
  joint-law absolute continuity for real and complex atoms.
- `DensityNonsingularity`: independent nonatomic atoms avoid every nonzero
  polynomial zero set; both Assumption-2.1 density branches imply full,
  cyclic, and normalized dense shifted a.e. nonsingularity.
- `Proposition36`, `Proposition36Source`, `Proposition36Models`: generic,
  source-scale, and concrete-model main theorems.
- `Audit`: soundness audit commands.
- `BC12/NegativeMomentCounting`: finite layer-cake summation, an explicit
  `p=1/128`, and tightness from polynomial lower bounds and mesoscopic counts.
- `LocalStieltjesNet`, `HorizontalPolynomialNet`,
  `HorizontalComparisonProbability`: the explicit arbitrary-radius
  horizontal grid and its full quantitative probability estimate.
- `ExplicitStieltjesRate`: the common exponent extracted from the vendored
  v3 (3.11) arithmetic.
- `HilbertSchmidtCutoffRemoval`: the two-limit cutoff removal by tightness.
- `PoissonSmoothingKernel`, `PoissonSmoothingFinite`, `LocalPoissonSmoothing`,
  `PoissonSmoothingCDF`, `PoissonSmoothingProbability`: the full finite-spectrum
  smoothing chain and the constructor for the named local CDF interface.
- `Vendor`: small upstream source snapshots; see `UPSTREAM.md` for the
  complete file manifest and the boundary between staging and integration.
