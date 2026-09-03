# Dense profile and Ginibre source reuse

Status: combined cloud verification and transitive axiom audit passed in
[run 33731702204](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33731702204)
at commit `ccdfb4c52fffd96f6facd4042529c6eb796ae590`.
The target `CircularLawSection6.GinibreFiniteFormulaSources` and its imports
compiled; `DenseGinibreAudit.lean` checked 145 declarations with only
`propext`, `Classical.choice`, and `Quot.sound` permitted transitively.
The source-token scan checked 170 selected Lean files.

These are explicit-import modules, not a claim that the historical umbrella
or its full regression suite was rerun. No local Lean compilation or new
local toolchain/mathlib download was performed. This work remains on
`codex/section6-formalization`; it has not been merged into main.

## Actual dense profile, without Han

`DenseProfilePublishedModel` constructs the full cyclic Gaussian matrix on
the common countable sample space and proves its V3 and planar model laws.
The geometric planar width is `N`; the exact spectral bandwidth is
`1 / max q`, with lower bound `N/C` from `q ≤ C/N`.

`DenseProfileLSV`, `DenseProfileScales`, and `DenseProfileConclusion` apply
the general root Section 3 least-value, all-cutoff counting, bulk comparison
and Proposition 3.6 proofs. They do not impose the short-ring condition
`2W+1 ≤ N` on a full-width model.

`DenseProfileEndpoint` transports the actual dense raw-potential law, applies
the existing subsequence replacement, and combines the dense branch with
the verified sparse Section 4/5 branch. Its theorem
`NoncompactProfile.gaussian_profile_circular_law_without_Han` does not take
`HanGaussianDenseInput`. This is not a proof of Han's more general theorem.

## Existing Gaussian negative moments

The local `finite-moment-short-ring-anchor` project supplied the two new
root Section 3 modules `BC12/GinibreSmallBall` and `BC12/GinibreNegativeMoments`.
Only those small source files were copied; their existing imports were
reused. Cloud elaboration fixes are included in this development branch.

`GinibreGaussianLaw` identifies the actual scalar Gaussian array with the
Euclidean-column Gaussian law, including both square-root normalizations.
`GinibreNegativeSources` derives the negative moment at `p=1/128` from BBV
and the proved polynomial Gaussian lower edge. `SingularValueMeasurability`
justifies finite-law transport of the actual negative-moment event.

The final green run includes the actual Gaussian law, the negative moment
on the shared infinite array, its transport to the triangular finite laws,
and the reduced source bundle. Intermediate runs compiled individual pieces
but are superseded by the combined checkpoint above. Negative-moment
tightness is in probability; no uniform expectation bound is asserted.

## Logarithmic and spectral sources

`GinibreReferenceSources` derives raw and spectral reference limits from
the existing BC12 source; the spectral step calls Section 5's proved
diagonal-disk reference and replacement theorem.

`GinibreReducedSources` removes duplicate raw/negative/spectral fields.
Its remaining inputs are uniform BBV, the actual Gaussian logarithmic
limit, the classical shifted squared-singular-value bounded-test limit,
and the two finite Section 4 pressure estimates.

`GinibreFiniteFormulaSources` further constructs the logarithmic input by
calling root Section 3's
`BC12.ginibre_matrix_logdet_convergesInProbability_of_formulas` for the
actual `ginibreOnSequence` matrices. Exact finite projection/correlation
formulas remain explicit hypotheses. Candidate kernel or density identities
alone do not establish those formulas for the actual Gaussian eigenvalues.

No independent BBV-only proof of the logarithmic center or the classical
squared-singular-value limit is claimed. The new final endpoint is still
conditional on these clearly identified literature boundaries.

## BBV route identified for further source reduction

`PublishedStieltjesMean.published_dense_meanStieltjes_tendsto` already proves
the fixed-positive-height expected Hermitized Stieltjes limit from BBV for
the actual dense models. Together with the scalar Dyson equation, this
provides a route that does not require Gaussian eigenvalue correlations.
At imaginary height `t`, writing `m = i v` and `a = t + v`, the proposed
logarithmic primitive is `log(a^2 + norm(z)^2)/2 - v^2/2`.

Identification of this primitive, convergence of the regularized random
potential, and removal of regularization in probability remain to be
formalized on this route. The existing negative-moment result is available
for the last step. Existing lower-cutoff **L1** theorems already assume raw
potential convergence and must not be used circularly to establish it.
The scalar-Dyson uniqueness file also exists in the user's separate local
Proposition 3.4 project; it is not yet imported into this adapter chain.

A second possible reduction avoids the separate squared-test limiting law:
the same-size block-to-Ginibre CDF and cutoff-mean comparison is already
proved without that law. Root Section 3's deterministic Stieltjes smoothing
also accepts different matrix dimensions. What is not yet packaged is the
random comparison of two dense Ginibre dimensions tending independently to
infinity, followed by the core block-average proof relative to the ambient
Ginibre mean (a moving reference, with difference tending to zero). This
must retain local blocks; comparing the entire low-bandwidth core directly
would introduce an unsupported bandwidth-versus-dimension restriction.
The current reduced source record still includes `ginibreSquared` until
that new assembly is proved and verified.
