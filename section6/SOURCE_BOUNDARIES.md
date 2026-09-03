# Section 6 source boundaries

The target declaration is
`CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law`
in `CircularLawSection6/GaussianProfileTheorem.lean`. The complete 110-module
checkpoint, including this theorem, passed strict compilation, the transitive
axiom audit and all 107 regressions in GitHub run 33708812493. See
`VERIFICATION.md` for the exact commit and scope.

## What the endpoint says

For a strictly positive continuous profile with bounded variation, finite
integral and integral one, and positive bandwidths tending to infinity,
the actual normalized Gaussian cyclic matrices converge to the circular law
against every continuous compactly supported real test function, in
probability on the explicitly constructed Gaussian product sample space.
There is **no assumption that W/N has a limit**.

The finite model is `p.matrix (n+1) (W n)`. `cyclicPhysicalMatrix` only
changes the coordinate labels from `ZMod (n+1)` to `Fin (n+1)`; the determinant
and normalized Hilbert--Schmidt energy are proved unchanged. The comparison
ensemble is the actual normalized circular Ginibre matrix, not an abstract
model supplied by the caller.

## Explicit external inputs

The endpoint takes ordinary mathematical hypotheses, never new axioms.
The axiom audit cannot and does not discharge these hypotheses.

| Input | Exact mathematical content | Location |
| --- | --- | --- |
| `coreSection5` | Section 5's literal normalized Gaussian core log-potential limit in probability, after any required finite prefix | `FinitePrefixCoreBridge.lean` |
| `coreSection3` | Local finite squared-singular CDF comparison with finite Ginibre, plus the Ginibre bounded-test singular-law limit with nonnegative support and finite second moment | `CanonicalSourceComparison.lean` |
| `ginibreRaw` | Classical normalized Ginibre raw log-potential convergence in probability for planar-a.e. shift | `SubsequenceSourceEndpoint.lean` |
| `ginibreNegative` | Tightness in probability of one positive-order inverse singular-value moment of shifted Ginibre | `GinibreLowerCutoff.lean` |
| `ginibreSpectral` | Classical circular law for the actual normalized Ginibre reference | `SubsequenceSourceEndpoint.lean` |
| `HanGaussianDenseInput` | Gaussian specialization of Han, arXiv:2410.16457v3, Theorem 1.5, at exponent 11/12 = 5/6 + 1/12 | `DenseGaussianSourceAdapter.lean` |

The core assumptions are stated for increasing dimension sequences because
the final proof extracts subsequences. They are **not** assumptions that
the full noncompact model converges. The local comparison dimensions obey
`2H+1 <= M <= 2*(2H+1)^2`, independently of the global matrix dimension.

Han's source: [Theorem 1.5 and Definition 1.2](https://arxiv.org/html/2410.16457v3).
The dense adapter proves the profile bounds `q_s <= C/N` and the eventual
threshold `C/N <= N^(-11/12)`. Row and column normalization follows from the
proved cyclic variance-sum identities and `p.sum_weight`.

## What is proved internally

The proof constructs the Gaussian atoms, physical matrices, positive core
weights and their normalization. It proves Gaussian determinant integrability,
nonvanishing, concentration, full/core/tail energy and sample-law identities,
Jensen lower comparison, cutoff stability, the complementary mass limits,
and the fourth-root normalization error.

For compact comparison it constructs a balanced partition, using one exact
unchanged block when the matrix is shorter than the quadratic block scale.
It proves the boundary energy/cutoff error and exact weighted block average,
converts local finite-CDF convergence to cutoff expectations, and proves
uniformity over all admissible block lengths. The actual full-matrix cutoff
comparison is a conclusion, not an input.

Inverse-moment tightness gives lower-cutoff smallness in probability; proved
uniform second-moment control upgrades this to the iterated L1 estimate.
This yields the actual noncompact mean limit and then the probability limit.
The already proved Section 5/Tao--Vu replacement theorem is instantiated
with exact mean normalized energies one for both concrete models.

Subsequence gaps are filled with the Ginibre matrix, preserving the original
dimension at every index. Sparse/dense extraction and recombination are
proved on numerical bad-event probabilities. No exchange of an uncountable
subsequence quantifier with an almost-everywhere spectral-parameter quantifier
is used.

## What is not claimed

This package does not reprove the cited Han, BC12 or classical Ginibre source
theorems. Section 3 has not been silently formalized by naming an input.
The Section 5 endpoint is an explicitly declared input at the manuscript
boundary; the final theorem does not yet call a fully bundled external
Section 3/4/5 instance with no parameters.

The proof uses an inverse-moment/uniform-L2 alternative to the manuscript's
separate linear limiting-singular-density hard-edge estimate. That stronger
standalone estimate is not claimed as proved by this route. Accordingly,
completion of the circular-law chain conditional on the stated sources is
not identical to a line-by-line formalization of every intermediate claim.

`StieltjesHardEdge.lean` separately proves the generic implication
`integral t/(s^2+t^2) <= C` implies `sigma([0,t]) <= 2*C*t`, and its CDF
version for nonnegative laws. The actual limiting-law transform bound and
the logarithmic layer-cake identity are still separate boundaries, not
consequences claimed from that generic adapter alone.
