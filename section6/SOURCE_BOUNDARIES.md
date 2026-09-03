# Section 6 source boundaries

The current BBV-only Ginibre and concrete profile endpoint is documented in
[BBV_ONLY_ENDPOINT.md](BBV_ONLY_ENDPOINT.md). Its complete import chain,
203-declaration transitive audit and seven regression examples passed
[run 33740349647](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33740349647)
at `9d98ca87d112a240fc5b596d1a27801450b15cbe`.

The current `GaussianProfileBBVSources` has exactly two explicit fields:

- `bbv`: the uniform published BBV comparison input.
- `coreSection4`: the two finite Section 4 pressure estimates for each
  compact core.

The actual Gaussian logarithmic-potential limit, spectral circular law and
negative-moment tightness at order `1/128` are now derived from BBV and the
proved Gaussian estimates. The logarithmic limit holds for every fixed
complex shift. Unequal-dimension comparison and the moving Ginibre reference
remove the separate limiting squared-singular-test source. The actual dense
profile branch calls repository-root Section 3 instead of
`HanGaussianDenseInput`; Section 5 imports that same root `section3/`.

The BBV literature result and finite Section 4 pressure estimates remain
explicit hypotheses, not newly proved results. A transitive axiom audit
does not discharge them. The older four-field
`GaussianProfileReducedSources` and finite-formula interfaces remain as
compatibility endpoints, but are not extra inputs of the new two-field
endpoint.

## Historical published-source interface

The table below describes the older published-source endpoint, not the
current two-field source bundle above.

The subsequent concrete interface passed run33725000131 at
`c992bff30e9af6ddabcba04f113447cd48c27f20` and constructs the actual core
Section 3 model/sampling data internally. Thus the finite-input limitations
of the older interfaces below are not limitations of that newer caller.

The current branch includes a user-approved correction to Section 3's
bounded-density record: its bound is explicitly below ENNReal top, not an
auto-implicit variable. Concrete Gaussian instantiation compiled in cloud;
the full 136-module integration, audits and 126 regressions have passed. The historical
122-module checkpoint below predates this correction;
see `../section3/INTEGRATION_CORRECTIONS.md`.

The new target declaration is
`CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law_of_published_sources`
in `CircularLawSection6/PublishedSourceGaussianProfile.lean`; its targeted
verification passed in run 33719510129 at commit `3ccc69511387b2e923c38f2184b140d3536a1c09`.
The older
`gaussian_profile_circular_law_of_published_section3` belongs to the 122-module
checkpoint, which passed strict compilation, the transitive
axiom audits and all 119 regressions in GitHub run 33714847892. See
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
| `coreSection34` | Two finite quantitative Section 4 pressure estimates and finite published Section 3 model/sampling/literature data; both Section 3 anchors and the Section 5 core limit are derived internally | `PublishedSection3CoreEndpoint.lean` |
| `coreLocal` | BBV comparison for two explicitly constructed finite Gaussian models, plus the common Ginibre bounded-test singular-law limit with nonnegative support and finite second moment; local CDF convergence is derived internally | `PublishedCoreLocalInput.lean` |
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

The historical interfaces described above retain their named literature hypotheses.
The current two-field endpoint instead derives the needed actual Ginibre
logarithmic and spectral results from BBV and avoids the Han input. This is
not a proof of the general Han theorem or of the BBV literature result.
Section 3 has not been silently formalized by naming an input.
In those historical interfaces, the Section 5 endpoint is called internally, with all core geometry and
Gaussian atom transfer proved. The new published Section 3/density entry point
also passed combined cloud verification. Finite model/sampling identities,
fixed atom laws and the published BBV/BC12 sources remain explicit; the real
density branch additionally retains geometric Brascamp--Lieb. The model and
sampling adapters are not a claim that every possible caller's finite inputs
have been automatically instantiated.

The proof uses an inverse-moment/uniform-L2 alternative to the manuscript's
separate linear limiting-singular-density hard-edge estimate. The separate
hard-edge modules now also prove the actual limiting-law estimate from the
explicit BBV and Ginibre weak-law sources. Accordingly,
completion of the circular-law chain conditional on the stated sources is
not identical to a line-by-line formalization of every intermediate claim.

`StieltjesHardEdge.lean` separately proves the generic implication
`integral t/(s^2+t^2) <= C` implies `sigma([0,t]) <= 2*C*t`, and its CDF
version for nonnegative laws. The exact logarithmic layer-cake identity,
integrability and linear cutoff error are now proved from this CDF bound.
The actual limiting-law bound and logarithmic-potential identification
subsequently compiled in run 33718531306 via `GinibreLimitingHardEdge.lean`
and `GinibreLimitingLogPotential.lean`. The later 136-module run 33719510129
checks those results together with all model/endpoint adapters, both audits
and the regression suite. These results are not
inferred merely from the generic adapter or from the axiom audit.
