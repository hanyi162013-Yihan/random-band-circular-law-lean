# Section 6: Gaussian noncompact profiles

This verified continuation is published on `main`; its development snapshot
remains on `codex/section6-formalization`. It imports the verified `section5/`
package and shares the pinned Lean 4.33.0/mathlib dependencies. No second
mathlib checkout or large local download is needed. See
[main integration and exact verification scope](MAIN_INTEGRATION.md).

## Main endpoint and verification status

**Current migration verified:** the new source changes, all 808 named public
source theorems, both old regression files and sixteen module kernel replays
passed at `55b3dfe`. See the
[exact cross-project certificate](../GAUSSIAN_MIGRATION_VERIFICATION.md) and
[input map](../GAUSSIAN_INPUT_MIGRATION.md).
The actual Ginibre raw-log and spectral limits now have proved constructors
without BBV; its negative moment still uses BBV. The historical sparse,
subsequence and published-source records no longer ask for those three
Gaussian conclusions. The separate squared-singular/Han routes are retained
as optional conditional results, not inputs of the preferred endpoint.

The following is the earlier verified BBV-only checkpoint, not a certificate
for the newer migration changes.

The new endpoint `NoncompactProfile.gaussian_profile_circular_law_of_bbv_sources`
passed [run 33740349647](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33740349647)
at `9d98ca87d112a240fc5b596d1a27801450b15cbe`: complete target/import build,
203-declaration transitive axiom audit, seven new regressions and a 196-file
source scan. Its only source fields are uniform BBV and the two finite
Section 4 pressure estimates for each core. Actual Ginibre negative-moment tightness,
raw-log and spectral limits are proved from BBV; unequal-dimension comparison
removes the separate squared-singular-test source. No Han input remains.
See [the exact result and boundary](BBV_ONLY_ENDPOINT.md).

The following paragraphs record earlier verified checkpoints.

The concrete Section 3 → Section 5 → Section 6 interfaces passed
[run 33725000131](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33725000131)
at `c992bff30e9af6ddabcba04f113447cd48c27f20`, including the 93-declaration
Section 5 and 35-declaration Section 6 transitive audits. The literal core
anchor models and samples are constructed at this newer endpoint, not
requested as extra convergence certificates. The Section 5 portion was
published separately to main at `6887a8c7591ec15c37513f6c0944605c3680d5ef`.

New explicit-import adapters assemble
`gaussian_profile_circular_law_without_Han` in `DenseProfileEndpoint.lean`
and reuse the actual Gaussian negative-moment and finite-formula log-limit
proofs from root `section3/`. Their combined cloud compilation and
145-declaration transitive axiom audit passed
[run 33731702204](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33731702204)
at `ccdfb4c52fffd96f6facd4042529c6eb796ae590`. That earlier bundle's inputs
are BBV, the actual Ginibre logarithmic limit, the bounded squared-singular
test limit, and two finite Section 4 pressure estimates. Han and separate
Ginibre negative-moment/raw/spectral duplicate inputs are no longer needed
at that endpoint. The BBV-only derivation and stronger final endpoint have
now passed the newer checkpoint above.
See [Dense/Ginibre adapter scope](DENSE_GINIBRE_ADAPTERS.md).

The earlier 136-module integration passed the targeted cloud check.
A concrete Gaussian density constructor exposed an auto-implicit `top` in
the imported Section 3 density record. The user-approved shared correction is documented in
[Section 3 integration corrections](../section3/INTEGRATION_CORRECTIONS.md).
The 122-module checkpoint below predates that correction and verifies
conditional proofs, not satisfiability of the former density premise.

The earlier published-source target is
`CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law_of_published_sources`
in [PublishedSourceGaussianProfile.lean](CircularLawSection6/PublishedSourceGaussianProfile.lean).
It derives local finite-CDF comparison internally from the checked Section 3
estimates on the actual Gaussian models. This endpoint passed
[run 33719510129](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33719510129)
at commit `3ccc69511387b2e923c38f2184b140d3536a1c09`: all 136 modules,
126 regressions and both transitive audits passed. The audit covered 1305
Section 6 declarations/1103 theorems and 126 new Section 3 integration declarations.
The prior
`gaussian_profile_circular_law_of_published_section3` remains available.
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

This earlier theorem is conditional on explicitly stated mathematical sources.
[SOURCE_BOUNDARIES.md](SOURCE_BOUNDARIES.md) lists their exact content:
finite Section 4 estimates and published Section 3 model/literature data for the internally called Section 5 theorem, BBV estimates for the actual local comparison models,
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
The 136-module run additionally verifies the actual limiting-law and model
adapters, including the concrete Gaussian density record with the shared fix.

## Boundaries not concealed by the endpoint

Historical conditional routes do not reprove Han or the limiting
squared-singular law. Neither is required by the preferred BBV-only endpoint.
The current Section 5 source record takes finite model/sampling identities,
the actual Gaussian law, and BBV comparisons; Gaussian log and negative-moment
estimates are constructed internally, not supplied as BC12 premises.
Real-density routes additionally retain geometric Brascamp--Lieb.
Generic conditional helper theorems remain available for other source models.

The circular-law chain uses an inverse-moment/uniform-L2 route. The separate
hard-edge modules prove that a bounded Poisson transform implies a linear CDF
bound, then derive the exact logarithmic layer-cake identity, logarithmic
integrability and cutoff limit. The 136-module run also verifies that bound
for the actual limiting Ginibre law, its logarithmic-potential identification
from the classical sources, and the variance-scaled uniform cutoff estimate.
The older general interfaces retain finite short-ring/calibration data.
The newer concrete interface constructs those data for this Gaussian core.
Thus the conditional main endpoint is not a claim that
every intermediate statement of Section 6 has been formalized line by line.

## Reproduce verification

```sh
cd section6
LEAN_NUM_THREADS=1 lake --no-cache build CircularLawSection6
python3 ../scripts/build_gaussian_migration.py --project section6 --audit
```

The current audit checks every named public source theorem in
`PublicTheoremAxiomAudit.lean`, the focused migration checks, and both original
regression suites. It uses default checking limits and permits only
`propext`, `Classical.choice`, and `Quot.sound` transitively. Private helpers
are covered transitively when used, not counted separately.
The older `AxiomAudit.lean` is retained only as historical tooling.
GitHub retains build, audit and
regression logs, and saves completed dependency builds even after a failed
new-module check.
