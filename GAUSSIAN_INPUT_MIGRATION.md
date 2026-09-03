# Gaussian input audit and migration

Status: **Section 3 and Section 8 passed; the Section 5/6/10 migration is still being validated**.
The Section 3 construction is already verified and merged in PR #3, at
`43798327f45d98c45f2aaae6e5d1f0d041fc19c9`.
This document is not a certificate for the newer source changes.

Section 8's BC12-free adapter and both final theorem families passed
[run 33812017163](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33812017163)
at `8d9dbc26f820f7056b37108c980501cecb951203`: ordinary target builds,
61 exact axiom reports and both compiled public-signature audits.
The broader migration at `94d3efa` is checked separately in
[run 33812184651](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33812184651).
The later compatibility/taper migration and extraction of
`BC12.normalizedGaussianPair_map` into the shared Section 3 layer are pending.
The shared lemma removes duplicated normalization proofs from Sections 8 and 10.

## Scope and proof boundary

The target is to remove *externally supplied Gaussian conclusions* from the
article's concrete public endpoints. Independence, atom moments, densities,
and a statement that a variable has its specified Gaussian model law are
model data, not external spectral theorems. In the concrete Section 5, 8 and
10 adapters even the Gaussian matrix-law identification is proved internally.

Uniform BBV/van Handel comparison, the explicitly retained Proposition 3.2
and Cook 1.12 inputs, the separate Cook/Nguyen Section 8/9 inputs, real
geometric Brascamp–Lieb, and generic Section 4 pressure interfaces are not
silently discarded. Eliminating BC12 does not prove these different results.

## Current chapter map

| Chapter | Concrete public route | Gaussian premise after migration | Verification |
|---|---|---|---|
| 3 | `proposition36_cyclicShortRing_withoutBC12`, `Proposition38.proposition38_withoutBC12` | No BC12 estimate; explicit Gaussian model law | Passed, merged |
| 4 | deterministic / density / pressure results | No Gaussian spectral source found; “Gaussian elimination” is linear algebra | Sources unchanged |
| 5 | `PublishedSection3Concrete.indicator_complex_full_of_published_literature` and real counterpart | `hBC12` removed; `provedGinibreInput hBBV` constructs both estimates | Pending |
| 6 | `NoncompactProfile.gaussian_profile_circular_law_of_bbv_sources` and BBV-core route | Only BBV and concrete Section 4 pressure fields; no raw-log, squared-test, Han or correlation field | New migration pending; earlier BBV-only endpoint already existed |
| 7–9 | Section 7 lemmas are housed in the Section 8/9 libraries; both Section 8 final endpoints use the actual Section 3 adapter | Section 8 negative-moment/projection/correlation fields removed; Section 9 Cook/Nguyen inputs are distinct | Section 8 passed at `8d9dbc2`; Section 9 sources unchanged |
| 10 | `BernoulliSection10Source.planar_density_circular_law`, `real_density_circular_law`, and both ring-log limits | `hBC12` removed; exact real-pair reference law and both estimates constructed | Pending |

### Section 6 really does depend on Section 5

`section6/lakefile.toml` requires `CircularLawSections56` from `../section5`.
The Gaussian law/negative-moment construction needed by Section 5 is now
available in its own `VerifiedGinibreSources` module without importing
Section 6. Section 6's core and dense calls are migrated to this lower-level
constructor. The original BBV-based Ginibre derivation is retained as an
independent proved route, not converted into a hidden premise.

## Compatibility statements are not external assumptions

`BC12GinibreInput` is retained as a compatibility proposition in the old
`LiteratureInputs` / `PublishedSection3Literature` files. Its proved constructor
now supplies it at concrete call sites. The proposition itself is not an axiom.
Generic lemmas such as `bc12_on_sampleLaw`, `ginibre_raw_of_bc12`, or a cutoff
lemma conditional on bounded negative moments remain valid reusable lemmas.

Section 6 also retains historical conditional routes with
`ClassicalGinibreSquaredTestInput` and `HanGaussianDenseInput`.
They are **not** the preferred BBV-only public route and are not claimed
to be assumption-free. The full limiting squared-singular law
has not been proved by this migration; the concrete BBV-core route avoids
needing it. `verifiedGinibreFiniteFormulaInput` instead constructs the exact
finite correlation/projection record with no premise.
`verifiedGinibreLogPotentialInput` likewise constructs the log-limit record.
Even the historical concrete/reduced bundles no longer ask callers for
BC12, raw-log, negative-moment, spectral or full-log fields; their former
accessors are proved methods where needed for compatibility.

The regression guard checks the selected public signatures and record fields;
it does not establish that every historical conditional theorem in the
repository has been deleted or generalized. The cloud audit must inspect the
compiled declarations as well as their transitive kernel axioms.

The generic Section 5 taper lemmas with arbitrary comparison processes remain
available. The new `TaperVerifiedGinibre` adapter instead constructs their
Gaussian nonsingularity, negative moment, full-log limit and row moments from
an actual Ginibre model law and BBV, fixing the compatible exponent to
`p = 1/128`. Its reduced record has only the taper's LSV, count and local
comparison fields. This is a Gaussian-source migration, not a proof of those
three taper estimates or a uniform-positive-profile theorem for taper weights.
These additional compatibility/taper changes still require cloud validation.

## Verification plan

- No local Lean compilation or large cache download for this migration.
- `build_gaussian_migration.py` computes the actual import closure for each
  of the root, Section 5 and Section 6 projects, including the pinned Ginibre
  package, rejects import cycles and builds modules serially.
- Each project ends with ordinary `lake --no-cache build` of its public targets.
- Separate compiled axiom/signature audits require the usual
  `propext`, `Classical.choice`, `Quot.sound` allowlist with exact report counts.
- No new proof-checking limit overrides, custom axioms, `sorry`, `admit`,
  `unsafe`, or `native_decide` are permitted in the new source constructors.
- Cloud reports must be associated with their exact commit before marking a
  chapter passed or merging this migration.
