# Gaussian input audit and migration

Status: **migration in progress; new Section 5/6/8/10 signatures still require cloud validation**.
The Section 3 construction is already verified and merged in PR #3, at
`43798327f45d98c45f2aaae6e5d1f0d041fc19c9`.
This document is not a certificate for the newer source changes.

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
| 7–9 | Section 7 lemmas are housed in the Section 8/9 libraries; both Section 8 final endpoints use the actual Section 3 adapter | Section 8 negative-moment/projection/correlation fields removed; Section 9 Cook/Nguyen inputs are distinct | Section 8 cloud build pending; Section 9 sources unchanged |
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
`ClassicalGinibreSquaredTestInput`, `GinibreLogPotentialInput`, and
`HanGaussianDenseInput`. They are **not** the reduced public route and are
not claimed to be assumption-free. The full limiting squared-singular law
has not been proved by this migration; the concrete BBV-core route avoids
needing it. `verifiedGinibreFiniteFormulaInput` instead constructs the exact
finite correlation/projection record with no premise.

The regression guard checks the selected public signatures and record fields;
it does not establish that every historical conditional theorem in the
repository has been deleted or generalized. The cloud audit must inspect the
compiled declarations as well as their transitive kernel axioms.

The generic Section 5 taper interfaces also retain explicit negative-moment
and full-log premises for arbitrary comparison processes. They are not the
fixed-law indicator endpoints migrated here. Discharging those premises
requires a concrete Gaussian-law identification and the compatible exponent
`p = 1/128`; it does not follow for an arbitrary process or a taper with a
vanishing lower profile bound. No full taper-source migration is claimed.

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
