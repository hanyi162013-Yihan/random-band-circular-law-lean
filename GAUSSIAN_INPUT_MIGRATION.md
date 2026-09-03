# Gaussian input audit and migration

Status: **Sections 3, 5, 8 and 10 passed their migration checks;
the strengthened Section 6 route and whole-chapter regression are pending**.
The Section 3 construction is already verified and merged in PR #3, at
`43798327f45d98c45f2aaae6e5d1f0d041fc19c9`.
This document is not a certificate for the newer source changes.

Section 8's BC12-free adapter and both final theorem families passed
[run 33814530370](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33814530370)
at `7012b1ef2e13d63154e4436d0b201581dafa7954`: ordinary target builds,
62 exact axiom reports and both compiled public-signature audits, including
the shared Section 3 normalization lemma.
At `c4e807877fefef8339a6ff01ec4ed75bc08ded81`,
[run 33815655602](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33815655602)
passed the Section 5 public build and all 240 reports, including the taper
adapter. Its root job passed all Section 8/10 target builds and all 564
reports (502 for Section 10), then failed on a missing Section 9 umbrella
import in the audit configuration. That is **not** a successful whole-run
certificate. The missing audit-only imports are now included in the build
closure. The full chapter check at `d603e53` is running in
[run 33816611348](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33816611348).
Its root job has now passed all nine public targets and 975 axiom reports,
including Sections 4 and 9; Section 5/6 are still being checked.
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
| 5 | `PublishedSection3Concrete.indicator_complex_full_of_published_literature` and real counterpart | `hBC12` removed; `provedGinibreInput hBBV` constructs both estimates | Passed at `c4e8078`, 240 reports, including the taper adapter |
| 6 | `NoncompactProfile.gaussian_profile_circular_law_of_bbv_sources` and BBV-core route | Only BBV and concrete Section 4 pressure fields; no raw-log, squared-test, Han or correlation field | New migration pending; earlier BBV-only endpoint already existed |
| 7–9 | Section 7 lemmas are housed in the Section 8/9 libraries; both Section 8 final endpoints use the actual Section 3 adapter | Section 8 negative-moment/projection/correlation fields removed; Section 9 Cook/Nguyen inputs are distinct | Section 8 passed at `7012b1e`; Section 9 sources unchanged |
| 10 | `BernoulliSection10Source.planar_density_circular_law`, `real_density_circular_law`, and both ring-log limits | `hBC12` removed; exact real-pair reference law and both estimates constructed | Builds and all 502 chapter reports passed at `c4e8078`; whole-run check still pending |

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
The later `ginibre_raw_verified` and `ginibre_spectral_verified` strengthen
the Section 6 cyclic-reference statements further: neither requires BBV.
Only the negative-moment constructor still uses BBV. These later
factorizations are awaiting their own cloud check.
Even the historical concrete/reduced bundles no longer ask callers for
BC12, raw-log, negative-moment, spectral or full-log fields; their former
accessors are proved methods where needed for compatibility.

The sparse/subsequence, Section 3/4 and published-source records have also
been reduced: their old `ginibreRaw`, `ginibreNegative` and `ginibreSpectral`
fields are replaced by one explicit `bbv` field. Their proofs call the
verified raw/spectral limit and the BBV-derived negative moment internally.
This is an intentional change to those older generic source APIs; it does
not eliminate their separate core-local, pressure or optional Han inputs.

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
The taper adapter passed at `c4e8078`; the newer Section 6 compatibility
changes still require cloud validation.

## Verification plan

- No local Lean compilation or large cache download for this migration.
- `build_gaussian_migration.py` computes the actual import closure for each
  of the root, Section 5 and Section 6 projects, including the pinned Ginibre
  package, rejects import cycles and builds modules serially.
- Each project ends with ordinary `lake --no-cache build` of its public targets.
- Separate compiled axiom/signature audits require the usual
  `propext`, `Classical.choice`, `Quot.sound` allowlist with exact report counts.
- The final expanded audit covers 1379 root, 240 Section 5 and 31 Section 6
  reports. Optional kernel replay checks the 28 changed proof modules with
  one worker and exact module coverage. This uses Lean's own kernel, not an
  external independent verifier, and does not replay all of mathlib.
- The upstream signature audit prints the genuine Gaussian model definitions
  and the density/correlation/log-limit signatures; Schur change of variables
  and finite correlations must not reappear as external hypotheses.
- The expanded audit also compiles the existing Section 6 regression
  examples and BBV-only regression, both Section 8 public signature audits,
  and the Section 10 density schema regression; errors in any file fail CI.
- No new proof-checking limit overrides, custom axioms, `sorry`, `admit`,
  `unsafe`, or `native_decide` are permitted in the new source constructors.
- Cloud reports must be associated with their exact commit before marking a
  chapter passed or merging this migration.
