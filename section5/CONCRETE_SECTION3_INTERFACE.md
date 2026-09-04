# Concrete Section 3 → Section 5 interface

## Stronger complex-density endpoint

`PublishedSection3Concrete.indicator_complex_full_of_bbv`, in
`VerifiedComplexSection5Endpoint.lean`, constructs both finite Section 4
pressure contracts on the actual matrix sample space. Its only external
literature premise is BBV; density, moments, profile and bandwidth assumptions
remain explicit. It passed the ordinary build, 1118 axiom reports, a direct
no-pressure-premise call and eight module kernel replays at `7136329`.
See [the separate verification evidence](../PRESSURE_INPUT_MIGRATION.md).
The real-density endpoint still retains its pressure and geometric
Brascamp–Lieb premises. These are separate branches, not extra premises of
the Gaussian Section 6 endpoint.

## Earlier Gaussian-source migration

**Migration status:** the current branch removes the external BC12 parameter
using `provedGinibreInput` in the `PublishedSection3Concrete` namespace,
defined in `VerifiedGinibreSources.lean`. These signature changes passed
at `c4e8078`, with all 240 Section 5 reports and the normal target build;
see [the current certificate](SECTION3_INTEGRATION.md).
The later migration of the general `PublishedSection3Model.Sources` record
to an actual Gaussian-law field passed at `d7d732c`, with 1109 reports and
six module kernel replays; see the
[exact certificate](../GAUSSIAN_MIGRATION_VERIFICATION.md). That record
no longer contains a negative exponent or either BC12 estimate; it uses
the fixed proved exponent `1/128` internally.
See [the whole-paper migration audit](../GAUSSIAN_INPUT_MIGRATION.md).

The new entry points construct the actual short-ring and calibration matrices
and invoke the checked Section 3 theorem internally. The caller no longer
supplies a Section 3 anchor limit, finite sampling certificate, matrix identity,
or a model-by-model comparison certificate.

## Earlier conditional endpoints and their remaining inputs

`PublishedSection3ConcreteEndpoint.lean` exports
`indicator_complex_full_of_published_literature` and
`indicator_real_full_of_published_literature` in
`CircularLawSections56.Section5.PublishedSection3Concrete`.
Their conclusions are the existing full Section 5 conclusions on the actual
finite IID spaces, including the spectral-test comparison to the disk model.

The scope is a fixed atom law satisfying the original moment and bounded-density
assumptions, centered indicator-band geometry, fixed positive lower/upper profile
bounds, bandwidth tending to infinity, and eventual dimension/bandwidth fit.
Real atoms are returned on their original real IID space. The source hypotheses
are universal BBV for the canonical Gaussian companions and the two quantitative Section 4
pressure estimates. The stronger complex endpoint above supplies these
estimates internally. The real branch also retains geometric Brascamp–Lieb.
These are ordinary theorem hypotheses, not new axioms. The actual normalized
Ginibre law, negative-moment tightness and full-log limit are constructed
internally, rather than requested as a BC12 parameter.

The old taper and varying-atom interfaces remain available. This new fixed-law,
uniformly positive profile wrapper does **not** claim automatic Section 3
instantiation for arbitrary size-dependent atom laws or taper profiles with
vanishing lower profile constants.

## Internal constructions

- An explicit product of two infinite IID arrays provides both the original
  atom samples and the independent actual circular Gaussian reference.
- Finite coordinate maps are measure-preserving. Calibration uses exactly the
  first rows of the original array, with the physical calibration dimension
  as its logarithmic-determinant normalization.
- The actual finite ring models, density/moment records, common constants,
  cutoffs, and published Section 3 source inputs are constructed internally.
- Inactive branches use auxiliary mesoscopic rings; finitely many invalid
  indices are replaced by the first valid model. No all-index high-band
  premise or inactive-branch convergence certificate is added to the endpoint.
- The proved short and calibration limits are transported back to the
  original finite IID laws before invoking the existing Section 5 theorem.

The construction follows the verified Section 10 sampling/literature pattern;
it uses the scalar signed-band geometry proved here, not the Section 10 block
matrix conclusion.

## Section 6 caller

`CircularLawSection6.CoreRadiusBounds.ConcreteSection4Input.toSection34`
constructs these anchors for the actual clamped Gaussian core. Its input record
contains only the two Section 4 pressure estimates. These are now constructed
by `CoreRadiusBounds.verifiedConcreteSection4Input`; the preferred
`NoncompactProfile.gaussian_profile_circular_law_of_bbv` endpoint requests
only BBV and the profile/bandwidth assumptions. Its build, public-call tests,
841 axiom reports and seventeen module kernel replays passed at `0b33ba4`;
see [the separate certificate](../PRESSURE_INPUT_MIGRATION.md).
The older `gaussian_profile_circular_law_of_bbv_sources` API remains available.
The following older conditional route remains for compatibility:
`CircularLawSection6.NoncompactProfile.gaussian_profile_circular_law_of_concrete_sources`
also constructs the local Section 3 input from universal BBV and the classical
actual-Ginibre squared-singular bounded-test limit. It retains that specific
limiting-law source and Han, but not Gaussian log/negative/spectral fields;
there is no finite anchor or local-CDF certificate in the new caller record.

## Historical verification before the BC12 migration

The complete targeted proof build passed in
[run 33724679472](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33724679472)
at `fe24e7ea62df3985035840be465574f0f21d4142` (4435 dependency-inclusive jobs).
After correcting the audit driver's counter types, the build and both audits
passed in [run 33725000131](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33725000131)
at `c992bff30e9af6ddabcba04f113447cd48c27f20`: 93 new Section 5 declarations and
35 new Section 6 declarations were audited transitively. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. Mathematical hypotheses
are not discharged by this audit.

The Section 5-only main publication preserves all other chapters and library
registrations. All 316 repository-owned non-Section-5 modules in the combined
old-umbrella/new-endpoint import closure are byte-identical to main at
`3c2005e1ce2987e9fc211d10c156d70240b5b93e`; main's different Section 3 umbrella
is not imported. The Section 6 caller remains on `codex/section6-formalization`
and is not included in the Section 5-only main update.

Use the explicit new module imports; the historical umbrella targets and their
full verification manifests have not been expanded or rerun for this change.
The cloud check builds only the two new final modules and their dependencies,
then runs `PublishedSection3ConcreteAudit.lean` and `PublishedConcreteAudit.lean`.
No local Lean build or local toolchain/mathlib download was performed.
