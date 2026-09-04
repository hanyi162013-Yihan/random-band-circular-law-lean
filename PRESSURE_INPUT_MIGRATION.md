# Separate pressure-input construction

Status: **Section 5 and Section 6 verified, 2026-09-04 UTC**. The completed BC12 migration
is separately certified in
[GAUSSIAN_MIGRATION_VERIFICATION.md](GAUSSIAN_MIGRATION_VERIFICATION.md) and
was merged into main as `88baed3`. This extension does not invalidate or
extend that certificate. The separate evidence for this extension is below.

The route connects the already proved finite Section 4 estimates
to the exact matrix observables used by Sections 5 and 6:

1. Prove that the calibration prefix is an IID marginal and that its outside
   rows equal the existing calibration restriction pointwise.
2. Transport the finite determinant/pressure seam and pressure concentration
   to the original full matrix sample space, including the empty suffix.
3. Construct all four fields of each finite quantitative pressure contract.
4. Apply these constructors to complex-density indicator bands and the
   actual clamped Gaussian profile cores.

The new endpoints are
`PublishedSection3Concrete.indicator_complex_full_of_bbv` and
`NoncompactProfile.gaussian_profile_circular_law_of_bbv`.
Their only external literature premise is uniform BBV; density,
moments, profile and bandwidth assumptions remain explicit model data.
The general construction allows finite constants to depend on the fixed
complex shift. No bounded-shift condition is introduced.

## New declarations

`section5/CircularLawSections56/Section5/VerifiedComplexPressureInputs.lean`
proves the eight finite-model lemmas:

- `normalized_profile_lower_scale_le_one`
- `complex_literalModelPressure_inputs`
- `complex_literalModelRawDeterminant_seam`
- `literalPressurePrefix_measurePreserving`
- `literalCalibrationRows_eq_prefix_suffix`
- `complex_literalModelCalibrationRaw_seam`
- `complex_literalModelCalibration_quantitative`
- `complex_literalModelFinal_quantitative`

They are in `CircularLawSections56.Section5` and take only explicit model,
moment, density and finite-geometry hypotheses, with no literature input.
`VerifiedComplexSection5Endpoint.lean` adds
`PublishedSection3Concrete.indicator_complex_full_of_bbv`.
`section6/CircularLawSection6/VerifiedCorePressure.lean` adds
`CoreRadiusBounds.verifiedConcreteSection4Input` and
`NoncompactProfile.gaussian_profile_circular_law_of_bbv`.
The core constructor itself does not require BBV; the final two circular-law
endpoints do. Each subproject also has a new `VerifiedPressureRegression.lean`
with direct calls that do not supply a pressure certificate. All three proof
modules are included in the public imports, axiom audits and kernel replay.

## Preserved interfaces outside this task

The real-density Section 5 endpoint still has its explicit pressure and
real geometric Brascamp–Lieb inputs. The taper's LSV/count/local-comparison
interfaces are also unchanged. These are pre-existing conditional interfaces,
outside this migration's agreed scope, not additional completion requirements
or regressions caused by this work.

These real-density and taper branches are not premises of the Gaussian
Section 6 endpoint above. Importing and applying a proved Section 4 or Section 5
theorem is an ordinary internal dependency; an estimate still appearing as a
caller-supplied argument is an undischarged interface at that particular
endpoint. This extension removes the latter for the complex Section 5 and
Gaussian Section 6 pressure contracts, without claiming to close every branch.

The old source records and conditional endpoints are preserved. The extension
adds stronger callable endpoints and boundary regression examples rather
than changing the already verified record APIs again. New proofs use default
checking limits, disable implicit undeclared parameters and treat warnings
as errors. Verification uses normal cloud target builds, exhaustive
public-theorem axiom audits, explicit public-call regressions and kernel replay.

## Separate verification evidence

Section 5 passed [run 33827692255](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33827692255),
job `100883756017`, at source commit
`71363294144cc6f292db19a5702d3db5a3da9cd8`:

- Ordinary `lake --no-cache build CircularLawSections56`: passed, 4466 jobs.
- Three audit files: 1118 reports, including every one of the 874 named public
  Section 5/bridge source theorems. Only `propext`, `Classical.choice` and
  `Quot.sound` are permitted.
- `VerifiedPressureRegression.lean`: passed without either pressure premise.
- Eight module kernel replays: passed with exact coverage. This is Lean's own
  kernel checker, not an independent external verifier or a replay of mathlib.
- Report artifact `9920626057`, 28329 bytes, SHA-256
  `16cae0ade054ddd93005e709a7ae391f792070d703f060e368154b2e05ca5255`.

Section 6 passed [run 33831340031](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33831340031),
job `100894797135`, at source commit
`0b33ba4575b0c283ae8abf81f17e6490a764b7e9`:

- Ordinary `lake --no-cache build CircularLawSection6 CircularLawSection6.GinibreFiniteFormulaSources`:
  passed, 4586 jobs.
- Two audit files: 841 reports, including every one of the 810 named public
  Section 6 source theorems. Only the same three standard axioms occur.
- `Regression.lean`, `BBVOnlyRegression.lean` and `VerifiedPressureRegression.lean`:
  all passed. The last file calls both new declarations without supplying any
  pressure or Gaussian-limit certificate.
- Seventeen module kernel replays: passed with exact coverage, including
  `CircularLawSection6.VerifiedCorePressure`.
- Report artifact `9921891784`, 21515 bytes, SHA-256
  `fe349c474c29348502d55feed4fe144c89522b086f34c21a483a4577de445784`.

All eleven new named theorems are covered. Section 5 Lean sources are unchanged
between its successful `7136329` run and the final `0b33ba4` run. Subsequent
documentation/checksum-only publication changes do not change these proofs.

The initial pressure run did not share the old development branch's GitHub
cache scope and rebuilt dependencies. Its cache was saved; the successful
Section 5 retry restored it and checked unchanged modules through Lake's
normal trace validation. No cache, timestamp or proof artifact was fabricated.
No local Lean build, toolchain download or Mathlib cache download was used.

The Section 3/4/8/10 proof sources and dependency pins are unchanged from the
merged Gaussian-source checkpoint. Their earlier certificate remains valid;
the extra checks here concern the Section 5/6 targets, not a new claim about
unmodified later-chapter proofs. The old conditional record APIs are unchanged.
