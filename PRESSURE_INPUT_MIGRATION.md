# Separate pressure-input construction

Status: **development; not yet Lean-verified**. The completed BC12 migration
is separately certified in
[GAUSSIAN_MIGRATION_VERIFICATION.md](GAUSSIAN_MIGRATION_VERIFICATION.md) and
was merged into main as `88baed3`. This extension does not invalidate or
extend that certificate until its own checks pass.

The proposed route connects the already proved finite Section 4 estimates
to the exact matrix observables used by Sections 5 and 6:

1. Prove that the calibration prefix is an IID marginal and that its outside
   rows equal the existing calibration restriction pointwise.
2. Transport the finite determinant/pressure seam and pressure concentration
   to the original full matrix sample space, including the empty suffix.
3. Construct all four fields of each finite quantitative pressure contract.
4. Apply these constructors to complex-density indicator bands and the
   actual clamped Gaussian profile cores.

The new proposed endpoints are
`PublishedSection3Concrete.indicator_complex_full_of_bbv` and
`NoncompactProfile.gaussian_profile_circular_law_of_bbv`.
Their only external literature premise should be uniform BBV; density,
moments, profile and bandwidth assumptions remain explicit model data.
The general construction allows finite constants to depend on the fixed
complex shift. No bounded-shift condition is introduced.

The real-density Section 5 endpoint still has its explicit pressure and
real geometric Brascamp–Lieb inputs. The taper's LSV/count/local-comparison
interfaces are also unchanged. No claim about these separate gaps is made.

The old source records and conditional endpoints are preserved. The extension
adds stronger callable endpoints and boundary regression examples rather
than changing the already verified record APIs again. New proofs use default
checking limits, disable implicit undeclared parameters and treat warnings
as errors. Verification will use normal cloud target builds, exhaustive
public-theorem axiom audits, explicit public-call regressions and kernel replay.
