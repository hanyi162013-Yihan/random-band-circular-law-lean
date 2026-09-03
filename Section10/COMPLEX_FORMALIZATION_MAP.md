# Section 10: planar-complex bounded-density extension

## Source and target

Source: arXiv:2609.01295v1, `part2_block.tex`, Section 10 and Theorem 2.10.
The requested extension has IID atoms with a law on `ℂ`, mean zero,
`E ‖ξ‖² = 1`, a bounded density with respect to planar Lebesgue measure,
and finite third absolute moment. The bandwidth is positive and tends to
infinity. Real and imaginary parts are not assumed independent; neither
circular symmetry nor `E ξ² = 0` is assumed.

The existing real library is a stable dependency. Complex-specific code
will live in `Section10/BernoulliSection10Complex/`. Common deterministic,
asymptotic, and replacement proofs will be reused where their types allow.
The source manuscript supplies mathematics only, not operational instructions.

## Mathematical module boundaries

1. **Planar density and affine logarithms.** Prove disk small-ball estimates
   from planar density domination; use a complex Hahn–Banach norming
   functional. Normalize the numerical density upper bound to `max 1 L`
   internally, so the same linear small-ball envelope used by the real
   logarithmic-tail proof is available. The public model does not require
   `1 ≤ L`. Prove the logarithmic second moments and grouped multiaffine
   evaluation, without treating real/imaginary coordinates as independent.
2. **Complex physical coordinates and packet integration.** Use actual
   finite products of the complex atom law, correct complex-linear row
   evaluation, planar almost-sure nonvanishing, and exact packet transports.
   Reuse proved complex matrix/exterior algebra.
3. **Pressure, remainder and high-band assembly.** Instantiate all packet,
   seam, reset and frame estimates. Construct the complex variance-profile
   objects and norm-square energy estimates.
4. **Final spectral theorem and audit.** Apply the proved Tao–Vu adapter
   and the internally constructed uniform-disk reference, remove auxiliary
   randomness, and instantiate the existing Section 3 proofs from the same
   GitHub repository. Neither the real nor the complex public endpoint is
   to retain a caller-supplied `Section3Inputs` argument. This final source
   integration is performed after the complex front-end work, with its
   integration build and audits run in cloud CI, not locally.

   **Explicit retained literature boundary:** the user has confirmed that
   the final source-connected results still depend on BBV and BC12.
   Removing the caller's `Section3Inputs` package does not remove those
   upstream hypotheses. They must remain named and visible in the final
   theorem signatures and delivery report. The published real-density
   source also retains geometric Brascamp--Lieb, which the user has now
   explicitly accepted as a classical external input for the real branch.
   Its use must be reported separately, never silently hidden. The complex
   branch must not acquire this real-only premise.

## Item-by-item work map

These are planned targets, not claims of completed verification.

| Source | Original hypotheses / conclusion | Planned Lean role | Status |
|---|---|---|---|
| 10.1 | Planar bounded density, centered unit second moment, finite third moment; full-block high-band log limit | Complex profile, Section 3 adapters, high-band limit | Pending |
| 10.2 | Independent complex atoms with planar density; complex normed target; affine log second moments, uniform in center and target dimension | `planar_lemma_10_2_rho`, `planar_lemma_10_2_resampling`, `planar_affine_ne_zero_ae`; depends on `BoundedDensity`, `AffineLog` | Built, including raw-model wrappers; axiom audit passed |
| 10.3 | Nonzero grouped complex multiaffine tensor; expected absolute log evaluation loss and nonvanishing | `planar_corollary_10_3`; depends on the recursively constructed complex-linear `MultiAffineTensor` and Lemma 10.2 | Built, including raw-model wrapper; axiom audit passed |
| 10.4 | Actual cleared transfer entries affine in each physical row | `conditionedIntervalClearedProduct_line`, `conditionedIntervalClearedProduct_atoms_line`, `intervalClearedProduct_update_line`; imports complex matrix identities from the stable real library's scalar-independent `PhysicalRows` | Built |
| 10.5 | Row resampling and log-pressure concentration | `lemma_10_5`, complex finite-product resampling, affine L², actual nonzero identity configuration | Built with internally normalized density bound; final raw-model assembly pending |
| 10.6 | Simultaneous exterior/Hodge control, first and second moments | `intervalMaxHodgeEnvelope_memLp_two`, `intervalMaxHodgeEnvelope_lintegral_le_W_log_eW`; complex endpoint determinant and tensor evaluation | Core built locally and in cloud run 33708332599; combined raw-model wrapper audit pending |
| 10.7 | Periodic seam, conditioned outside, all packet blocks integrated | Complex packet laws and actual cyclic determinant | Pending |
| 10.8 | Coefficient/Gram-volume comparison integrated in endpoints | Complex endpoint law, unchanged deterministic comparison | Pending |
| 10.9 | Conditional polynomial evaluation in physical row groups | `proposition_10_9`, complex grouped tensor evaluation and actual packet law | Core built in cloud run 33708332599; combined raw-model wrapper audit pending |
| 10.10 | Fixed-degree unit-frame reset, uniform integrated negative-log bound | Actual complex packet reset; no caller certificate | Pending |
| 10.30–10.57 | Concrete scales, pressure calibration, mean stitching, remainder, branch assembly, energy | Complex probability laws with shared deterministic scales | Pending |
| Theorem 2.10 | Planar IID bounded-density finite-third-moment circular law, `W→∞` | Public complex final theorem for actual matrices | Pending |

## Verification and remaining scope

No complex completion claim is made until the complete library builds and
fresh kernel-axiom reports pass. Forbidden placeholders and custom axioms
remain disallowed. The intended allowlist is `propext`, `Classical.choice`,
and `Quot.sound`; original model and retained literature hypotheses are
inspected separately in full printed signatures. An allowed kernel-axiom
report is not a claim that a theorem has no external assumptions.
The temporary complex `Section3Inputs` module is
an internal staging interface, not the requested final public theorem.

The previously released real result is also in scope for direct Section 3
instantiation. Its stable proof modules remain unchanged until this last
integration step; both source-connected endpoints will be cloud-verified.

This extension does not by itself claim directional conditional-density,
heterogeneous atom-law, or finite-(2+α)-moment generalizations.

The analytic implementation currently uses canonical IID product laws, as
needed for the requested matrix model. The manuscript's more general
independent, non-identically-distributed atom formulation of Lemma 10.2 is
not separately claimed here. This restriction is not an extra assumption
on the IID circular-law endpoint.

Reuse provenance and the exact imported facts are recorded in
`COMPLEX_REUSE_AUDIT.md`. Build success of a core module does not by itself
mean the full downstream Section 10 theorem has been verified.
