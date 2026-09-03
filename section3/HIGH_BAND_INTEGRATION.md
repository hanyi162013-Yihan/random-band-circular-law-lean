# Hermitization counting and the published Theorem 3.1

## Verification status

The complete build and axiom audit **passed on 2026-09-03 UTC**, at proof-source
commit `79798346f1cc9dda9cfd0c5bf2c3044aea5162a9`.
[Successful GitHub run](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33702782802).

- All **230 Lean source files** are included in the successfully checked
  serial import closure, including both Proposition 3.6 endpoints.
- The normal `lake --no-cache build` passed.
- `Audit.lean` produced **207** exact reports and `HighBandIntegrationAudit.lean`
  produced **64**: **271 reports covering 260 distinct declarations**.
- Every report uses only `propext`, `Classical.choice`, and/or `Quot.sound`.
  Missing, duplicate, unexpected, or nonstandard-axiom reports fail the check.
- The source scan found no active proof placeholder, custom axiom, unsafe
  declaration, native-decide shortcut, or unapproved option.
- The cached remote verification took approximately **10 minutes 25 seconds**,
  including toolchain/dependency setup, the complete scoped build, and audits.

Both density endpoints were also built locally. This includes their cyclic
law adapters, numerical reindexing, and HS cutoff removal. The real theorem
retains its explicit geometric BL premise; an axiom audit does not discharge it.
The complete local repeat subsequently passed as well: normal `lake build`,
all 271 exact reports, and the 230-file source scan.

The durable [GitHub job log](audit/github-verification-2026-09-03.log) and
[verification summary](audit/github-verification-2026-09-03.json) record this run.
Exact individual kernel reports and the generated `summary.json` are in the
[run artifact](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33702782802/artifacts/9874344264).

The independent package is published under the paper-wide repository's
`section3/` directory. The historical first remote attempt was
[GitHub Actions run 33701162416](https://github.com/hanyi162013-Yihan/random-band-circular-law-lean/actions/runs/33701162416),
at source commit `3a16167bb50baa1446d037734617716f6a13c674`.
That run checked 221 of its 227 selected modules, then stopped at a `simp`
compatibility error in `Theorem31CyclicReal.lean`. The normalization identity
now uses explicit `withDensity_apply` and `restrict_univ` rewrites. The first
run is not a successful full-build certificate; its compiled artifacts are
saved for the corrected run. The dedicated workflow
does not build other chapters. Existing project directories are untouched.

## Mathematical reconstruction

The counting proof uses the exact cutoff

```text
a_M = B_M^(-1/8) M^tau,     B_M a_M^8 = M^(8 tau).
```

The v3 pointwise comparison and McDiarmid estimate are applied on a finite
vertical grid with spacing `M^-2`. Its complement has probability at most
`4 M^-8` in all sufficiently large dimensions. The canonical free Stieltjes
transform has norm below one; grid interpolation gives norm at most three.
The Poisson kernel then gives, on one common event, for every `r >= a_M`,

```text
# {Hermitization eigenvalues in [-r,r]} <= 6 M (2r).
```

For `r > 1` the dimension bound suffices. This is the actual shifted matrix,
not a separately assumed spectral family. BBV remains the named external
comparison. The resulting Proposition 3.6 endpoint has no `hCount`, no
externally supplied counting event, and no externally chosen counting constant.

The Theorem 3.1 proof is copied from the user's high-band project at commit
`d20607307ee57f31d77397b34bdb2910bef30936`, not introduced as a hypothesis.
The new adapters establish:

1. The cyclic profile satisfies the source lower/upper variance bounds with
   constants `c0/3` and `C0`, and has row normalization one.
2. Independence and matching entry laws identify the full matrix law with
   the source product model, including deterministic off-band zeros.
3. For the real branch, an essentially bounded density has an everywhere
   bounded measurable representative with the same law. An almost surely
   real atom has the law of its real-part embedding.
4. The numerical certificates hold along arbitrary `M k -> infinity`,
   without requiring the dimensions to be injective or strictly increasing.
5. The two definitions of the least singular value agree. With `t=M^-2`,
   the source threshold is exactly `exp(-sourceHardEdgeScale)`.
6. The strict lower-tail event with HS cutoff is Borel and transports under
   equality of matrix laws. The source's non-strict estimate bounds it.
7. `HS(X)^2/M` equals the empirical singular-value second moment. Its
   expectation is one. Markov and the proved two-limit argument remove
   the HS cutoff without adding a concentration premise.

All shifts `z : Complex` are allowed; bounds may depend on the fixed shift.
Neither a radius-five condition nor a bound `|z| <= 2.5` is introduced.

## Endpoint boundary

The most concrete planar endpoint is
`proposition36_cyclicShortRing_planar_from_published_theorem31`.
The real/complex-alternative endpoint is
`proposition36_cyclicShortRing_from_published_theorem31`.
Both construct the former `hCount` and `hLSV` inputs internally.

The remaining literature premises are explicit theorem parameters:

- BBV's canonical Gaussian-to-free comparison. For the ring it is supplied
  on the upper half-plane, covering both the vertical counting grid and
  horizontal smoothing lines; for the dense process only the latter are needed.
- The BC12 shifted negative-moment tightness input. The previously proved
  polynomial-least-value/mesoscopic-count reduction remains available.
- The BC12 full logdet convergence input. The previously proved finite-formula
  theorem can supply it; Gaussian moment/correlation formulas are not inferred
  merely from normalized independent entries.
- Only for the real branch: `RealFiniteGeometricBrascampLieb`, exactly the
  premise present in the copied upstream proof. The planar endpoint does
  not require it.

There are no new least-value, joint-law, singular-vector-measurability,
HS-concentration, local CDF, or Hermitization-count hypotheses.

## Remaining work after this integration

The next short route for the BC12 negative-moment boundary is to identify
the actual normalized shifted Gaussian law with the already available
polynomial least-value estimate, and combine it with the dense specialization
of the counting constructor above. The deterministic summation and
high-probability-to-tightness steps are already proved in
`BC12/NegativeMomentCounting.lean`; no new Stieltjes smoothing is required.
The finite-formula logdet route is separate and remains explicitly conditional
on its exact Ginibre formulas. Neither BBV nor the real geometric BL theorem
is claimed to be proved by this integration.

## New source files

All paths in this table are under `ShortRingAnchor/`.

| File | Role |
| --- | --- |
| `VerticalStieltjesCounting.lean` | Vertical grid, resolvent interpolation, finite counting and probability bound |
| `HermitizationCountingFromV3.lean` | Exact cutoff arithmetic and actual-model all-cutoff event |
| `Proposition36Counting.lean` | Proposition 3.6 with counting input discharged |
| `CyclicHighBandProfile.lean` | Cyclic support and source variance-profile bounds |
| `UniformSequenceSelection.lean` | Uniformization over all admissible width sequences |
| `HighBandUniformNumerics.lean` | Reindex the copied numerical certificates |
| `CyclicPlanarHighBandModel.lean` | Planar product model and equality of matrix laws |
| `HighBandLSVBridge.lean` | Exact scalar, measurable-event, and second-moment identities |
| `HighBandLSVProbability.lean` | Apply the copied planar theorem and remove the HS cutoff |
| `Theorem31CyclicPlanar.lean` | Actual cyclic least-value conclusion, planar branch |
| `BoundedDensityRepresentative.lean` | Everywhere bounded measurable density representative |
| `CyclicRealHighBandModel.lean` | Real product model and equality of matrix laws |
| `HighBandRealLSVProbability.lean` | Apply the copied real theorem, retaining its BL premise |
| `Theorem31CyclicReal.lean` | Actual cyclic least-value conclusion, real/alternative branches |
| `Proposition36Planar.lean` | Planar Proposition 3.6 with counting and Theorem 3.1 connected |
| `Proposition36PublishedTheorem31.lean` | Real/complex-alternative Proposition 3.6 endpoint |
| `HighBandIntegrationAudit.lean` | Audit all new declarations and fourteen retained upstream endpoints |

Three additional copied files are `Vendor/ModelLawTransport.lean`,
`Vendor/ModelStatements.lean`, and `Vendor/PaperModelTheorem.lean`.
Their provenance and all compatibility edits are listed in [UPSTREAM.md](UPSTREAM.md).
The new helpers are `scripts/serial-upstream-build.mjs`,
`scripts/verify-project.mjs`, `scripts/export-source.mjs`, and
`scripts/audit-lean-sources.mjs`. The source scanner checks all project/vendored Lean
sources outside hidden dependency directories, excluding comments and strings;
it is a hygiene check, not a substitute for kernel verification.

No manuscript or original proof project is changed. No Lake directory is
copied or removed; all dependencies are built from existing local sources.
Failed development logs are retained for diagnostics, not counted as
verification certificates.

## New theorem inventory

All names below are in `ShortRingAnchor`. The first group has no external
literature-conclusion premise; it can still take explicit deterministic
bounds or probability/model hypotheses. The second group retains the named
literature boundary. Build status is the one stated at the top, not inferred
from membership in this list.

Internal deterministic and probabilistic deductions:

- `verticalGrid_cover`, `verticalStieltjesGridGood_norm_le_three`,
  `smallHermitizationEigenvalueIndices_eq_v3`, `verticalStieltjesGridGood_count`,
  `verticalStieltjesGridGood_bad_le`;
- `hardEdgeCutoff_eighth_power`, `hardEdgeCutoff_lower`,
  `eventually_formula311Error_hardEdge`;
- `exists_cyclicColumn_of_cyclicDist_le`, `cyclicVarianceCoefficient_local_floor`,
  `cyclicVarianceCoefficient_upper`,
  `HasBoundedDensityWithRespectTo.exists_pos_measure_le`;
- `eventually_uniform_of_eventually_every_sequence`,
  `eventually_highBandNumerics_uniform_width`, `eventually_highBandNumerics_along_dimensions`;
- `identDistrib_matrix_of_independent_entries`, `planarBandModel_entries_independent`,
  `planarBandModel_entry_law`, `cyclicPlanarBandModel_matrix_identDistrib`;
- `ginibreLeastSingularValue_eq_last`, `highBand_threshold_eq_source_exp`,
  `isOpen_leastSingularValue_lt`, `measurableSet_highBand_strict_bad`,
  `highBand_strict_bad_le_of_identDistrib`,
  `empiricalSecondMoment_zero_eq_hilbertSchmidt_sq`;
- `planar_lsv_of_highBandNumericalCertificates`, `eventually_planar_lsv_along_dimensions`,
  `hsCutoff_of_empiricalSecondMoment_le`, `highBandLSV_failure_tendsto_zero`,
  `theorem31MinimumInput_of_truncated_estimate`,
  `theorem31MinimumSingularValueInput_cyclic_planar`;
- `HasBoundedDensityWithRespectTo.exists_measurable_bounded_density`,
  `realBandModel_entries_independent`, `identDistrib_realPart_embedding`,
  `realBandModel_entry_law`, `cyclicRealBandModel_matrix_identDistrib`.

Conditional deductions:

- BBV: `hermitizationAllCutoffsCountingInput_of_v3_model`,
  `hermitizationAllCutoffsCountingInput_cyclic`.
- Real geometric BL: `real_lsv_of_highBandNumericalCertificates`,
  `eventually_real_lsv_along_dimensions`,
  `theorem31MinimumSingularValueInput_cyclic_real`,
  `theorem31MinimumSingularValueInput_cyclic_of_densityAlternative`.
- BBV + BC12: `proposition36_cyclicShortRing_planar_from_published_theorem31`.
- BBV + BC12 + real geometric BL:
  `proposition36_cyclicShortRing_from_published_theorem31`.
- Intermediate version also accepting `hLSV`:
  `proposition36_cyclicShortRing_of_atom_copies_bbv_and_lsv`.

The audited auxiliary definitions are `verticalGridHeight`,
`verticalStieltjesGridGood`, `HighBandNumericalCertificates`,
`cyclicPlanarBandModel`, and `cyclicRealBandModel`.
