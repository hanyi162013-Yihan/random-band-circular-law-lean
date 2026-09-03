# Local upstream source snapshots

Only Lean source dependency closures are copied; no upstream Lake directory was
downloaded or copied. Original namespaces are preserved; local module imports
acquire a `Vendor.` prefix. Copying source is not a claim that every endpoint
has been ported, checked, or connected to Proposition 3.6.

## Origins

- High-band LSV: https://github.com/hanyi162013-Yihan/high-band-lsv-2609-01295,
  local HEAD `d20607307ee57f31d77397b34bdb2910bef30936`, Lean 4.32.0.
  This is the published proof to reuse for manuscript Theorem 3.1.
  The planar-density endpoint has no external analytic interface. The real
  branch explicitly assumes `RealFiniteGeometricBrascampLieb`.
  No LICENSE was present in that checkout; local reuse was requested by its
  owner, and this file does not purport to relicense it.
- Ginibre LSV: https://github.com/hanyi162013-Yihan/ginibre-lsv-lean,
  local HEAD `0c7078d4b08235645084b6ef8a11fdda7f5f0475`, Lean 4.32.0.
  License: [Apache 2.0](Vendor/licenses/Ginibre.txt).
- SLT matrix infrastructure: the local dependency of the Ginibre project,
  with no Git metadata in the source directory.
  License: [Apache 2.0](Vendor/licenses/SLT.txt).
- Projection density: https://github.com/hanyi162013-Yihan/projection-density-theorem-formalization,
  local HEAD `45079c99499f8e8f7fe62301057e0ecd0d05f841`.
  License: [Apache 2.0](Vendor/licenses/Livshyts.txt).
- arXiv 2410.16457 v3 proof: the local Aug 27 project,
  local HEAD `2b1d12039dbb50f8e9e572766d98f8e280d77ccb`, Lean 4.33.0.
  License: [MIT](Vendor/licenses/Arxiv2410.txt).
  BBV Theorem 2.8 remains an explicit hypothesis.

The actual working files at the paths below were copied. A recorded HEAD does
not assert that a potentially dirty working file equals its committed version.
No original proof project or manuscript was modified.

For publication, workstation-only prefixes in provenance comments and this
table are replaced by `upstream-sources/`; the remaining project and file
names identify the original working sources. This changes no Lean command.
`SOURCE_MANIFEST.json` records SHA-256 hashes of the published payload,
not a substitute for the successful build and axiom audit.

## Local adaptations

- The 2026-09-02 integration additionally copies `ModelStatements.lean`,
  `PaperModelTheorem.lean`, and `ModelLawTransport.lean` from the clean
  high-band checkout at commit `d20607307ee57f31d77397b34bdb2910bef30936`.
  These copies change only local import prefixes.
- The umbrella `Mathlib` imports in
  `Section5Formalization/Section5Formalization.lean` and
  `LivshytsProjectionFormalization/ProbabilityCore.lean` are narrowed to
  their specific mathematical and tactic imports. Original source projects
  are unchanged. The no-cache serial build helper refuses umbrella
  `Mathlib` builds and records complete build logs under `audit/`.
- All local dependency imports in snapshots are prefixed with `Vendor.`.
- `TraceComparison.lean` replaces the umbrella `Mathlib.Tactic` import with
  the specific tactics used in its chain; statements and proof bodies unchanged.
- `PoissonCounting.lean` makes the same import-only narrowing for the
  scalar Poisson/counting lemmas used by the new smoothing proof.
- `HermitianStieltjes`, `RowReplacement`, `ResolventPerturbation`,
  `BVH/EntryResolvent`, and `BVH/ProductLindeberg` likewise replace the
  umbrella tactic import by the specific algebra/order tactics used;
  this avoids building unrelated tactic dependencies during integration.
- Compatibility edits for Lean/mathlib 4.33 are recorded here when applied.
- `PlanarSmallBall.lean`: replace the unavailable `mul_le_mul_right'`
  with `mul_le_mul'` and reflexivity for the unchanged volume factor.
- `NormalEvents.lean`: identify the unit-norm set with the sphere by
  unfolding `Metric.sphere`; this avoids the changed `convert`/`ext`
  behavior on a proposition-valued compactness goal.
- `LivshytsProjectionFormalization/ConcreteProjectionDensity.lean`:
  replace two unavailable `mul_le_mul_left'` calls with `mul_le_mul'`
  and reflexivity for the unchanged factor.
- `LivshytsProjectionFormalization/FiniteProductDensity.lean`: retain the
  finite-product Fubini induction, explicitly restate the successor-indexed
  product space, and prove the integrand equality coordinate by coordinate
  using `insertNth_apply_same` and `insertNth_apply_succAbove`. This avoids
  simplifying dependent casts and measurable-space instances together.
- `SLT/MatrixInfra/Basic.lean`: use explicit rewrites in the diagonal case of
  `orthonormal_leftSingularVector_of_singularValues_ne_zero`, avoiding broad
  simplification of the index subtype's singular-value predicate in mathlib 4.33.
- Upstream heartbeat settings only raise resource limits, not logical power.
  Checked proofs may not contain `sorry`, `admit`, `unsafe`, or custom axioms.
- New bridge proofs live under `ShortRingAnchor/`.

## Full source manifest (136 Lean files)

| New local file | Original working file |
| --- | --- |
| `Vendor/AnisotropicLabels.lean` | `upstream-sources/high-band-lsv-2609-01295/AnisotropicLabels.lean` |
| `Vendor/AnisotropicMesh.lean` | `upstream-sources/high-band-lsv-2609-01295/AnisotropicMesh.lean` |
| `Vendor/AnisotropicNetAssembly.lean` | `upstream-sources/high-band-lsv-2609-01295/AnisotropicNetAssembly.lean` |
| `Vendor/AnisotropicNetGeometry.lean` | `upstream-sources/high-band-lsv-2609-01295/AnisotropicNetGeometry.lean` |
| `Vendor/AnisotropicNets.lean` | `upstream-sources/high-band-lsv-2609-01295/AnisotropicNets.lean` |
| `Vendor/Arxiv2410/V3/BVH/AtomCovariance.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/AtomCovariance.lean` |
| `Vendor/Arxiv2410/V3/BVH/Coordinates.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/Coordinates.lean` |
| `Vendor/Arxiv2410/V3/BVH/EntryLindeberg.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/EntryLindeberg.lean` |
| `Vendor/Arxiv2410/V3/BVH/EntryResolvent.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/EntryResolvent.lean` |
| `Vendor/Arxiv2410/V3/BVH/GaussianConstruction.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/GaussianConstruction.lean` |
| `Vendor/Arxiv2410/V3/BVH/GaussianModelMoments.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/GaussianModelMoments.lean` |
| `Vendor/Arxiv2410/V3/BVH/GaussianMoments.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/GaussianMoments.lean` |
| `Vendor/Arxiv2410/V3/BVH/ModelMoments.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/ModelMoments.lean` |
| `Vendor/Arxiv2410/V3/BVH/ProductLindeberg.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/ProductLindeberg.lean` |
| `Vendor/Arxiv2410/V3/BVH/Remark613.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/Remark613.lean` |
| `Vendor/Arxiv2410/V3/BVH/TraceUniversality.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/BVH/TraceUniversality.lean` |
| `Vendor/Arxiv2410/V3/ComplexMcDiarmid.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/ComplexMcDiarmid.lean` |
| `Vendor/Arxiv2410/V3/ConcreteEtaNet.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/ConcreteEtaNet.lean` |
| `Vendor/Arxiv2410/V3/Corollary35.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Corollary35.lean` |
| `Vendor/Arxiv2410/V3/DiagonalCorrection.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/DiagonalCorrection.lean` |
| `Vendor/Arxiv2410/V3/DoobBridge.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/DoobBridge.lean` |
| `Vendor/Arxiv2410/V3/EtaUniformization.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/EtaUniformization.lean` |
| `Vendor/Arxiv2410/V3/External/VanHandel.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/External/VanHandel.lean` |
| `Vendor/Arxiv2410/V3/FixedZImaginaryBound.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/FixedZImaginaryBound.lean` |
| `Vendor/Arxiv2410/V3/FreeDysonExistence.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/FreeDysonExistence.lean` |
| `Vendor/Arxiv2410/V3/GaussianDiagonal.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/GaussianDiagonal.lean` |
| `Vendor/Arxiv2410/V3/HermitianStieltjes.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/HermitianStieltjes.lean` |
| `Vendor/Arxiv2410/V3/McDiarmid.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/McDiarmid.lean` |
| `Vendor/Arxiv2410/V3/McDiarmidArithmetic.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/McDiarmidArithmetic.lean` |
| `Vendor/Arxiv2410/V3/Model.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Model.lean` |
| `Vendor/Arxiv2410/V3/ModelMcDiarmidBridge.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/ModelMcDiarmidBridge.lean` |
| `Vendor/Arxiv2410/V3/PoissonCounting.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/PoissonCounting.lean` |
| `Vendor/Arxiv2410/V3/ProbabilityEvent.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/ProbabilityEvent.lean` |
| `Vendor/Arxiv2410/V3/Proposition34.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34.lean` |
| `Vendor/Arxiv2410/V3/Proposition34Canonical.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34Canonical.lean` |
| `Vendor/Arxiv2410/V3/Proposition34Complete.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34Complete.lean` |
| `Vendor/Arxiv2410/V3/Proposition34Dyson.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34Dyson.lean` |
| `Vendor/Arxiv2410/V3/Proposition34McDiarmid.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34McDiarmid.lean` |
| `Vendor/Arxiv2410/V3/Proposition34OnlyBBV.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34OnlyBBV.lean` |
| `Vendor/Arxiv2410/V3/Proposition34RowMcDiarmid.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34RowMcDiarmid.lean` |
| `Vendor/Arxiv2410/V3/Proposition34Uniform.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/Proposition34Uniform.lean` |
| `Vendor/Arxiv2410/V3/RandomModel.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/RandomModel.lean` |
| `Vendor/Arxiv2410/V3/RateArithmetic.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/RateArithmetic.lean` |
| `Vendor/Arxiv2410/V3/RateArithmeticAllEta.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/RateArithmeticAllEta.lean` |
| `Vendor/Arxiv2410/V3/ResolventPerturbation.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/ResolventPerturbation.lean` |
| `Vendor/Arxiv2410/V3/RowIndependence.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/RowIndependence.lean` |
| `Vendor/Arxiv2410/V3/RowReplacement.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/RowReplacement.lean` |
| `Vendor/Arxiv2410/V3/RowSensitivity.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/RowSensitivity.lean` |
| `Vendor/Arxiv2410/V3/ScalarConcentration.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/ScalarConcentration.lean` |
| `Vendor/Arxiv2410/V3/ScalarDysonBound.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/ScalarDysonBound.lean` |
| `Vendor/Arxiv2410/V3/TraceComparison.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/TraceComparison.lean` |
| `Vendor/Arxiv2410/V3/TraceMeasurability.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/TraceMeasurability.lean` |
| `Vendor/Arxiv2410/V3/VarianceProfile.lean` | `upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/VarianceProfile.lean` |
| `Vendor/BlockGeometry.lean` | `upstream-sources/high-band-lsv-2609-01295/BlockGeometry.lean` |
| `Vendor/FiniteProbability.lean` | `upstream-sources/high-band-lsv-2609-01295/FiniteProbability.lean` |
| `Vendor/FixedNormalProbability.lean` | `upstream-sources/high-band-lsv-2609-01295/FixedNormalProbability.lean` |
| `Vendor/GinibreLSV/Conditioning.lean` | `upstream-sources/i-2/work/ginibre-lsv-lean/GinibreLSV/Conditioning.lean` |
| `Vendor/GinibreLSV/Deterministic.lean` | `upstream-sources/i-2/work/ginibre-lsv-lean/GinibreLSV/Deterministic.lean` |
| `Vendor/GinibreLSV/GaussianSmallBall.lean` | `upstream-sources/i-2/work/ginibre-lsv-lean/GinibreLSV/GaussianSmallBall.lean` |
| `Vendor/GinibreLSV/Ginibre.lean` | `upstream-sources/i-2/work/ginibre-lsv-lean/GinibreLSV/Ginibre.lean` |
| `Vendor/GinibreLSV/GinibreSmoothed.lean` | `upstream-sources/i-2/work/ginibre-lsv-lean/GinibreLSV/GinibreSmoothed.lean` |
| `Vendor/GinibreLSV/Probability.lean` | `upstream-sources/i-2/work/ginibre-lsv-lean/GinibreLSV/Probability.lean` |
| `Vendor/HighBandLSV.lean` | `upstream-sources/high-band-lsv-2609-01295/HighBandLSV.lean` |
| `Vendor/InternalNet.lean` | `upstream-sources/high-band-lsv-2609-01295/InternalNet.lean` |
| `Vendor/LivshytsProjectionFormalization.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization.lean` |
| `Vendor/LivshytsProjectionFormalization/ConcreteFiberBL.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/ConcreteFiberBL.lean` |
| `Vendor/LivshytsProjectionFormalization/ConcreteProjectionDensity.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/ConcreteProjectionDensity.lean` |
| `Vendor/LivshytsProjectionFormalization/DensityScaling.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/DensityScaling.lean` |
| `Vendor/LivshytsProjectionFormalization/EntropyJacobian.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/EntropyJacobian.lean` |
| `Vendor/LivshytsProjectionFormalization/FiniteProductDensity.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/FiniteProductDensity.lean` |
| `Vendor/LivshytsProjectionFormalization/GeometricBrascampLieb.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/GeometricBrascampLieb.lean` |
| `Vendor/LivshytsProjectionFormalization/KernelCoordinateFrame.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/KernelCoordinateFrame.lean` |
| `Vendor/LivshytsProjectionFormalization/OrthogonalProjectionCoarea.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/OrthogonalProjectionCoarea.lean` |
| `Vendor/LivshytsProjectionFormalization/ProbabilityCore.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/ProbabilityCore.lean` |
| `Vendor/LivshytsProjectionFormalization/ProjectionSmallBall.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/ProjectionSmallBall.lean` |
| `Vendor/LivshytsProjectionFormalization/ProjectionWithoutCoarea.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/ProjectionWithoutCoarea.lean` |
| `Vendor/LivshytsProjectionFormalization/RandomVectorProjection.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/RandomVectorProjection.lean` |
| `Vendor/LivshytsProjectionFormalization/RealComplexCorrespondence.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/RealComplexCorrespondence.lean` |
| `Vendor/LivshytsProjectionFormalization/Section5TargetFormalization.lean` | `upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/Section5TargetFormalization.lean` |
| `Vendor/LSVAssembly.lean` | `upstream-sources/high-band-lsv-2609-01295/LSVAssembly.lean` |
| `Vendor/MatrixColumnBound.lean` | `upstream-sources/high-band-lsv-2609-01295/MatrixColumnBound.lean` |
| `Vendor/MatrixGeometry.lean` | `upstream-sources/high-band-lsv-2609-01295/MatrixGeometry.lean` |
| `Vendor/MeshParameters.lean` | `upstream-sources/high-band-lsv-2609-01295/MeshParameters.lean` |
| `Vendor/ModelNumerics.lean` | `upstream-sources/high-band-lsv-2609-01295/ModelNumerics.lean` |
| `Vendor/ModelLawTransport.lean` | `upstream-sources/high-band-lsv-2609-01295/ModelLawTransport.lean` |
| `Vendor/ModelStatements.lean` | `upstream-sources/high-band-lsv-2609-01295/ModelStatements.lean` |
| `Vendor/ModelPartition.lean` | `upstream-sources/high-band-lsv-2609-01295/ModelPartition.lean` |
| `Vendor/NeighborPath.lean` | `upstream-sources/high-band-lsv-2609-01295/NeighborPath.lean` |
| `Vendor/NormalEvents.lean` | `upstream-sources/high-band-lsv-2609-01295/NormalEvents.lean` |
| `Vendor/NormalNetEvents.lean` | `upstream-sources/high-band-lsv-2609-01295/NormalNetEvents.lean` |
| `Vendor/PathGeometry.lean` | `upstream-sources/high-band-lsv-2609-01295/PathGeometry.lean` |
| `Vendor/PaperModelTheorem.lean` | `upstream-sources/high-band-lsv-2609-01295/PaperModelTheorem.lean` |
| `Vendor/PlanarModelTheorem.lean` | `upstream-sources/high-band-lsv-2609-01295/PlanarModelTheorem.lean` |
| `Vendor/PlanarNets.lean` | `upstream-sources/high-band-lsv-2609-01295/PlanarNets.lean` |
| `Vendor/PlanarNormalTheorem.lean` | `upstream-sources/high-band-lsv-2609-01295/PlanarNormalTheorem.lean` |
| `Vendor/PlanarRowBounds.lean` | `upstream-sources/high-band-lsv-2609-01295/PlanarRowBounds.lean` |
| `Vendor/PlanarSmallBall.lean` | `upstream-sources/high-band-lsv-2609-01295/PlanarSmallBall.lean` |
| `Vendor/PlanarTensorization.lean` | `upstream-sources/high-band-lsv-2609-01295/PlanarTensorization.lean` |
| `Vendor/ProductEvents.lean` | `upstream-sources/high-band-lsv-2609-01295/ProductEvents.lean` |
| `Vendor/QuadraticLinearization.lean` | `upstream-sources/high-band-lsv-2609-01295/QuadraticLinearization.lean` |
| `Vendor/RadialLedger.lean` | `upstream-sources/high-band-lsv-2609-01295/RadialLedger.lean` |
| `Vendor/RadialNetAssembly.lean` | `upstream-sources/high-band-lsv-2609-01295/RadialNetAssembly.lean` |
| `Vendor/RadialRawBound.lean` | `upstream-sources/high-band-lsv-2609-01295/RadialRawBound.lean` |
| `Vendor/RandomMatrixModel.lean` | `upstream-sources/high-band-lsv-2609-01295/RandomMatrixModel.lean` |
| `Vendor/RealAnisotropicGeometry.lean` | `upstream-sources/high-band-lsv-2609-01295/RealAnisotropicGeometry.lean` |
| `Vendor/RealColumnExposure.lean` | `upstream-sources/high-band-lsv-2609-01295/RealColumnExposure.lean` |
| `Vendor/RealColumnSmallBall.lean` | `upstream-sources/high-band-lsv-2609-01295/RealColumnSmallBall.lean` |
| `Vendor/RealFixedNormalProbability.lean` | `upstream-sources/high-band-lsv-2609-01295/RealFixedNormalProbability.lean` |
| `Vendor/RealFormSmallBall.lean` | `upstream-sources/high-band-lsv-2609-01295/RealFormSmallBall.lean` |
| `Vendor/RealLSVAssembly.lean` | `upstream-sources/high-band-lsv-2609-01295/RealLSVAssembly.lean` |
| `Vendor/RealMatrixColumnBound.lean` | `upstream-sources/high-band-lsv-2609-01295/RealMatrixColumnBound.lean` |
| `Vendor/RealMatrixForms.lean` | `upstream-sources/high-band-lsv-2609-01295/RealMatrixForms.lean` |
| `Vendor/RealModelTheorem.lean` | `upstream-sources/high-band-lsv-2609-01295/RealModelTheorem.lean` |
| `Vendor/RealNetCost.lean` | `upstream-sources/high-band-lsv-2609-01295/RealNetCost.lean` |
| `Vendor/RealNetProbability.lean` | `upstream-sources/high-band-lsv-2609-01295/RealNetProbability.lean` |
| `Vendor/RealNormalNetEvents.lean` | `upstream-sources/high-band-lsv-2609-01295/RealNormalNetEvents.lean` |
| `Vendor/RealNormalTheorem.lean` | `upstream-sources/high-band-lsv-2609-01295/RealNormalTheorem.lean` |
| `Vendor/RealProjectionAdapter.lean` | `upstream-sources/high-band-lsv-2609-01295/RealProjectionAdapter.lean` |
| `Vendor/RealProjectionInterface.lean` | `upstream-sources/high-band-lsv-2609-01295/RealProjectionInterface.lean` |
| `Vendor/RealProjectionSmallBall.lean` | `upstream-sources/high-band-lsv-2609-01295/RealProjectionSmallBall.lean` |
| `Vendor/RealRandomMatrixModel.lean` | `upstream-sources/high-band-lsv-2609-01295/RealRandomMatrixModel.lean` |
| `Vendor/RealRawBound.lean` | `upstream-sources/high-band-lsv-2609-01295/RealRawBound.lean` |
| `Vendor/RealRowBounds.lean` | `upstream-sources/high-band-lsv-2609-01295/RealRowBounds.lean` |
| `Vendor/RealSmallBallNumerics.lean` | `upstream-sources/high-band-lsv-2609-01295/RealSmallBallNumerics.lean` |
| `Vendor/RealTensorization.lean` | `upstream-sources/high-band-lsv-2609-01295/RealTensorization.lean` |
| `Vendor/RealWeightedGeometry.lean` | `upstream-sources/high-band-lsv-2609-01295/RealWeightedGeometry.lean` |
| `Vendor/Section5Formalization.lean` | `upstream-sources/high-band-lsv-2609-01295/Section5Formalization.lean` |
| `Vendor/Section5Formalization/BlockEnergy.lean` | `upstream-sources/high-band-lsv-2609-01295/Section5Formalization/BlockEnergy.lean` |
| `Vendor/Section5Formalization/CyclicPartition.lean` | `upstream-sources/high-band-lsv-2609-01295/Section5Formalization/CyclicPartition.lean` |
| `Vendor/Section5Formalization/DeterministicCompletion.lean` | `upstream-sources/high-band-lsv-2609-01295/Section5Formalization/DeterministicCompletion.lean` |
| `Vendor/Section5Formalization/ExponentLedger.lean` | `upstream-sources/high-band-lsv-2609-01295/Section5Formalization/ExponentLedger.lean` |
| `Vendor/Section5Formalization/MatrixNormal.lean` | `upstream-sources/high-band-lsv-2609-01295/Section5Formalization/MatrixNormal.lean` |
| `Vendor/Section5Formalization/Section5Formalization.lean` | `upstream-sources/high-band-lsv-2609-01295/Section5Formalization/Section5Formalization.lean` |
| `Vendor/Section5Formalization/VolumetricNet.lean` | `upstream-sources/high-band-lsv-2609-01295/Section5Formalization/VolumetricNet.lean` |
| `Vendor/SLT/MatrixInfra/Basic.lean` | `upstream-sources/i-2/work/deps/slt/SLT/MatrixInfra/Basic.lean` |
| `Vendor/SLT/MatrixInfra/CourantFischer.lean` | `upstream-sources/i-2/work/deps/slt/SLT/MatrixInfra/CourantFischer.lean` |
