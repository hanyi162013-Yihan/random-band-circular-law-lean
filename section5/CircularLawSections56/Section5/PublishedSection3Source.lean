import ShortRingAnchor.Proposition36Planar
import ShortRingAnchor.Proposition36PublishedTheorem31
import CircularLawSections56.Section6.PhysicalReplacementBridge

/-! # Direct calls to the checked Section 3 density endpoints

These records contain ensemble data and the published theorem's explicit
literature hypotheses, not a short-ring convergence conclusion. Both calls
below use the actual copied Proposition 3.6 proof. In particular least-value,
counting, nonsingularity and local CDF conclusions are not additional inputs.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open ShortRingAnchor Arxiv2410V3
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace CircularLawSections56.Section5

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} {νA νG : Measure ℂ}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure νA] [IsProbabilityMeasure νG]
variable {M W : ℕ → ℕ} [∀ n, Nonempty (Fin (M n))] {c₀ C₀ : ℝ}

/-- Fixed-law ensemble data for the actual cyclic and normalized dense models.
No independence across different dimensions or between the two models is required. -/
structure PublishedSection3Model (μ : Measure Ω) (νA νG : Measure ℂ)
    (M W : ℕ → ℕ) (c₀ C₀ : ℝ) where
  weights : ∀ n, AdmissibleWeights (W n) c₀ C₀
  fit : ∀ n, 2 * W n + 1 ≤ M n
  dimension_pos : ∀ n, 0 < M n
  ringEntry : ∀ n, Ω → Fin (M n) → BandOffset (W n) → ℂ
  denseAtom : ∀ n, Ω → Fin (M n) → Fin (M n) → ℂ
  momentsA : AtomMomentAssumption21 νA id
  momentsG : AtomMomentAssumption21 νG id
  copiesA : ∀ n, IndependentAtomCopies21 μ νA id
    (fun is : Fin (M n) × BandOffset (W n) => fun sample => ringEntry n sample is.1 is.2)
  copiesG : ∀ n, IndependentAtomCopies21 μ νG id
    (fun ij : Fin (M n) × Fin (M n) => fun sample => denseAtom n sample ij.1 ij.2)
  densityG : AtomDensityAlternative21 νG id

namespace PublishedSection3Model

def matrix (D : PublishedSection3Model μ νA νG M W c₀ C₀) :
    ∀ n, Ω → Matrix (Fin (M n)) (Fin (M n)) ℂ :=
  fun n => cyclicShortRingRandomMatrix (D.weights n) (D.fit n) (D.ringEntry n)

/-- The remaining source conditions in the published Section 3 theorem.
The deterministic scale choices are explicit. BBV and BC12 are ordinary
mathematical hypotheses and are not discharged by the axiom audit. -/
structure Sources (D : PublishedSection3Model μ νA νG M W c₀ C₀) (z : ℂ) where
  comparisonConstant : ℝ
  omega : ℝ
  chi : ℝ
  kappa : ℝ
  tau : ℝ
  K : ℝ
  p : ℝ
  R : ℕ → ℝ
  omega_range : 0 < omega ∧ omega < 1 / 9
  parameters : HardEdgeAdmissible (v3BandwidthExponent omega) chi kappa tau
  dimension_tendsto : Tendsto M atTop atTop
  bandwidth_tendsto : Tendsto W atTop atTop
  bandwidth_lower : ∀ n, (M n : ℝ) ^ v3BandwidthExponent omega ≤ (W n : ℝ)
  cutoff_constant : C₀ ^ (1 / 8 : ℝ) ≤ K
  radius_tendsto : Tendsto R atTop atTop
  radius_lower : ∀ r, Real.sqrt (Real.exp 1) < R r
  bbvA : ∀ n eta, 0 < eta.im → CanonicalBBVAt
    (cyclicV3Model (D.weights n) (D.fit n) (D.ringEntry n) id D.momentsA (D.copiesA n)) z
    eta (D.weights n).bandwidthParameter
    (max comparisonConstant (sourceV3MomentBudget νA νG id id))
  bbvG : ∀ n u, CanonicalBBVAt
    (denseV3Model (D.dimension_pos n) (D.denseAtom n) id D.momentsG (D.copiesG n)) z
    (spectralParameter u (localBulkHeight (v3BandwidthExponent omega / 2) (M n)))
    (M n) (max comparisonConstant (sourceV3MomentBudget νA νG id id))
  negative_exponent_pos : 0 < p
  bc12_negative : BC12GinibreNegativeMomentTightness μ p
    (shiftedSingularValueProcess (normalizedDenseMatrixProcess D.denseAtom) z)
  bc12_full : ConvergesInProbability μ
    (fun n sample => normalizedShiftLogDet (normalizedDenseMatrixProcess D.denseAtom n sample) z)
    (circularLogPotential z)

theorem Sources.planar_conclusion
    (D : PublishedSection3Model μ νA νG M W c₀ C₀) (z : ℂ) (h : D.Sources z)
    (hDensity : HasBoundedDensityWithRespectTo (Measure.map id νA) (volume : Measure ℂ)) :
    Proposition36SequenceConclusion μ M D.matrix z := by
  exact proposition36_cyclicShortRing_planar_from_published_theorem31
    D.weights D.fit D.ringEntry D.denseAtom id id D.momentsA D.momentsG
    D.copiesA D.copiesG hDensity D.densityG z h.comparisonConstant h.omega h.chi
    h.kappa h.tau h.K h.p h.R h.omega_range h.parameters D.dimension_pos
    h.dimension_tendsto h.bandwidth_tendsto h.bandwidth_lower h.cutoff_constant
    h.radius_tendsto h.radius_lower h.bbvA h.bbvG h.negative_exponent_pos
    h.bc12_negative h.bc12_full

theorem Sources.density_conclusion
    (D : PublishedSection3Model μ νA νG M W c₀ C₀) (z : ℂ) (h : D.Sources z)
    (hDensity : AtomDensityAlternative21 νA id)
    (hGBL : LivshytsProjectionFormalization.RealFiniteGeometricBrascampLieb) :
    Proposition36SequenceConclusion μ M D.matrix z := by
  exact proposition36_cyclicShortRing_from_published_theorem31
    D.weights D.fit D.ringEntry D.denseAtom id id D.momentsA D.momentsG
    D.copiesA D.copiesG hDensity hGBL D.densityG z h.comparisonConstant h.omega h.chi
    h.kappa h.tau h.K h.p h.R h.omega_range h.parameters D.dimension_pos
    h.dimension_tendsto h.bandwidth_tendsto h.bandwidth_lower h.cutoff_constant
    h.radius_tendsto h.radius_lower h.bbvA h.bbvG h.negative_exponent_pos
    h.bc12_negative h.bc12_full

theorem Sources.planar_tri
    (D : PublishedSection3Model μ νA νG M W c₀ C₀) (z : ℂ) (h : D.Sources z)
    (hDensity : HasBoundedDensityWithRespectTo (Measure.map id νA) (volume : Measure ℂ)) :
    TendstoInProbabilityTri (fun _ => μ)
      (fun n sample => normalizedShiftLogDet (D.matrix n sample) z) (circularLogPotential z) :=
  (Section6.tendstoInMeasure_iff_tri μ _ _).1 (Sources.planar_conclusion D z h hDensity)

theorem Sources.density_tri
    (D : PublishedSection3Model μ νA νG M W c₀ C₀) (z : ℂ) (h : D.Sources z)
    (hDensity : AtomDensityAlternative21 νA id)
    (hGBL : LivshytsProjectionFormalization.RealFiniteGeometricBrascampLieb) :
    TendstoInProbabilityTri (fun _ => μ)
      (fun n sample => normalizedShiftLogDet (D.matrix n sample) z) (circularLogPotential z) :=
  (Section6.tendstoInMeasure_iff_tri μ _ _).1 (Sources.density_conclusion D z h hDensity hGBL)

end PublishedSection3Model
end CircularLawSections56.Section5
