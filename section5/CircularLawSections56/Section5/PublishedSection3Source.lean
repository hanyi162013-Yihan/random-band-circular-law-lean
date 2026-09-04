import ShortRingAnchor.Proposition36Planar
import ShortRingAnchor.Proposition36PublishedTheorem31
import ShortRingAnchor.BC12.GinibreNegativeMoments
import ShortRingAnchor.BC12.GaussianMatrixLawBridge
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

namespace CircularLawSections56.Section5

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} {νA νG : Measure ℂ}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure νA] [IsProbabilityMeasure νG]
variable {M W : ℕ → ℕ} {c₀ C₀ : ℝ}

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

/-- The source data for the published Section 3 theorem. Only BBV estimates
are external mathematical inputs. The dense reference has its actual
Gaussian law, from which both former BC12 estimates are proved below. -/
structure Sources (D : PublishedSection3Model μ νA νG M W c₀ C₀) (z : ℂ) where
  comparisonConstant : ℝ
  omega : ℝ
  chi : ℝ
  kappa : ℝ
  tau : ℝ
  K : ℝ
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
  bbvG : ∀ n eta, 0 < eta.im → CanonicalBBVAt
    (denseV3Model (D.dimension_pos n) (D.denseAtom n) id D.momentsG (D.copiesG n)) z
    eta
    (M n) (max comparisonConstant (sourceV3MomentBudget νA νG id id))
  ginibreLaw : ∀ n, HasLaw (normalizedDenseMatrixProcess D.denseAtom n)
    (BC12.normalizedGinibreLaw (M n)) μ

/-- Proposition 3.6 / manuscript (3.14): the Gaussian negative moment
is derived from the actual law and the displayed dense BBV comparison. -/
theorem Sources.ginibre_negative_moment
    (D : PublishedSection3Model μ νA νG M W c₀ C₀) (z : ℂ) (h : D.Sources z) :
    BC12GinibreNegativeMomentTightness μ (1 / 128)
      (shiftedSingularValueProcess (normalizedDenseMatrixProcess D.denseAtom) z) := by
  have hC : 8 ≤ max h.comparisonConstant (sourceV3MomentBudget νA νG id id) :=
    (sourceV3MomentBudget_ge_eight id id).trans (le_max_right _ _)
  have hthird : (∫ x, ‖id x‖ ^ 3 ∂νG) + BVH.complexGaussianThirdMomentConstant ≤
      max h.comparisonConstant (sourceV3MomentBudget νA νG id id) :=
    (sourceV3MomentBudget_ge_right id id).trans (le_max_right _ _)
  exact BC12.negativeMomentTightness_normalizedDenseMatrixProcess
    D.dimension_pos h.dimension_tendsto D.denseAtom id D.momentsG D.copiesG h.ginibreLaw
    z hC hthird
    (fun n v hv => h.bbvG n (spectralParameter 0 v) (by simpa [spectralParameter] using hv))

/-- Proposition 3.6 reference step: exact Ginibre correlations prove the
full-log limit. This is a proved consequence, not a source record field. -/
theorem Sources.ginibre_logPotential
    (D : PublishedSection3Model μ νA νG M W c₀ C₀) (z : ℂ) (h : D.Sources z) :
    ConvergesInProbability μ
    (fun n sample => normalizedShiftLogDet (normalizedDenseMatrixProcess D.denseAtom n sample) z)
    (circularLogPotential z) :=
  BC12.ginibre_logdet_convergesInProbability_of_ginibreLaw D.dimension_pos h.dimension_tendsto
    (normalizedDenseMatrixProcess D.denseAtom) h.ginibreLaw z

/-- Lemma 3.5 local smoothing height: specialize the same dense comparison
used for the negative-moment bound, without introducing a second input. -/
theorem Sources.ginibre_local_comparison
    (D : PublishedSection3Model μ νA νG M W c₀ C₀) (z : ℂ) (h : D.Sources z) :
    ∀ n u, CanonicalBBVAt
      (denseV3Model (D.dimension_pos n) (D.denseAtom n) id D.momentsG (D.copiesG n)) z
      (spectralParameter u (localBulkHeight (v3BandwidthExponent h.omega / 2) (M n)))
      (M n) (max h.comparisonConstant (sourceV3MomentBudget νA νG id id)) := by
  intro n u
  apply h.bbvG n
  simpa [spectralParameter, localBulkHeight] using
    Real.rpow_pos_of_pos (by exact_mod_cast D.dimension_pos n : (0 : ℝ) < M n)
      (-(localBulkEffectiveExponent (v3BandwidthExponent h.omega / 2) / 16))

variable [∀ n, Nonempty (Fin (M n))]

theorem Sources.planar_conclusion
    (D : PublishedSection3Model μ νA νG M W c₀ C₀) (z : ℂ) (h : D.Sources z)
    (hDensity : HasBoundedDensityWithRespectTo (Measure.map id νA) (volume : Measure ℂ)) :
    Proposition36SequenceConclusion μ M D.matrix z := by
  exact proposition36_cyclicShortRing_planar_from_published_theorem31
    D.weights D.fit D.ringEntry D.denseAtom id id D.momentsA D.momentsG
    D.copiesA D.copiesG hDensity D.densityG z h.comparisonConstant h.omega h.chi
    h.kappa h.tau h.K (1 / 128) h.R h.omega_range h.parameters D.dimension_pos
    h.dimension_tendsto h.bandwidth_tendsto h.bandwidth_lower h.cutoff_constant
    h.radius_tendsto h.radius_lower h.bbvA (h.ginibre_local_comparison D z) (by norm_num)
    (h.ginibre_negative_moment D z) (h.ginibre_logPotential D z)

theorem Sources.density_conclusion
    (D : PublishedSection3Model μ νA νG M W c₀ C₀) (z : ℂ) (h : D.Sources z)
    (hDensity : AtomDensityAlternative21 νA id)
    (hGBL : LivshytsProjectionFormalization.RealFiniteGeometricBrascampLieb) :
    Proposition36SequenceConclusion μ M D.matrix z := by
  exact proposition36_cyclicShortRing_from_published_theorem31
    D.weights D.fit D.ringEntry D.denseAtom id id D.momentsA D.momentsG
    D.copiesA D.copiesG hDensity hGBL D.densityG z h.comparisonConstant h.omega h.chi
    h.kappa h.tau h.K (1 / 128) h.R h.omega_range h.parameters D.dimension_pos
    h.dimension_tendsto h.bandwidth_tendsto h.bandwidth_lower h.cutoff_constant
    h.radius_tendsto h.radius_lower h.bbvA (h.ginibre_local_comparison D z) (by norm_num)
    (h.ginibre_negative_moment D z) (h.ginibre_logPotential D z)

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
