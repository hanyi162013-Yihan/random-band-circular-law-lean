import ShortRingAnchor.IndependentAtomCopies

/-!
# The normalized dense comparison ensemble as a v3 model

This is a law-agnostic construction: standard complex Gaussian atoms give
Ginibre, but the normalization and independence arguments require only the
stated atom moments and independent copies.
-/

noncomputable section
namespace ShortRingAnchor
open MeasureTheory ProbabilityTheory Arxiv2410V3
open scoped BigOperators

/-- Manuscript dense normalization: the squared entry coefficient is `1 / M`. -/
theorem denseVarianceCoefficient_sq (M : ℕ) :
    (1 / Real.sqrt (M : ℝ)) ^ 2 = 1 / (M : ℝ) := by
  rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg M)]

/-- v3 Definition 1.2: the dense doubly stochastic variance profile. -/
def denseVarianceProfile {M : ℕ} (hM : 0 < M) : DoublyStochasticVarianceProfile (Fin M) where
  coefficient _ _ := 1 / Real.sqrt (M : ℝ)
  coefficient_nonneg _ _ := by positivity
  row_sq_sum _ := by
    simp only [denseVarianceCoefficient_sq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel (by exact_mod_cast ne_of_gt hM)
  col_sq_sum _ := by
    simp only [denseVarianceCoefficient_sq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    exact mul_one_div_cancel (by exact_mod_cast ne_of_gt hM)

/-- v3 bandwidth definition: the normalized dense ensemble has exact bandwidth `M`. -/
theorem denseVarianceProfile_isBandwidth {M : ℕ} (hM : 0 < M) :
    IsBandwidth (denseVarianceProfile hM) (M : ℝ) := by
  have heq : ∀ i j, (denseVarianceProfile hM).coefficient i j ^ 2 = (M : ℝ)⁻¹ := by
    intro i j
    simpa only [denseVarianceProfile, one_div] using denseVarianceCoefficient_sq M
  refine ⟨by exact_mod_cast hM, fun i j => (heq i j).le, ?_⟩
  exact ⟨⟨0, hM⟩, ⟨0, hM⟩, heq _ _⟩

/-- Construct the v3 model of `entry / sqrt M` from the actual dense atom array.
This verifies the complete v3 model hypotheses, not just row second moments. -/
def denseV3Model
    {Omega OmegaXi : Type*} [MeasurableSpace Omega] [MeasurableSpace OmegaXi]
    {mu : Measure Omega} {nu : Measure OmegaXi}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {M : ℕ} (hM : 0 < M) (entry : Omega → Fin M → Fin M → ℂ)
    (atom : OmegaXi → ℂ) (hatom : AtomMomentAssumption21 nu atom)
    (hcopies : IndependentAtomCopies21 mu nu atom
      (fun ij : Fin M × Fin M => fun sample => entry sample ij.1 ij.2)) :
    RandomMatrixModelV3 M Omega OmegaXi mu nu where
  matrix sample i j := entry sample i j / (Real.sqrt (M : ℝ) : ℂ)
  atom := atom
  profile := denseVarianceProfile hM
  entry_measurable i j := (hcopies.measurable (i, j)).div_const _
  entries_independent := hcopies.independent.comp (fun _ x => x / (Real.sqrt (M : ℝ) : ℂ))
    (fun _ => measurable_id.div_const _)
  entry_law i j := by
    simpa only [denseVarianceProfile, div_eq_mul_inv, one_mul,
      Complex.ofReal_inv, mul_comm] using
      (hcopies.law (i, j)).div_const (Real.sqrt (M : ℝ) : ℂ)
  atom_integrable := hatom.integrable
  atom_mean_zero := hatom.centered
  atom_variance_one := hatom.unitSecondMoment
  atom_third_moment_finite := hatom.thirdMomentIntegrable

end ShortRingAnchor
