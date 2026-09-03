import CircularLawSection6.GinibreGaussianLaw
import ShortRingAnchor.HighProbabilityTransfer
import ShortRingAnchor.LeastSingularValueAdapter
import Mathlib.Topology.Instances.Matrix

/-! # Ginibre nonsingularity at every fixed complex shift

The proved Gaussian small-ball estimate tends to zero as its threshold
tends to zero at fixed dimension. This is a pointwise-in-shift result,
not merely a planar-almost-everywhere parameter statement. It uses no
BBV, BC12 logarithmic limit, or other literature hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology ShortRingAnchor
open CircularLawSections56.Section5.PublishedSection3Concrete
  (gaussianSequenceLaw ginibreOnSequence)
open CircularLawSection6.GinibreReferenceSources
open scoped ENNReal
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem leastSingularValue_lt_of_shifted_det_eq_zero
    {N : ℕ} (hN : 0 < N) (A : Matrix (Fin N) (Fin N) ℂ) (z : ℂ)
    (hdet : (A - z • 1).det = 0) {ε : ℝ} (hε : 0 < ε) :
    GinibreLSV.leastSingularValue (A - z • 1) < ε := by
  let : NeZero N := ⟨hN.ne'⟩
  by_contra hnot
  have hleast : ε ≤ shiftedSingularValueFamily A z (lastSingularValueIndex N hN) :=
    le_of_not_gt hnot
  exact (shifted_det_ne_zero_of_singularValue_lower A z ε hε
    (fun i => hleast.trans (shiftedSingularValueFamily_last_le hN A z i))) hdet

theorem ginibreOnSequence_shifted_det_ne_zero (N : ℕ) (hN : 0 < N) (z : ℂ) :
    ∀ᵐ ω ∂gaussianSequenceLaw, (ginibreOnSequence N ω - z • 1).det ≠ 0 := by
  let bad := {ω | (ginibreOnSequence N ω - z • 1).det = 0}
  have hbound (k : ℕ) : gaussianSequenceLaw bad ≤
      ENNReal.ofReal (4 * (N : ℝ) ^ 3 * (1 / (k + 1 : ℕ))) := by
    refine (measure_mono (show bad ⊆ {ω |
      GinibreLSV.leastSingularValue (ginibreOnSequence N ω - z • 1) < 1 / (k + 1 : ℕ)} from ?_)).trans
      (BC12.normalizedGinibre_smallBall_of_hasLaw hN (ginibreOnSequence_hasLaw N) z (by positivity))
    intro ω hω
    exact leastSingularValue_lt_of_shifted_det_eq_zero hN (ginibreOnSequence N ω) z hω (by positivity)
  have hr : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1 : ℕ)) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).const_div_atTop 1
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal
      (4 * (N : ℝ) ^ 3 * (1 / (k + 1 : ℕ)))) atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (hr.const_mul (4 * (N : ℝ) ^ 3))
  have hzero : gaussianSequenceLaw bad = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound)) zero_le
  simpa only [ae_iff, not_not] using hzero

/-- Every fixed shifted finite cyclic Ginibre matrix is nonsingular almost
surely, with the actual cyclic law and its exact normalization. -/
theorem ginibre_shifted_det_ne_zero (N : ℕ) [NeZero N] (z : ℂ) :
    ∀ᵐ ω ∂cyclicAtomLaw N circularComplexGaussian,
      (ginibreMatrix N ω - z • 1).det ≠ 0 := by
  classical
  have hmeas : Measurable (fun ω => (ginibreMatrix N ω - z • 1).det) := by
    have hA : Measurable (fun ω => ginibreMatrix N ω - z • 1) :=
      (ginibreMatrix_measurable N).sub measurable_const
    exact continuous_id.matrix_det.measurable.comp hA
  have heq (ω : ℕ → ℂ) : (ginibreOnSequence N ω - z • 1).det =
      (ginibreMatrix N (cyclicSamples N ω) - z • 1).det :=
    (congrArg Matrix.det (cyclicSamples_shifted_matrix N ω z).symm).trans
      (Matrix.det_submatrix_equiv_self (ZMod.finEquiv N).toEquiv
        (ginibreMatrix N (cyclicSamples N ω) - z • 1))
  have hseq := ginibreOnSequence_shifted_det_ne_zero N (NeZero.pos N) z
  rw [ae_iff] at hseq ⊢
  simp only [not_not] at hseq ⊢
  rw [← (cyclicSamples_measurePreserving N).measure_preimage
    (measurableSet_eq_fun hmeas measurable_const).nullMeasurableSet]
  simpa only [Set.preimage_ofPred_eq, ← heq] using hseq

end CircularLawSection6
