import ShortRingAnchor.CyclicHighBandProfile

/-! # Assumption 2.1: a pointwise bounded measurable density representative -/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace ShortRingAnchor

/-- Theorem 3.1 real model adapter: an essential density bound admits a
measurable, everywhere bounded representative with exactly the same law. -/
theorem HasBoundedDensityWithRespectTo.exists_measurable_bounded_density
    {E : Type*} [MeasurableSpace E] {mu lambda : Measure E}
    (h : HasBoundedDensityWithRespectTo mu lambda) :
    ∃ L : ℝ, 0 < L ∧ ∃ f : E → ℝ≥0∞,
      Measurable f ∧ (∀ x, f x ≤ ENNReal.ofReal L) ∧ lambda.withDensity f = mu := by
  let L := h.bound.toReal + 1
  let f := fun x => min (h.densityAEMeasurable.mk h.density x) (ENNReal.ofReal L)
  have hL : 0 < L := by dsimp [L]; positivity
  have hb : h.bound ≤ ENNReal.ofReal L := by
    calc
      h.bound = ENNReal.ofReal h.bound.toReal := (ENNReal.ofReal_toReal h.bound_lt_top.ne).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by dsimp [L]; linarith)
  have heq : f =ᵐ[lambda] h.density := by
    filter_upwards [h.densityAEMeasurable.ae_eq_mk, h.density_le_bound] with x hx hxbound
    dsimp [f]
    rw [← hx, min_eq_left (hxbound.trans hb)]
  refine ⟨L, hL, f, h.densityAEMeasurable.measurable_mk.min measurable_const,
    fun x => min_le_right _ _, ?_⟩
  exact (withDensity_congr_ae heq).trans h.law_eq_withDensity.symm

end ShortRingAnchor
