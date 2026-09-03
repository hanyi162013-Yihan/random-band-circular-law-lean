import CircularLawSection6.ProfileQuadrature
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Profile-mass limits from the proved quadrature estimate

Only geometric window/radius hypotheses are required here. Convergence of
the sampled sums is derived, not assumed. The sparse-regime geometry is
kept separate from these analytic estimates.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace CircularLawSection6

theorem intervalIntegral_tendsto_of_endpoints {f : ℝ → ℝ} (hf : Integrable f)
    {a b : ℕ → ℝ} {a₀ b₀ : ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀)) :
    Tendsto (fun n => ∫ x in a n..b n, f x) atTop (𝓝 (∫ x in a₀..b₀, f x)) := by
  have hc := hf.continuous_primitive 0
  have heq (c d : ℝ) : (∫ x in 0..d, f x) - (∫ x in 0..c, f x) =
      ∫ x in c..d, f x :=
    intervalIntegral.integral_interval_sub_left hf.intervalIntegrable hf.intervalIntegrable
  simpa only [Function.comp_apply, heq] using
    ((hc.tendsto b₀).comp hb).sub ((hc.tendsto a₀).comp ha)

namespace NoncompactProfile

theorem quadratureError_tendsto_zero (p : NoncompactProfile)
    {W : ℕ → ℝ} (hW : Tendsto W atTop atTop) :
    Tendsto (fun n => (eVariationOn p.f Set.univ).toReal / W n) atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hW) :
      Tendsto (fun n => (eVariationOn p.f Set.univ).toReal * (W n)⁻¹) atTop
        (𝓝 ((eVariationOn p.f Set.univ).toReal * 0)))

theorem normalizer_tendsto_of_window_exhaustion (p : NoncompactProfile)
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ)
    (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hleft : Tendsto (fun n => -((N n / 2 : ℕ) : ℝ) / W n) atTop atBot)
    (hright : Tendsto (fun n => (((N n + 1) / 2 : ℕ) : ℝ) / W n) atTop atTop) :
    Tendsto (fun n => p.normalizer (N n) (W n) / W n) atTop (𝓝 1) := by
  have herr : Tendsto (fun n => p.normalizer (N n) (W n) / W n -
      ∫ x in -((N n / 2 : ℕ) : ℝ) / W n..(((N n + 1) / 2 : ℕ) : ℝ) / W n, p.f x)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm _ (p.quadratureError_tendsto_zero hWlim)
    intro n
    simpa only [Real.norm_eq_abs] using p.normalizer_quadrature_error (N n) (hW n)
  have hint := intervalIntegral_tendsto_integral p.integrable hleft hright
  simpa only [sub_add_cancel, zero_add, p.integral_one] using herr.add hint

theorem rawCoreMass_tendsto_of_scaled_radius (p : NoncompactProfile)
    (N H : ℕ → ℕ) [∀ n, NeZero (N n)] (W : ℕ → ℝ)
    (hW : ∀ n, 0 < W n) (hWlim : Tendsto W atTop atTop)
    (hsize : ∀ᶠ n in atTop, 2 * H n + 1 ≤ N n)
    {R : ℝ} (hR : Tendsto (fun n => (H n : ℝ) / W n) atTop (𝓝 R)) :
    Tendsto (fun n => p.rawCoreMass (N n) (H n) (W n) / W n) atTop
      (𝓝 (∫ x in -R..R, p.f x)) := by
  have ha : Tendsto (fun n => -(H n : ℝ) / W n) atTop (𝓝 (-R)) := by
    simpa only [neg_div] using hR.neg
  have hb : Tendsto (fun n => ((H n : ℝ) + 1) / W n) atTop (𝓝 R) := by
    simpa only [Function.comp_apply, add_div, one_div, add_zero] using
      hR.add (tendsto_inv_atTop_zero.comp hWlim)
  have hint := intervalIntegral_tendsto_of_endpoints p.integrable ha hb
  have herr : Tendsto (fun n => p.rawCoreMass (N n) (H n) (W n) / W n -
      ∫ x in -(H n : ℝ) / W n..((H n : ℝ) + 1) / W n, p.f x) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (p.quadratureError_tendsto_zero hWlim)
    filter_upwards [hsize] with n hn
    simpa only [Real.norm_eq_abs] using p.rawCoreMass_quadrature_error (N n) (H n) hn (hW n)
  simpa only [sub_add_cancel, zero_add] using herr.add hint

/-- The actual floor cutoff has the required scaled-radius limit. -/
theorem floor_radius_tendsto {W : ℕ → ℝ} (hW : Tendsto W atTop atTop)
    {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n => (⌊R * W n⌋₊ : ℝ) / W n) atTop (𝓝 R) :=
  (tendsto_nat_floor_mul_div_atTop hR).comp hW

end NoncompactProfile
end CircularLawSection6
