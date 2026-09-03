import ShortRingAnchor.ExplicitStieltjesRate
import Vendor.Arxiv2410.V3.Proposition34Canonical
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Expected Stieltjes transforms from the published Section 3 comparison

Apply the verified finite comparison at its own expectation: its concentration
term is then exactly zero. The canonical Gaussian construction discharges all
coupling and Gaussian-law fields. BBV Theorem 2.8 remains the literature input.
-/

open MeasureTheory Filter Topology Arxiv2410V3
noncomputable section
set_option autoImplicit false

namespace CircularLawSection6

theorem published_meanStieltjes_comparison
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {N : ℕ} (hN : 2 ≤ N) (model : RandomMatrixModelV3 N Ω Ξ μ ν)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) {B C : ℝ}
    (hB : IsBandwidth model.profile B) (hC : 8 ≤ C)
    (hthird : BVH.atomThirdMoment model + BVH.complexGaussianThirdMomentConstant ≤ C)
    (hBBV : External.BBVTheorem28GaussianFreeHypothesis
      (∫ ω, stieltjesTrace (BVH.canonicalCircularizedMatrix model ω) z eta
        ∂BVH.canonicalGaussianMeasure model)
      (freeDysonStieltjes z eta) B eta.im C) :
    ‖(∫ ω, stieltjesTrace (model.matrix ω) z eta ∂μ) - freeDysonStieltjes z eta‖ ≤
      formula311Error N B eta.im C 0 := by
  let : NeZero N := ⟨by omega⟩
  exact proposition34_formula311_fixedEta_from_only_bbv
    model (BVH.canonicalGaussianCompanion model)
    (BVH.canonicalCircularizedMatrix model) (BVH.canonicalDiagonalDifference model)
    z eta (∫ ω, stieltjesTrace (model.matrix ω) z eta ∂μ)
    heta hN hB hC hthird
    (BVH.canonicalCircularizedMatrix_entry_measurable model)
    (BVH.canonicalGaussianMatrix_sub_circularized model)
    (BVH.canonicalDiagonalDifference_re_hasGaussianLaw model)
    (BVH.canonicalDiagonalDifference_im_hasGaussianLaw model)
    (BVH.canonicalDiagonalDifference_re_mean_zero model)
    (BVH.canonicalDiagonalDifference_im_mean_zero model)
    (BVH.canonicalDiagonalDifference_re_variance_le_two_div_bandwidth model hB)
    (BVH.canonicalDiagonalDifference_im_variance_le_two_div_bandwidth model hB)
    (by simp) hBBV

theorem dense_fixedHeight_scale_eventually (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n in atTop, (N n : ℝ) ^ (1 / 2 : ℝ) ≤ (N n : ℝ) * t ^ 8 := by
  have hlim : Tendsto (fun n => Real.sqrt (N n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  filter_upwards [hlim.eventually (eventually_ge_atTop (1 / t ^ 8))] with n hn
  have ht8 : 0 < t ^ 8 := pow_pos ht _
  have hmul : 1 ≤ Real.sqrt (N n : ℝ) * t ^ 8 := (div_le_iff₀ ht8).mp hn
  have hh := mul_le_mul_of_nonneg_left hmul (Real.sqrt_nonneg (N n : ℝ))
  rw [← Real.sqrt_eq_rpow]
  simpa only [mul_one, ← mul_assoc, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg (N n))] using hh

theorem published_dense_meanStieltjes_tendsto
    {Ω : ℕ → Type*} {Ξ : Type*} [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ξ]
    (μ : ∀ n, Measure (Ω n)) (ν : Measure Ξ)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (model : ∀ n, RandomMatrixModelV3 (N n) (Ω n) Ξ (μ n) ν)
    (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) {C : ℝ} (hC : 8 ≤ C)
    (hB : ∀ n, IsBandwidth (model n).profile (N n : ℝ))
    (hthird : ∀ n, BVH.atomThirdMoment (model n) + BVH.complexGaussianThirdMomentConstant ≤ C)
    (hBBV : ∀ n, External.BBVTheorem28GaussianFreeHypothesis
      (∫ ω, stieltjesTrace (BVH.canonicalCircularizedMatrix (model n) ω) z eta
        ∂BVH.canonicalGaussianMeasure (model n))
      (freeDysonStieltjes z eta) (N n : ℝ) eta.im C) :
    Tendsto (fun n => ∫ ω, stieltjesTrace ((model n).matrix ω) z eta ∂μ n)
      atTop (𝓝 (freeDysonStieltjes z eta)) := by
  have hrates := hN.eventually
    (ShortRingAnchor.eventually_formula311Error_le_explicit_nat_allEta
      (show 0 ≤ C by linarith) (le_refl (0 : ℝ))
      (show (0 : ℝ) < 1 / 2 by norm_num))
  have hlim : Tendsto (fun n => (N n : ℝ) ^ (-((1 / 2 : ℝ) / 32))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp
      (tendsto_natCast_atTop_atTop.comp hN)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hN.eventually (eventually_ge_atTop 2), hrates,
    dense_fixedHeight_scale_eventually N hN heta] with n hn hr hs
  have hnR : (1 : ℝ) ≤ N n := by exact_mod_cast (show 1 ≤ N n by omega)
  exact (published_meanStieltjes_comparison hn (model n) z heta (hB n) hC (hthird n)
    (hBBV n)).trans (hr (N n) eta.im hnR le_rfl heta hs)

end CircularLawSection6
