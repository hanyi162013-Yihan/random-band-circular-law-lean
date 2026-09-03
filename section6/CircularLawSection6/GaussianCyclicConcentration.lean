import CircularLawSection6.CyclicRowTransport
import CircularLawSection6.GaussianDensityBounds
import CircularLawSection6.NormalizedConcentration

/-! # Literal Gaussian cyclic determinant concentration

The density constant is instantiated by the normalized circular Gaussian.
The displayed variance constant depends only on the diagonal comparison
constant, the fixed matrix scaling, and the spectral parameter.
-/

open MeasureTheory ProbabilityTheory Filter Topology CircularLawSection4
open CircularLawSections56.Section5

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

attribute [local instance] iidMeasure_isProbability

def scaledDiagonalConstant (c r : ℝ) : ℝ := min 1 (r ^ 2 * c)

theorem scaledDiagonalConstant_pos {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    0 < scaledDiagonalConstant c r := lt_min zero_lt_one (mul_pos (sq_pos_of_pos hr) hc)

theorem scaledDiagonalConstant_le_one (c r : ℝ) : scaledDiagonalConstant c r ≤ 1 :=
  min_le_left _ _

theorem sqrt_scaledDiagonalConstant_le {N c r t : ℝ}
    (hN : 0 < N) (hr : 0 < r) (ht : c / N ≤ t) :
    Real.sqrt (scaledDiagonalConstant c r / N) ≤ r * Real.sqrt t := by
  have h : scaledDiagonalConstant c r / N ≤ r ^ 2 * t := by
    calc
      _ ≤ (r ^ 2 * c) / N := div_le_div_of_nonneg_right (min_le_right _ _) hN.le
      _ = r ^ 2 * (c / N) := mul_div_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left ht (sq_nonneg r)
  have hs := Real.sqrt_le_sqrt h
  simpa only [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs, abs_of_pos hr] using hs

def gaussianCyclicVarianceConstant (c r : ℝ) (z : ℂ) : ℝ :=
  2 * uniformFiberSquareConstant (scaledDiagonalConstant c r) 2 z

/-- The manuscript's variance estimate, with its Gaussian law and uniform
constant instantiated. Dimensions at least two suffice for every limit. -/
theorem gaussian_cyclic_memLp_and_variance (d : ℕ)
    (q : ZMod (d + 2) → ℝ) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (z : ℂ)
    (hq : c / (d + 2 : ℝ) ≤ q 0) :
    MemLp (cyclicRawLogDet (d + 2) q r z) 2 (cyclicAtomLaw (d + 2) circularComplexGaussian) ∧
      variance (cyclicRawLogDet (d + 2) q r z) (cyclicAtomLaw (d + 2) circularComplexGaussian) ≤
        gaussianCyclicVarianceConstant c r z * (d + 2 : ℝ) *
          (Real.log (Real.exp 1 * (d + 2 : ℝ))) ^ 2 := by
  have hc' := scaledDiagonalConstant_pos hc hr
  have hc1 := scaledDiagonalConstant_le_one c r
  have hN : (0 : ℝ) < d + 2 := by positivity
  have hδ : 0 < Real.sqrt (scaledDiagonalConstant c r / (d + 2 : ℝ)) :=
    Real.sqrt_pos.2 (div_pos hc' hN)
  have hδ1 : Real.sqrt (scaledDiagonalConstant c r / (d + 2 : ℝ)) ≤ 1 := by
    apply Real.sqrt_le_one.2
    exact (div_le_one hN).2 (hc1.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) d]))
  have hb := sqrt_scaledDiagonalConstant_le hN hr hq
  have hmem := (cyclicRawLogDet_memLp_and_variance (d + 1) circularComplexGaussian
    circularComplexGaussian_ballBound (by norm_num) q hr.le z hδ hδ1 hb
    circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment.le).1
  refine ⟨hmem, ?_⟩
  have hv := weightedRowsLogDet_variance_le_uniform circularComplexGaussian
    circularComplexGaussian_ballBound (by norm_num) hc' hc1 d
    (cyclicRowAmplitude (d + 2) q r) z
    (fun i => by rw [cyclicRowAmplitude_diagonal _ _ hr.le]; exact hb)
    circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment.le
  have he := (cyclicColumnSample_measurePreserving (d + 2) circularComplexGaussian).variance_fun_comp
    (weightedRowsLogDet_measurable (cyclicRowAmplitude (d + 2) q r) z).aemeasurable
  simp only [weightedRowsLogDet_cyclicColumnSample] at he
  exact he.trans_le hv

/-- Normalized raw potentials concentrate for arbitrary dimension-varying
Gaussian cyclic profiles with one uniform diagonal comparison constant. -/
theorem gaussian_cyclic_concentration (d : ℕ → ℕ)
    (hd : Tendsto (fun n => d n + 2) atTop atTop)
    (q : ∀ n, ZMod (d n + 2) → ℝ) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (z : ℂ)
    (hq : ∀ n, c / (d n + 2 : ℝ) ≤ q n 0) :
    Tendsto (fun n => ∫ ω,
      |cyclicRawLogDet (d n + 2) (q n) r z ω / (d n + 2 : ℝ) -
        ∫ x, cyclicRawLogDet (d n + 2) (q n) r z x / (d n + 2 : ℝ)
          ∂cyclicAtomLaw (d n + 2) circularComplexGaussian|
      ∂cyclicAtomLaw (d n + 2) circularComplexGaussian) atTop (𝓝 0) ∧
    TendstoInProbabilityTri (fun n => cyclicAtomLaw (d n + 2) circularComplexGaussian)
      (fun n ω => cyclicRawLogDet (d n + 2) (q n) r z ω / (d n + 2 : ℝ) -
        ∫ x, cyclicRawLogDet (d n + 2) (q n) r z x / (d n + 2 : ℝ)
          ∂cyclicAtomLaw (d n + 2) circularComplexGaussian) 0 := by
  have h := concentration_of_logarithmic_variance
    (fun n => cyclicAtomLaw (d n + 2) circularComplexGaussian)
    (fun n => cyclicRawLogDet (d n + 2) (q n) r z) (fun n => d n + 2)
    (fun _ => by omega) hd (gaussianCyclicVarianceConstant c r z)
    (fun n => (gaussian_cyclic_memLp_and_variance (d n) (q n) hc hr z (hq n)).1)
    (fun n => by simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (gaussian_cyclic_memLp_and_variance (d n) (q n) hc hr z (hq n)).2)
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h

end CircularLawSection6
