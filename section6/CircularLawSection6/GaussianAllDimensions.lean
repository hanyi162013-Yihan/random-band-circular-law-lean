import CircularLawSection6.GaussianCyclicConcentration

/-! # Concentration without a dimension-prefix restriction

The one-dimensional case uses the already proved affine-row estimate.
Increasing the uniform constant once incorporates it without changing any
asymptotic rate or requiring a finite-prefix filler.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open CircularLawSections56.Section5

noncomputable section

namespace CircularLawSection6

def gaussianCyclicVarianceConstantAll (c r : ℝ) (z : ℂ) : ℝ :=
  gaussianCyclicVarianceConstant c r z +
    2 * affineRowLogBound 0 (Real.sqrt (scaledDiagonalConstant c r)) 2 z

theorem gaussianCyclicVarianceConstant_nonneg (c r : ℝ) (z : ℂ) :
    0 ≤ gaussianCyclicVarianceConstant c r z := by
  unfold gaussianCyclicVarianceConstant uniformFiberSquareConstant
  positivity

theorem gaussianCyclicVarianceConstant_le_all (c r : ℝ) (z : ℂ) :
    gaussianCyclicVarianceConstant c r z ≤ gaussianCyclicVarianceConstantAll c r z :=
  le_add_of_nonneg_right (mul_nonneg (by norm_num) (affineRowLogBound_nonneg _ _ _ _))

theorem gaussian_cyclic_memLp_and_variance_all (N : ℕ) [NeZero N]
    (q : ZMod N → ℝ) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (z : ℂ)
    (hq : c / (N : ℝ) ≤ q 0) :
    MemLp (cyclicRawLogDet N q r z) 2 (cyclicAtomLaw N circularComplexGaussian) ∧
      variance (cyclicRawLogDet N q r z) (cyclicAtomLaw N circularComplexGaussian) ≤
        gaussianCyclicVarianceConstantAll c r z * (N : ℝ) *
          (Real.log (Real.exp 1 * (N : ℝ))) ^ 2 := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    cases n with
    | zero =>
      have hδ : 0 < Real.sqrt (scaledDiagonalConstant c r) :=
        Real.sqrt_pos.2 (scaledDiagonalConstant_pos hc hr)
      have hδ1 : Real.sqrt (scaledDiagonalConstant c r) ≤ 1 :=
        Real.sqrt_le_one.2 (scaledDiagonalConstant_le_one c r)
      have hb : Real.sqrt (scaledDiagonalConstant c r) ≤ r * Real.sqrt (q 0) := by
        simpa only [Nat.cast_one, div_one] using sqrt_scaledDiagonalConstant_le
          (N := 1) zero_lt_one hr (by simpa using hq)
      have h := cyclicRawLogDet_memLp_and_variance 0 circularComplexGaussian
        circularComplexGaussian_ballBound (by norm_num) q hr.le z hδ hδ1 hb
        circularComplexGaussian_sq_integrable circularComplexGaussian_secondMoment.le
      refine ⟨h.1, ?_⟩
      simp only [Nat.cast_one, zero_add,
        mul_one, Real.log_exp, one_pow]
      have hv : variance (cyclicRawLogDet 1 q r z) (cyclicAtomLaw 1 circularComplexGaussian) ≤
          2 * affineRowLogBound 0 (Real.sqrt (scaledDiagonalConstant c r)) 2 z := by
        simpa only [Nat.cast_zero, zero_add, mul_one] using h.2
      exact hv.trans (le_add_of_nonneg_left (gaussianCyclicVarianceConstant_nonneg c r z))
    | succ d =>
      have h := gaussian_cyclic_memLp_and_variance d q hc hr z
        (by simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using hq)
      refine ⟨h.1, ?_⟩
      have hv : variance (cyclicRawLogDet (d + 2) q r z) (cyclicAtomLaw (d + 2) circularComplexGaussian) ≤
          gaussianCyclicVarianceConstant c r z * ((d + 2 : ℕ) : ℝ) *
            (Real.log (Real.exp 1 * ((d + 2 : ℕ) : ℝ))) ^ 2 := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using h.2
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using
        hv.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (gaussianCyclicVarianceConstant_le_all c r z)
          (Nat.cast_nonneg (d + 2))) (sq_nonneg _))

theorem gaussian_cyclic_concentration_all (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (q : ∀ n, ZMod (N n) → ℝ)
    {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (z : ℂ)
    (hq : ∀ n, c / (N n : ℝ) ≤ q n 0) :
    Tendsto (fun n => ∫ ω,
      |cyclicRawLogDet (N n) (q n) r z ω / (N n : ℝ) -
        ∫ x, cyclicRawLogDet (N n) (q n) r z x / (N n : ℝ)
          ∂cyclicAtomLaw (N n) circularComplexGaussian|
      ∂cyclicAtomLaw (N n) circularComplexGaussian) atTop (𝓝 0) ∧
    TendstoInProbabilityTri (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
      (fun n ω => cyclicRawLogDet (N n) (q n) r z ω / (N n : ℝ) -
        ∫ x, cyclicRawLogDet (N n) (q n) r z x / (N n : ℝ)
          ∂cyclicAtomLaw (N n) circularComplexGaussian) 0 :=
  concentration_of_logarithmic_variance
    (fun n => cyclicAtomLaw (N n) circularComplexGaussian)
    (fun n => cyclicRawLogDet (N n) (q n) r z) N (fun n => NeZero.pos (N n)) hN
    (gaussianCyclicVarianceConstantAll c r z)
    (fun n => (gaussian_cyclic_memLp_and_variance_all (N n) (q n) hc hr z (hq n)).1)
    (fun n => (gaussian_cyclic_memLp_and_variance_all (N n) (q n) hc hr z (hq n)).2)

end CircularLawSection6
