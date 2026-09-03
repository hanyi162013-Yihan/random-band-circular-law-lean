import BernoulliSection10Complex.ConcretePressure
import BernoulliSection10Complex.HodgeFamilyGrowth

/-! # The whole-interval concentration scale in (10.33) and (10.42) -/

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

theorem log_three_width_bounds (W : ℕ) (hW : 0 < W) :
    0 ≤ Real.log (Real.exp 1 * ((3 * W : ℕ) : ℝ)) ∧
      Real.log (Real.exp 1 * ((3 * W : ℕ) : ℝ)) ≤
        (1 + Real.posLog 3) * densityLogScale W := by
  have hscale : (1 : ℝ) ≤ densityLogScale W := by
    rw [densityLogScale, ← one_add_posLog_nat_eq_log_e_mul W hW]
    exact le_add_of_nonneg_right Real.posLog_nonneg
  have hfactor : Real.log (Real.exp 1 * ((3 * W : ℕ) : ℝ)) =
      Real.posLog 3 + densityLogScale W := by
    rw [show Real.exp 1 * ((3 * W : ℕ) : ℝ) =
      3 * (Real.exp 1 * (W : ℝ)) by push_cast; ring]
    rw [Real.log_mul (by norm_num)
      (mul_ne_zero (Real.exp_ne_zero 1) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hW)))]
    congr 1
    exact (Real.posLog_eq_log (by norm_num : 1 ≤ |(3 : ℝ)|)).symm
  rw [hfactor]
  constructor
  · linarith [Real.posLog_nonneg (x := (3 : ℝ))]
  · have h := mul_le_mul_of_nonneg_left hscale (Real.posLog_nonneg (x := (3 : ℝ)))
    nlinarith only [h]

theorem sqrt_physicalRowResamplingEnergy_le
    (L : ℝ) (W : ℕ) (hW : 0 < W) :
    Real.sqrt (physicalRowResamplingEnergy W L) ≤
      oneSiteRowLogConstant L * densityLogScale W := by
  have hconst : 0 ≤ lemma10_2Constant L := by
    unfold lemma10_2Constant affineLogConstant
    positivity
  have hlog := log_three_width_bounds W hW
  rw [physicalRowResamplingEnergy, Real.sqrt_mul hconst, Real.sqrt_sq hlog.1]
  simpa only [oneSiteRowLogConstant, mul_assoc] using
    mul_le_mul_of_nonneg_left hlog.2 (Real.sqrt_nonneg (lemma10_2Constant L))

def densityConcentrationConstant (L : ℝ) : ℝ := 2 * oneSiteRowLogConstant L

theorem densityConcentrationConstant_nonneg (L : ℝ) :
    0 ≤ densityConcentrationConstant L :=
  mul_nonneg (by norm_num) (oneSiteRowLogConstant_nonneg L)

theorem intervalPressureConcentrationCost_le
    (L : ℝ) (W s : ℕ) (hW : 0 < W) :
    intervalPressureConcentrationCost L W s ≤
      densityConcentrationConstant L * Real.sqrt ((W : ℝ) * ((s * W : ℕ) : ℝ)) *
        densityLogScale W := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hdim : (((2 * W + 1 : ℕ) : ℝ) * (1 / 2 : ℝ)) ≤ 4 * W := by
    push_cast
    linarith only [hW1]
  have he := physicalRowResamplingEnergy_nonneg W L
  have hrow : 0 ≤ ((s * W : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsize : 0 ≤ (W : ℝ) * ((s * W : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) hrow
  have hcost : intervalPressureConcentrationCost L W s ≤
      2 * Real.sqrt ((W : ℝ) * ((s * W : ℕ) : ℝ)) *
        Real.sqrt (physicalRowResamplingEnergy W L) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdim hrow) he
      rw [mul_pow, mul_pow, Real.sq_sqrt hsize, Real.sq_sqrt he]
      nlinarith only [h]
  calc
    _ ≤ 2 * Real.sqrt ((W : ℝ) * ((s * W : ℕ) : ℝ)) *
        Real.sqrt (physicalRowResamplingEnergy W L) := hcost
    _ ≤ 2 * Real.sqrt ((W : ℝ) * ((s * W : ℕ) : ℝ)) *
        (oneSiteRowLogConstant L * densityLogScale W) :=
      mul_le_mul_of_nonneg_left (sqrt_physicalRowResamplingEnergy_le L W hW)
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    _ = _ := by unfold densityConcentrationConstant; ring

end BernoulliSection10Complex

