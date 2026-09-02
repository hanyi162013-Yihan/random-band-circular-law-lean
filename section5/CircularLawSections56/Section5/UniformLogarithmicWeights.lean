import CircularLawSections56.Section5.LiteralAtomRowCost
import CircularLawSections56.Section5.LiteralRealCellPackage

/-! # Uniform constants for dimension-dependent polynomial lower weights

The hypothesis bounds `|log c₀|` by a fixed multiple of the logarithmic
dimension.  Unlike substituting a dimension-dependent value into the older
constant, the estimates below do not introduce a spurious squared logarithm.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 800000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

theorem paperProjectiveCoefficientLogLoss_le_logarithmic
    (d : ℕ) (c₀ A : ℝ) (hc₀ : 0 < c₀) (hA : 0 ≤ A)
    (hc : |Real.log c₀| ≤ A * dimensionLogScale d) (q : ExteriorDegree (d + 1)) :
    paperProjectiveCoefficientLogLoss d c₀ q ≤
      (A + 4) * (d + 1 : ℝ) * dimensionLogScale d := by
  have hD : (0 : ℝ) ≤ d + 1 := by positivity
  have hH := one_le_dimensionLogScale d
  have ht : Real.log (d + 2 : ℝ) ≤ dimensionLogScale d := by
    unfold dimensionLogScale
    linarith
  have hw := negative_log_profile_sqrt_le d c₀ hc₀
  have hw' : -Real.log (Real.sqrt (c₀ / (d + 2 : ℝ))) ≤
      (A + 1) * dimensionLogScale d / 2 := by linarith
  have hweight := mul_le_mul_of_nonneg_left hw' hD
  have hcard := log_card_exteriorIndex_le (d + 1) q
  push_cast at hcard
  rw [paperProjectiveCoefficientLogLoss, max_le_iff]
  constructor
  · positivity
  · push_cast
    nlinarith [mul_nonneg hD (sub_nonneg.mpr hH),
      mul_nonneg (mul_nonneg hA hD) (le_trans zero_le_one hH)]

theorem paperIsolatedCoefficientLoss_le_logarithmic
    (d : ℕ) (c₀ A : ℝ) (hc₀ : 0 < c₀) (hA : 0 ≤ A)
    (hc : |Real.log c₀| ≤ A * dimensionLogScale d) :
    paperIsolatedCoefficientLoss d c₀ ≤
      (A + 4) * (d + 1 : ℝ) * dimensionLogScale d := by
  rw [paperIsolatedCoefficientLoss_eq hc₀]
  have hD : (1 : ℝ) ≤ d + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hH := one_le_dimensionLogScale d
  have ht : Real.log (d + 2 : ℝ) ≤ dimensionLogScale d := by
    unfold dimensionLogScale
    linarith
  have hw := negative_log_profile_sqrt_le d c₀ hc₀
  have hw' : -Real.log (Real.sqrt (c₀ / (d + 2 : ℝ))) ≤
      (A + 1) * dimensionLogScale d / 2 := by linarith
  have hweight := mul_le_mul_of_nonneg_left hw' (show (0 : ℝ) ≤ d + 1 by positivity)
  have hcard := log_card_exteriorFamilyEntry_le (d + 1)
  push_cast at hcard
  rw [show (d : ℝ) + 1 + 1 = d + 2 by ring] at hcard
  nlinarith [mul_nonneg (sub_nonneg.mpr hD) (le_trans zero_le_one hH),
    mul_nonneg (show (0 : ℝ) ≤ d + 1 by positivity) (sub_nonneg.mpr hH),
    mul_nonneg (mul_nonneg hA (show (0 : ℝ) ≤ d + 1 by positivity))
      (le_trans zero_le_one hH)]

def realFreshLogConstant (L : ℝ) : ℝ := Real.log (max 1 (4 * L)) + 2

theorem realFreshLogConstant_nonneg (L : ℝ) : 0 ≤ realFreshLogConstant L := by
  unfold realFreshLogConstant
  linarith [Real.log_nonneg (le_max_left 1 (4 * L))]

theorem realFreshNegativeBound_le_uniform (d : ℕ) (L : ℝ) :
    realFreshNegativeBound d L ≤ realFreshLogConstant L * (d + 1 : ℝ) * dimensionLogScale d := by
  have hD : (1 : ℝ) ≤ d + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
  have hDp : (0 : ℝ) < d + 1 := by positivity
  have ht : 0 ≤ Real.log (d + 2 : ℝ) := Real.log_nonneg (by linarith)
  have ha : 0 ≤ Real.log (max 1 (4 * L)) := Real.log_nonneg (le_max_left _ _)
  have hlog := log_max_one_mul_le (d + 1 : ℝ) (4 * L) hD
  have hlogD : Real.log (d + 1 : ℝ) ≤ Real.log (d + 2 : ℝ) :=
    Real.log_le_log hDp (by linarith)
  have hscalar : Real.log (max 1 ((d + 1 : ℝ) * (4 * L))) + 1 ≤
      realFreshLogConstant L * dimensionLogScale d := by
    unfold realFreshLogConstant dimensionLogScale
    nlinarith [mul_nonneg ha ht]
  calc
    _ = (Real.log (max 1 ((d + 1 : ℝ) * (4 * L))) + 1) * (d + 1 : ℝ) := by
      unfold realFreshNegativeBound
      field_simp
    _ ≤ _ := by
      simpa only [mul_right_comm] using mul_le_mul_of_nonneg_right hscalar hDp.le

theorem realLiteralProjectiveCellLoss_le_logarithmic
    (d : ℕ) (c₀ A L : ℝ) (hc₀ : 0 < c₀) (hA : 0 ≤ A)
    (hc : |Real.log c₀| ≤ A * dimensionLogScale d) (q : ExteriorDegree (d + 1)) :
    realLiteralProjectiveCellLoss d c₀ L q ≤
      (A + 4 + realFreshLogConstant L) * (d + 1 : ℝ) * dimensionLogScale d := by
  have h := add_le_add (paperProjectiveCoefficientLogLoss_le_logarithmic d c₀ A hc₀ hA hc q)
    (realFreshNegativeBound_le_uniform d L)
  simpa only [realLiteralProjectiveCellLoss, realFreshNegativeBound,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_mul] using h

theorem complexLiteralProjectiveCellLoss_le_logarithmic
    (d : ℕ) (c₀ A L : ℝ) (hc₀ : 0 < c₀) (hA : 0 ≤ A)
    (hc : |Real.log c₀| ≤ A * dimensionLogScale d) (q : ExteriorDegree (d + 1)) :
    complexLiteralProjectiveCellLoss d c₀ L q ≤
      (A + 4 + uniformFreshNegativeConstant L) * (d + 1 : ℝ) * dimensionLogScale d := by
  have h := add_le_add (paperProjectiveCoefficientLogLoss_le_logarithmic d c₀ A hc₀ hA hc q)
    (complexFreshNegativeBound_le_uniform d L)
  simpa only [complexLiteralProjectiveCellLoss, complexFreshNegativeBound,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_mul] using h

theorem negativeLog_profile_b_le_logarithmic
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (A : ℝ) (hA : 0 ≤ A)
    (hc : |Real.log c₀| ≤ A * dimensionLogScale d) (i : Fin (d + 2)) :
    negativeLog ‖profile.b i‖ ≤ (A + 1) * dimensionLogScale d / 2 := by
  have hs : 0 < Real.sqrt (c₀ / (d + 2 : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have hlower : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ ‖profile.b i‖ := by
    simpa only [Nat.cast_add, Nat.cast_one, show (d : ℝ) + 1 + 1 = d + 2 by ring] using
      profile.sqrt_lower_le_norm_b i
  have hlog := Real.log_le_log hs hlower
  have hw := negative_log_profile_sqrt_le d c₀ hc₀
  have hH := one_le_dimensionLogScale d
  have ht : Real.log (d + 2 : ℝ) ≤ dimensionLogScale d := by
    unfold dimensionLogScale
    linarith
  rw [negativeLog, max_le_iff]
  constructor
  · positivity
  · linarith

theorem literalAtomRowCostBound_le_logarithmic
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (A K : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hc : |Real.log c₀| ≤ A * dimensionLogScale d) (z : ℂ) :
    literalAtomRowCostBound d profile z K ≤
      (6 * ‖z‖ + 7 + A + 2 * K) * dimensionLogScale d := by
  have hl := negativeLog_profile_b_le_logarithmic d profile hc₀ A hA hc 0
  have hr := negativeLog_profile_b_le_logarithmic d profile hc₀ A hA hc (Fin.last (d + 1))
  have hH := one_le_dimensionLogScale d
  unfold literalAtomRowCostBound
  nlinarith [mul_nonneg hK (sub_nonneg.mpr hH)]

/-- A single fixed constant dominates cells, terminal rows, and either atom branch. -/
def atomTransferConstant (A J K : ℝ) (z : ℂ) : ℝ :=
  6 * (A + J + 2 * K + 6 * ‖z‖ + 20)

theorem atomTransferConstant_nonneg (A J K : ℝ) (z : ℂ)
    (hA : 0 ≤ A) (hJ : 0 ≤ J) (hK : 0 ≤ K) : 0 ≤ atomTransferConstant A J K z := by
  unfold atomTransferConstant
  positivity

end CircularLawSections56.Section5
