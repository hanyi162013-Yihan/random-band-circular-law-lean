import CircularLawSections56.Section5.LiteralPhysicalDeterminantSeam
import CircularLawSections56.Section5.LiteralPhysicalPressureSequence

/-!
# Dimension-uniform constants for the literal Section 4 estimates

The constants below depend on the density, profile lower bound, and fixed spectral
parameter, but not on the exterior degree, row length, or state dimension.  Cardinality
losses are bounded through the full power set, rather than assumed to be uniform.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

set_option maxHeartbeats 600000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

def dimensionLogScale (d : ℕ) : ℝ := 1 + Real.log (d + 2 : ℝ)

def uniformCoefficientConstant (c₀ : ℝ) : ℝ := |Real.log c₀| + 4

def uniformFreshNegativeConstant (L : ℝ) : ℝ := Real.log (max 1 (Real.pi * L)) + 2

def uniformFreshPositiveConstant (z : ℂ) : ℝ := 3 * ‖z‖ + 6

def uniformRawSeamConstant (c₀ L : ℝ) (z : ℂ) : ℝ :=
  uniformCoefficientConstant c₀ + uniformFreshNegativeConstant L +
    uniformFreshPositiveConstant z

theorem one_le_dimensionLogScale (d : ℕ) : 1 ≤ dimensionLogScale d := by
  have h : (1 : ℝ) ≤ d + 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  exact le_add_of_nonneg_right (Real.log_nonneg h)

theorem card_exteriorIndex_le_two_pow (D : ℕ) (q : ExteriorDegree D) :
    Fintype.card (ExteriorIndex D q) ≤ 2 ^ D := by
  have h := Fintype.card_le_of_injective
    (fun s : ExteriorIndex D q => (s : Finset (Fin D))) Subtype.val_injective
  simpa only [Fintype.card_finset, Fintype.card_fin] using h

theorem card_exteriorFamilyEntry_le (D : ℕ) :
    Fintype.card (ExteriorFamilyEntry D) ≤ (D + 1) * (2 ^ D) ^ 2 := by
  classical
  simp only [ExteriorFamilyEntry, Fintype.card_sigma, Fintype.card_prod]
  calc
    _ ≤ ∑ _q : ExteriorDegree D, (2 ^ D) ^ 2 := by
      apply Finset.sum_le_sum
      intro q _
      simpa only [pow_two] using Nat.mul_self_le_mul_self (card_exteriorIndex_le_two_pow D q)
    _ = _ := by simp [ExteriorDegree]

theorem log_card_exteriorIndex_le (D : ℕ) (q : ExteriorDegree D) :
    Real.log (Fintype.card (ExteriorIndex D q) : ℝ) ≤ (D : ℝ) := by
  let : Nonempty (ExteriorIndex D q) := exteriorIndex_nonempty_bridge D q
  have hpos : (0 : ℝ) < Fintype.card (ExteriorIndex D q) := by exact_mod_cast Fintype.card_pos
  have hle : (Fintype.card (ExteriorIndex D q) : ℝ) ≤ (2 : ℝ) ^ D := by
    exact_mod_cast card_exteriorIndex_le_two_pow D q
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ Real.log ((2 : ℝ) ^ D) := Real.log_le_log hpos hle
    _ = (D : ℝ) * Real.log 2 := Real.log_pow _ _
    _ ≤ (D : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) D]

theorem log_card_exteriorFamilyEntry_le (D : ℕ) :
    Real.log (Fintype.card (ExteriorFamilyEntry D) : ℝ) ≤
      Real.log (D + 1 : ℝ) + 2 * (D : ℝ) := by
  have hpos : (0 : ℝ) < Fintype.card (ExteriorFamilyEntry D) := by
    exact_mod_cast Fintype.card_pos
  have hle : (Fintype.card (ExteriorFamilyEntry D) : ℝ) ≤
      (D + 1 : ℝ) * ((2 : ℝ) ^ D) ^ 2 := by
    exact_mod_cast card_exteriorFamilyEntry_le D
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ Real.log ((D + 1 : ℝ) * ((2 : ℝ) ^ D) ^ 2) := Real.log_le_log hpos hle
    _ = Real.log (D + 1 : ℝ) + 2 * ((D : ℝ) * Real.log 2) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      norm_num
    _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) D]

theorem negative_log_profile_sqrt_le (d : ℕ) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    -Real.log (Real.sqrt (c₀ / (d + 2 : ℝ))) ≤
      (|Real.log c₀| + Real.log (d + 2 : ℝ)) / 2 := by
  rw [Real.log_sqrt (by positivity), Real.log_div hc₀.ne' (by positivity)]
  linarith [neg_le_abs (Real.log c₀)]

/-- Uniform coefficient loss, with no exterior-cardinality premise. -/
theorem paperProjectiveCoefficientLogLoss_le_uniform
    (d : ℕ) (c₀ : ℝ) (hc₀ : 0 < c₀) (q : ExteriorDegree (d + 1)) :
    paperProjectiveCoefficientLogLoss d c₀ q ≤
      uniformCoefficientConstant c₀ * (d + 1 : ℝ) * dimensionLogScale d := by
  have hD : (1 : ℝ) ≤ d + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have ht : 0 ≤ Real.log (d + 2 : ℝ) := Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  have ha : 0 ≤ |Real.log c₀| := abs_nonneg _
  have hweight := mul_le_mul_of_nonneg_left (negative_log_profile_sqrt_le d c₀ hc₀)
    (show (0 : ℝ) ≤ d + 1 by positivity)
  have hcard := log_card_exteriorIndex_le (d + 1) q
  rw [paperProjectiveCoefficientLogLoss, max_le_iff]
  dsimp only [uniformCoefficientConstant, dimensionLogScale]
  constructor
  · positivity
  · push_cast at hcard ⊢
    nlinarith [mul_nonneg ha ht, mul_nonneg (sub_nonneg.mpr hD) ht,
      mul_nonneg (show (0 : ℝ) ≤ d + 1 by positivity) (mul_nonneg ha ht)]

/-- Uniform isolated determinant coefficient loss. -/
theorem paperIsolatedCoefficientLoss_le_uniform
    (d : ℕ) (c₀ : ℝ) (hc₀ : 0 < c₀) :
    paperIsolatedCoefficientLoss d c₀ ≤
      uniformCoefficientConstant c₀ * (d + 1 : ℝ) * dimensionLogScale d := by
  rw [paperIsolatedCoefficientLoss_eq hc₀]
  have hD : (1 : ℝ) ≤ d + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have ht : 0 ≤ Real.log (d + 2 : ℝ) := Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  have ha : 0 ≤ |Real.log c₀| := abs_nonneg _
  have hweight := mul_le_mul_of_nonneg_left (negative_log_profile_sqrt_le d c₀ hc₀)
    (show (0 : ℝ) ≤ d + 1 by positivity)
  have hcard := log_card_exteriorFamilyEntry_le (d + 1)
  dsimp only [uniformCoefficientConstant, dimensionLogScale]
  push_cast at hcard
  rw [show (d : ℝ) + 1 + 1 = d + 2 by ring] at hcard
  nlinarith [mul_nonneg ha ht, mul_nonneg (sub_nonneg.mpr hD) ht,
    mul_nonneg (show (0 : ℝ) ≤ d + 1 by positivity) (mul_nonneg ha ht)]

theorem log_max_one_mul_le (D a : ℝ) (hD : 1 ≤ D) :
    Real.log (max 1 (D * a)) ≤ Real.log D + Real.log (max 1 a) := by
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have ha : 0 < max 1 a := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  calc
    _ ≤ Real.log (D * max 1 a) := by
      apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      apply max_le
      · exact le_trans hD (le_mul_of_one_le_right hDp.le (le_max_left _ _))
      · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hDp.le
    _ = _ := Real.log_mul hDp.ne' ha.ne'

theorem complexFreshNegativeBound_le_uniform (d : ℕ) (L : ℝ) :
    complexFreshNegativeBound d L ≤
      uniformFreshNegativeConstant L * (d + 1 : ℝ) * dimensionLogScale d := by
  have hD : (1 : ℝ) ≤ d + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hDpos : (0 : ℝ) < d + 1 := by positivity
  have ht : 0 ≤ Real.log (d + 2 : ℝ) :=
    Real.log_nonneg (by linarith)
  have ha : 0 ≤ Real.log (max 1 (Real.pi * L)) := Real.log_nonneg (le_max_left _ _)
  have hlog := log_max_one_mul_le (d + 1 : ℝ) (Real.pi * L) hD
  have hlogD : Real.log (d + 1 : ℝ) ≤ Real.log (d + 2 : ℝ) :=
    Real.log_le_log hDpos (by linarith)
  have hscalar : (Real.log (max 1 ((d + 1 : ℝ) * (Real.pi * L))) + 1) / 2 ≤
      (Real.log (max 1 (Real.pi * L)) + 2) * (1 + Real.log (d + 2 : ℝ)) := by
    nlinarith [mul_nonneg ha ht]
  calc
    _ = ((Real.log (max 1 ((d + 1 : ℝ) * (Real.pi * L))) + 1) / 2) *
        (d + 1 : ℝ) := by unfold complexFreshNegativeBound; field_simp
    _ ≤ _ := by
      simpa only [uniformFreshNegativeConstant, dimensionLogScale, mul_right_comm] using
        mul_le_mul_of_nonneg_right hscalar hDpos.le

theorem paperFreshTraceFactor_le (d : ℕ) :
    paperFreshTraceFactor d ≤ (d + 2 : ℝ) * (2 : ℝ) ^ (d + 1) := by
  unfold paperFreshTraceFactor
  calc
    _ ≤ ∑ _q : ExteriorDegree (d + 1), (2 : ℝ) ^ (d + 1) := by
      apply Finset.sum_le_sum
      intro q _
      exact_mod_cast card_exteriorIndex_le_two_pow (d + 1) q
    _ = _ := by simp [ExteriorDegree]; ring

theorem posLog_paperFreshTraceFactor_le (d : ℕ) :
    Real.posLog (paperFreshTraceFactor d) ≤
      2 * (d + 1 : ℝ) * dimensionLogScale d := by
  have hD : (1 : ℝ) ≤ d + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have ht : 0 ≤ Real.log (d + 2 : ℝ) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hbound : Real.log (paperFreshTraceFactor d) ≤
      Real.log (d + 2 : ℝ) + (d + 1 : ℝ) := by
    calc
      _ ≤ Real.log ((d + 2 : ℝ) * (2 : ℝ) ^ (d + 1)) :=
        Real.log_le_log (paperFreshTraceFactor_pos d) (paperFreshTraceFactor_le d)
      _ = Real.log (d + 2 : ℝ) + (d + 1 : ℝ) * Real.log 2 := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        push_cast
        rfl
      _ ≤ _ := by nlinarith
  rw [Real.posLog, max_le_iff]
  dsimp only [dimensionLogScale]
  constructor
  · positivity
  · nlinarith [mul_nonneg (sub_nonneg.mpr hD) ht]

theorem freshRow_sqrt_moment_le_uniform (d : ℕ) (z : ℂ) :
    Real.sqrt (3 * Real.log (d + 2 : ℝ) ^ 2 + 3 + 3 * ‖z‖ ^ 2) ≤
      (3 * ‖z‖ + 3) * dimensionLogScale d := by
  have ht : 0 ≤ Real.log (d + 2 : ℝ) :=
    Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  have hz := norm_nonneg z
  have hsum : 0 ≤ Real.log (d + 2 : ℝ) + 1 + ‖z‖ := by positivity
  have hsq : 3 * Real.log (d + 2 : ℝ) ^ 2 + 3 + 3 * ‖z‖ ^ 2 ≤
      (3 * (Real.log (d + 2 : ℝ) + 1 + ‖z‖)) ^ 2 := by
    nlinarith [mul_nonneg ht hz]
  calc
    _ ≤ 3 * (Real.log (d + 2 : ℝ) + 1 + ‖z‖) :=
      Real.sqrt_le_iff.2 ⟨by positivity, hsq⟩
    _ ≤ _ := by dsimp only [dimensionLogScale]; nlinarith [mul_nonneg ht hz]

theorem paperFreshPositiveBound_le_uniform (d : ℕ) (z : ℂ) :
    paperFreshPositiveBound d z ≤
      uniformFreshPositiveConstant z * (d + 1 : ℝ) * dimensionLogScale d := by
  have htrace := posLog_paperFreshTraceFactor_le d
  have hrow := mul_le_mul_of_nonneg_left (freshRow_sqrt_moment_le_uniform d z)
    (show (0 : ℝ) ≤ d + 1 by positivity)
  have hscale : 0 ≤ (d + 1 : ℝ) * dimensionLogScale d :=
    mul_nonneg (by positivity) (le_trans zero_le_one (one_le_dimensionLogScale d))
  dsimp only [paperFreshPositiveBound, uniformFreshPositiveConstant]
  nlinarith only [htrace, hrow, hscale]

theorem rawSeamLoss_le_uniform (d : ℕ) (c₀ L : ℝ) (z : ℂ) (hc₀ : 0 < c₀) :
    paperIsolatedCoefficientLoss d c₀ + complexFreshNegativeBound d L +
        paperFreshPositiveBound d z ≤
      uniformRawSeamConstant c₀ L z * (d + 1 : ℝ) * dimensionLogScale d := by
  have h := add_le_add (add_le_add (paperIsolatedCoefficientLoss_le_uniform d c₀ hc₀)
    (complexFreshNegativeBound_le_uniform d L)) (paperFreshPositiveBound_le_uniform d z)
  simpa only [uniformRawSeamConstant, add_mul] using h

theorem complexLiteralProjectiveCellLoss_le_uniform
    (d : ℕ) (c₀ L : ℝ) (hc₀ : 0 < c₀) (q : ExteriorDegree (d + 1)) :
    complexLiteralProjectiveCellLoss d c₀ L q ≤
      (uniformCoefficientConstant c₀ + uniformFreshNegativeConstant L) *
        (d + 1 : ℝ) * dimensionLogScale d := by
  have h := add_le_add (paperProjectiveCoefficientLogLoss_le_uniform d c₀ hc₀ q)
    (complexFreshNegativeBound_le_uniform d L)
  simpa only [complexLiteralProjectiveCellLoss, complexFreshNegativeBound,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_mul] using h

def uniformFiberNegativeConstant (c₀ L : ℝ) : ℝ :=
  Real.log (max 1 (Real.pi * L)) + |Real.log c₀| + 3

def uniformFiberSquareConstant (c₀ L : ℝ) (z : ℂ) : ℝ :=
  8 * (uniformFiberNegativeConstant c₀ L + 1) ^ 2 +
    2 * (3 * ‖z‖ + 3) ^ 2

theorem fiberNegativeLog_le_uniform (d : ℕ) (c₀ L : ℝ) (hc₀ : 0 < c₀) :
    Real.log (max 1 ((max 1 (Real.pi * L)) /
      ((1 / 2 : ℝ) * Real.sqrt (c₀ / (d + 2 : ℝ))))) ≤
      uniformFiberNegativeConstant c₀ L * dimensionLogScale d := by
  have hs : 0 < Real.sqrt (c₀ / (d + 2 : ℝ)) := Real.sqrt_pos.2 (by positivity)
  have ha : 0 ≤ Real.log (max 1 (Real.pi * L)) := Real.log_nonneg (le_max_left _ _)
  have hb := abs_nonneg (Real.log c₀)
  have ht : 0 ≤ Real.log (d + 2 : ℝ) :=
    Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.posLog_eq_log_max_one (by positivity), Real.posLog, max_le_iff]
  dsimp only [uniformFiberNegativeConstant, dimensionLogScale]
  constructor
  · positivity
  · rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) hs.ne', Real.log_div (by norm_num) (by norm_num), Real.log_one]
    nlinarith [negative_log_profile_sqrt_le d c₀ hc₀, mul_nonneg ha ht, mul_nonneg hb ht]

/-- The actual Section 4 fiber variance is bounded by a constant times `log² d`.
No degree or row-length dependence is hidden in the constant. -/
theorem complexPaperPressureFiberL2Bound_le_uniform
    (d : ℕ) (c₀ L : ℝ) (z : ℂ) (hc₀ : 0 < c₀) :
    complexPaperPressureFiberL2Bound d c₀ L z ≤
      uniformFiberSquareConstant c₀ L z * dimensionLogScale d ^ 2 := by
  have hH := one_le_dimensionLogScale d
  have hneg := fiberNegativeLog_le_uniform d c₀ L hc₀
  have hneg0 : 0 ≤ Real.log (max 1 ((max 1 (Real.pi * L)) /
      ((1 / 2 : ℝ) * Real.sqrt (c₀ / (d + 2 : ℝ))))) :=
    Real.log_nonneg (le_max_left _ _)
  have hneg1 : Real.log (max 1 ((max 1 (Real.pi * L)) /
      ((1 / 2 : ℝ) * Real.sqrt (c₀ / (d + 2 : ℝ))))) + 1 ≤
      (uniformFiberNegativeConstant c₀ L + 1) * dimensionLogScale d := by
    nlinarith only [hneg, hH]
  have hnegsq := pow_le_pow_left₀ (by positivity : 0 ≤ Real.log (max 1
      ((max 1 (Real.pi * L)) / ((1 / 2 : ℝ) * Real.sqrt (c₀ / (d + 2 : ℝ))))) + 1)
    hneg1 2
  have hpos := freshRow_sqrt_moment_le_uniform d z
  have hpossq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hpos 2
  rw [Real.sq_sqrt (by positivity)] at hpossq
  dsimp only [complexPaperPressureFiberL2Bound, oneSidedLogSecondMomentBound,
    uniformFiberSquareConstant]
  simp only [div_one, mul_one]
  nlinarith only [hnegsq, hpossq]

theorem dimensionLogScale_le_logEW (d W : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W) :
    dimensionLogScale d ≤ 3 * Real.log (Real.exp 1 * (W : ℝ)) := by
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWp : (0 : ℝ) < W := by positivity
  have hdr : (d : ℝ) + 1 = 2 * (W : ℝ) := by exact_mod_cast hd
  have hlogW := Real.log_nonneg hWr
  have hlog3 : Real.log 3 ≤ (2 : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hdim : Real.log (d + 2 : ℝ) ≤ Real.log 3 + Real.log (W : ℝ) := by
    calc
      _ ≤ Real.log (3 * (W : ℝ)) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := Real.log_mul (by norm_num) hWp.ne'
  rw [Real.log_mul (Real.exp_pos 1).ne' hWp.ne', Real.log_exp]
  dsimp only [dimensionLogScale]
  linarith

theorem uniformRawSeamConstant_nonneg (c₀ L : ℝ) (z : ℂ) :
    0 ≤ uniformRawSeamConstant c₀ L z := by
  have h := Real.log_nonneg (le_max_left 1 (Real.pi * L))
  unfold uniformRawSeamConstant uniformCoefficientConstant uniformFreshNegativeConstant
    uniformFreshPositiveConstant
  positivity

/-- A single fixed constant controls the raw seam, cell loss, and fiber variance.
The displayed dimension factors are the manuscript's `W log(eW)` and `log²(eW)`. -/
def uniformLiteralConstant (c₀ L : ℝ) (z : ℂ) : ℝ :=
  6 * uniformRawSeamConstant c₀ L z + 9 * uniformFiberSquareConstant c₀ L z + 1

theorem uniformLiteralConstant_pos (c₀ L : ℝ) (z : ℂ) :
    0 < uniformLiteralConstant c₀ L z := by
  have h := uniformRawSeamConstant_nonneg c₀ L z
  unfold uniformLiteralConstant uniformFiberSquareConstant
  positivity

theorem rawSeamLoss_le_uniform_logEW
    (d W : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    (c₀ L : ℝ) (z : ℂ) (hc₀ : 0 < c₀) :
    paperIsolatedCoefficientLoss d c₀ + complexFreshNegativeBound d L +
        paperFreshPositiveBound d z ≤
      uniformLiteralConstant c₀ L z * ((W : ℝ) * Real.log (Real.exp 1 * (W : ℝ))) := by
  have hC := uniformRawSeamConstant_nonneg c₀ L z
  have hH := dimensionLogScale_le_logEW d W hW hd
  have hdim : (d : ℝ) + 1 = 2 * (W : ℝ) := by exact_mod_cast hd
  have hL : 0 ≤ Real.log (Real.exp 1 * (W : ℝ)) := by
    have := one_le_dimensionLogScale d
    linarith
  have hcoef : 6 * uniformRawSeamConstant c₀ L z ≤ uniformLiteralConstant c₀ L z := by
    unfold uniformLiteralConstant uniformFiberSquareConstant
    nlinarith [sq_nonneg (uniformFiberNegativeConstant c₀ L + 1), sq_nonneg (3 * ‖z‖ + 3)]
  calc
    _ ≤ uniformRawSeamConstant c₀ L z * (d + 1 : ℝ) * dimensionLogScale d :=
      rawSeamLoss_le_uniform d c₀ L z hc₀
    _ ≤ (6 * uniformRawSeamConstant c₀ L z) *
        ((W : ℝ) * Real.log (Real.exp 1 * (W : ℝ))) := by
      have h := mul_le_mul_of_nonneg_left hH
        (mul_nonneg hC (show (0 : ℝ) ≤ d + 1 by positivity))
      rw [hdim] at h
      rw [hdim]
      nlinarith only [h]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by positivity) hL)

theorem fiberSquare_le_uniform_logEW
    (d W : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    (c₀ L : ℝ) (z : ℂ) (hc₀ : 0 < c₀) :
    complexPaperPressureFiberL2Bound d c₀ L z ≤
      uniformLiteralConstant c₀ L z * Real.log (Real.exp 1 * (W : ℝ)) ^ 2 := by
  have hF : 0 ≤ uniformFiberSquareConstant c₀ L z := by
    unfold uniformFiberSquareConstant
    positivity
  have hH := pow_le_pow_left₀ (le_trans zero_le_one (one_le_dimensionLogScale d))
    (dimensionLogScale_le_logEW d W hW hd) 2
  have hC := uniformRawSeamConstant_nonneg c₀ L z
  have hcoef : 9 * uniformFiberSquareConstant c₀ L z ≤ uniformLiteralConstant c₀ L z := by
    unfold uniformLiteralConstant
    linarith
  calc
    _ ≤ uniformFiberSquareConstant c₀ L z * dimensionLogScale d ^ 2 :=
      complexPaperPressureFiberL2Bound_le_uniform d c₀ L z hc₀
    _ ≤ (9 * uniformFiberSquareConstant c₀ L z) * Real.log (Real.exp 1 * (W : ℝ)) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hH hF
      nlinarith only [h]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)

end CircularLawSections56.Section5
