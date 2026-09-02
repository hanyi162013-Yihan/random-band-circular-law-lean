import CircularLawSections56.Section5.PolynomialTaperProfile
import CircularLawSections56.Section5.RealAtomLogMoments

/-! # Exact taper profiles and their logarithmic endpoint costs

The lower indicator parameter is allowed to depend on `W`; it is not silently
treated as a fixed positive constant.  Its logarithm is evaluated explicitly.
-/

open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5.PolynomialTaperProfile

open CircularLawSection4

def lowerParameter (p : PolynomialTaperProfile) (W : ℕ) : ℝ :=
  (p.lower / p.upper) * (1 / (W + 1 : ℝ)) ^ p.exponent

def upperParameter (p : PolynomialTaperProfile) : ℝ :=
  2 * p.upper / (p.lower * (1 / 2 : ℝ) ^ p.exponent)

theorem lowerParameter_pos (p : PolynomialTaperProfile) (W : ℕ) : 0 < p.lowerParameter W :=
  mul_pos (div_pos p.lower_pos p.upper_pos) (Real.rpow_pos_of_pos (by positivity) _)

theorem upperParameter_pos (p : PolynomialTaperProfile) : 0 < p.upperParameter :=
  div_pos (mul_pos (by norm_num) p.upper_pos)
    (mul_pos p.lower_pos (Real.rpow_pos_of_pos (by norm_num) _))

def paperWeights (p : PolynomialTaperProfile) (W : ℕ) :
    PaperIndicatorWeights (2 * W) (p.lowerParameter W) p.upperParameter where
  q := p.weight W
  normalized := p.sum_weight W
  lower := by
    intro i
    have h := (p.weight_bounds W i).1
    convert h using 1
    simp only [lowerParameter, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  upper := by
    intro i
    have hinner : 0 < p.lower * (1 / 2 : ℝ) ^ p.exponent :=
      mul_pos p.lower_pos (Real.rpow_pos_of_pos (by norm_num) _)
    apply (p.weight_bounds W i).2.trans
    simp only [upperParameter, Nat.cast_mul, Nat.cast_ofNat, div_div]
    apply (div_le_div_iff₀ (mul_pos (by positivity) hinner) (mul_pos hinner (by positivity))).2
    have hN : (2 * W + 1 : ℝ) ≤ 2 * (W + 1 : ℝ) := by linarith
    convert mul_le_mul_of_nonneg_left hN (mul_nonneg p.upper_pos.le hinner.le) using 1 <;> ring

theorem log_lowerParameter (p : PolynomialTaperProfile) (W : ℕ) :
    Real.log (p.lowerParameter W) =
      Real.log (p.lower / p.upper) - p.exponent * Real.log (W + 1 : ℝ) := by
  rw [lowerParameter, Real.log_mul (div_pos p.lower_pos p.upper_pos).ne'
    (Real.rpow_pos_of_pos (by positivity) _).ne', Real.log_rpow (by positivity),
    Real.log_div one_ne_zero (by positivity : (W + 1 : ℝ) ≠ 0), Real.log_one]
  ring

theorem abs_log_lowerParameter_le (p : PolynomialTaperProfile) (W : ℕ) :
    |Real.log (p.lowerParameter W)| ≤
      |Real.log (p.lower / p.upper)| + p.exponent * Real.log (W + 1 : ℝ) := by
  rw [p.log_lowerParameter W]
  exact (abs_sub _ _).trans_eq (by
    rw [abs_of_nonneg (mul_nonneg p.exponent_nonneg
      (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) W])))])

/-- Every edge amplitude costs only `O(log(W+1))`, even though it has no
uniform indicator lower bound. -/
theorem negativeLog_amplitude_le (p : PolynomialTaperProfile) (W : ℕ)
    (i : Fin (2 * W + 1)) :
    negativeLog ‖(p.paperWeights W).b i‖ ≤
      (|Real.log (p.lower / p.upper)| + p.exponent * Real.log (W + 1 : ℝ) +
        Real.log (2 * W + 1 : ℝ)) / 2 := by
  have hlog : 0 ≤ Real.log (2 * W + 1 : ℝ) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) W])
  have hwlog : 0 ≤ Real.log (W + 1 : ℝ) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) W])
  have hc := p.lowerParameter_pos W
  have hs := (p.paperWeights W).sqrt_lower_le_norm_b i
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
  have hspos : 0 < Real.sqrt (p.lowerParameter W / (2 * W + 1 : ℝ)) :=
    Real.sqrt_pos.2 (by positivity)
  have h := Real.log_le_log hspos hs
  rw [Real.log_sqrt (by positivity), Real.log_div hc.ne' (by positivity)] at h
  have hp := p.abs_log_lowerParameter_le W
  have ha := neg_le_abs (Real.log (p.lowerParameter W))
  rw [negativeLog, max_le_iff]
  constructor
  · exact div_nonneg (add_nonneg
      (add_nonneg (abs_nonneg _) (mul_nonneg p.exponent_nonneg hwlog)) hlog) (by norm_num)
  · linarith

theorem inner_weight_lower (p : PolynomialTaperProfile) (W : ℕ) (j : Fin (W + 1)) :
    (p.lower * (1 / 2 : ℝ) ^ p.exponent) / ((2 * W + 1 : ℝ) * p.upper) ≤
      p.weight W (taperInnerIndex W j) := by
  apply (le_div_iff₀ (p.mass_pos W)).2
  calc
    _ ≤ ((p.lower * (1 / 2 : ℝ) ^ p.exponent) / ((2 * W + 1 : ℝ) * p.upper)) *
        ((2 * W + 1 : ℝ) * p.upper) :=
      mul_le_mul_of_nonneg_left (p.mass_bounds W).2
        (div_nonneg (mul_nonneg p.lower_pos.le (Real.rpow_nonneg (by norm_num) _))
          (mul_nonneg (by positivity) p.upper_pos.le))
    _ = p.lower * (1 / 2 : ℝ) ^ p.exponent := div_mul_cancel₀ _
      (mul_pos (by positivity) p.upper_pos).ne'
    _ ≤ _ := p.raw_inner_lower W j

end CircularLawSections56.Section5.PolynomialTaperProfile
