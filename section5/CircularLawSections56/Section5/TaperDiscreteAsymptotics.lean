import CircularLawSections56.Section5.PolynomialTaperProfile

/-! # Explicit discrete bounds in the polynomial-taper corollary

These are the manuscript's `Z ≍ W`, `max q ≤ C/W`, `min q ≥ c/W^(1+κ)`
and inner-band `q ≥ c/W`, with fixed positive constants and no asymptotic
notation hiding a width-dependent factor.
-/

noncomputable section
set_option autoImplicit false

namespace CircularLawSections56.Section5.PolynomialTaperProfile

def innerRawConstant (p : PolynomialTaperProfile) : ℝ :=
  p.lower * (1 / 2 : ℝ) ^ p.exponent

def lowerWeightConstant (p : PolynomialTaperProfile) : ℝ := p.innerRawConstant / (3 * p.upper)

def upperWeightConstant (p : PolynomialTaperProfile) : ℝ := p.upper / p.innerRawConstant

theorem innerRawConstant_pos (p : PolynomialTaperProfile) : 0 < p.innerRawConstant :=
  mul_pos p.lower_pos (Real.rpow_pos_of_pos (by norm_num) _)

theorem lowerWeightConstant_pos (p : PolynomialTaperProfile) : 0 < p.lowerWeightConstant :=
  div_pos p.innerRawConstant_pos (mul_pos (by norm_num) p.upper_pos)

theorem upperWeightConstant_pos (p : PolynomialTaperProfile) : 0 < p.upperWeightConstant :=
  div_pos p.upper_pos p.innerRawConstant_pos

theorem mass_linear_bounds (p : PolynomialTaperProfile) (W : ℕ) (hW : 0 < W) :
    p.innerRawConstant * (W : ℝ) ≤ p.mass W ∧ p.mass W ≤ (3 * p.upper) * (W : ℝ) := by
  have hw : (1 : ℝ) ≤ W := by exact_mod_cast hW
  constructor
  · apply le_trans _ (p.mass_bounds W).1
    change p.innerRawConstant * (W : ℝ) ≤ (W + 1 : ℝ) * p.innerRawConstant
    nlinarith [p.innerRawConstant_pos]
  · apply (p.mass_bounds W).2.trans
    nlinarith [p.upper_pos]

theorem weight_upper_linear (p : PolynomialTaperProfile) (W : ℕ) (hW : 0 < W)
    (i : Fin (2 * W + 1)) : p.weight W i ≤ p.upperWeightConstant / (W : ℝ) := by
  have hw : (0 : ℝ) < W := Nat.cast_pos.2 hW
  apply (p.weight_bounds W i).2.trans
  change p.upper / ((W + 1 : ℝ) * p.innerRawConstant) ≤
    (p.upper / p.innerRawConstant) / (W : ℝ)
  calc
    _ ≤ p.upper / ((W : ℝ) * p.innerRawConstant) :=
      div_le_div_of_nonneg_left p.upper_pos.le (mul_pos hw p.innerRawConstant_pos)
        (mul_le_mul_of_nonneg_right (by linarith) p.innerRawConstant_pos.le)
    _ = _ := by ring

theorem weight_lower_polynomial (p : PolynomialTaperProfile) (W : ℕ) (hW : 0 < W)
    (i : Fin (2 * W + 1)) :
    p.lowerWeightConstant / (W : ℝ) ^ (p.exponent + 1) ≤ p.weight W i := by
  have hw : (0 : ℝ) < W := Nat.cast_pos.2 hW
  have hw1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hgap : 1 / (2 * (W : ℝ)) ≤ 1 / (W + 1 : ℝ) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hpow := Real.rpow_le_rpow (by positivity) hgap p.exponent_nonneg
  have hquot : (1 / (2 * (W : ℝ))) ^ p.exponent =
      (1 / 2 : ℝ) ^ p.exponent / (W : ℝ) ^ p.exponent := by
    rw [show 1 / (2 * (W : ℝ)) = (1 / 2 : ℝ) / (W : ℝ) by ring]
    exact Real.div_rpow (by norm_num) hw.le _
  have hden : (2 * (W : ℝ) + 1) * p.upper ≤ 3 * (W : ℝ) * p.upper :=
    mul_le_mul_of_nonneg_right (by linarith) p.upper_pos.le
  have hnum : 0 ≤ p.lower * (1 / (2 * (W : ℝ))) ^ p.exponent :=
    mul_nonneg p.lower_pos.le (Real.rpow_nonneg (by positivity) _)
  calc
    _ = (p.lower * (1 / (2 * (W : ℝ))) ^ p.exponent) /
        (3 * (W : ℝ) * p.upper) := by
      rw [hquot, Real.rpow_add_one hw.ne']
      unfold lowerWeightConstant innerRawConstant
      ring
    _ ≤ (p.lower * (1 / (2 * (W : ℝ))) ^ p.exponent) /
        ((2 * (W : ℝ) + 1) * p.upper) :=
      div_le_div_of_nonneg_left hnum (mul_pos (by positivity) p.upper_pos) hden
    _ ≤ (p.lower * (1 / (W + 1 : ℝ)) ^ p.exponent) /
        ((2 * (W : ℝ) + 1) * p.upper) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow p.lower_pos.le)
        (mul_nonneg (by positivity) p.upper_pos.le)
    _ ≤ _ := (p.weight_bounds W i).1

theorem weight_inner_linear (p : PolynomialTaperProfile) (W : ℕ) (hW : 0 < W)
    (i : Fin (2 * W + 1)) (hi : |taperGrid W i| ≤ 1 / 2) :
    p.lowerWeightConstant / (W : ℝ) ≤ p.weight W i := by
  have hw : (0 : ℝ) < W := Nat.cast_pos.2 hW
  have hr : p.innerRawConstant ≤ p.raw W i :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by norm_num)
      (by linarith : (1 / 2 : ℝ) ≤ 1 - |taperGrid W i|) p.exponent_nonneg)
      p.lower_pos.le).trans (p.interior _ (taperGrid_abs_lt_one W i)).1
  change p.lowerWeightConstant / (W : ℝ) ≤ p.raw W i / p.mass W
  calc
    _ = p.innerRawConstant / ((3 * p.upper) * (W : ℝ)) := by
      unfold lowerWeightConstant
      ring
    _ ≤ p.innerRawConstant / p.mass W := div_le_div_of_nonneg_left
      p.innerRawConstant_pos.le (p.mass_pos W) (p.mass_linear_bounds W hW).2
    _ ≤ _ := div_le_div_of_nonneg_right hr (p.mass_pos W).le

theorem weight_center_linear (p : PolynomialTaperProfile) (W : ℕ) (hW : 0 < W) :
    p.lowerWeightConstant / (W : ℝ) ≤ p.weight W ⟨W, by omega⟩ := by
  apply p.weight_inner_linear W hW
  simp [taperGrid]

end CircularLawSections56.Section5.PolynomialTaperProfile
