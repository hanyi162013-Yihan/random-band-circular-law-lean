import BernoulliSection9.ExternalInputs

/-!
# Uniform numerical form of the two Cook error terms

The terminal residual is split into two square blocks whose side lengths are
between `W / 3` and `3 * W` in the multiplicative sense used below.  This
module removes those two auxiliary dimensions from Cook's failure bound.
It is entirely deterministic and introduces no probabilistic input.
-/

noncomputable section

namespace BernoulliSection9

/-- A deliberately relaxed Cook error bound, uniform over every dimension
`n` satisfying `W / 3 ≤ n` and `n ≤ 3W`.  The denominator `4` in the
exponential term absorbs the unavoidable integer-rounding loss in
`W / 3 ≤ n`. -/
def uniformCookFailureBound (C c : ℝ) (W : ℕ) : ℝ :=
  C * Real.sqrt (9 * Real.log (3 * (W : ℝ)) / (W : ℝ)) +
    Real.exp (-c * (W : ℝ) / 4)

/-- Cook's numerical failure bound at a dimension comparable with `W` is
bounded by a quantity depending only on `W` and Cook's two constants. -/
theorem cookFailureBound_le_uniform
    (C c : ℝ) (W n : ℕ)
    (hW : 9 ≤ W) (hWdivn : W / 3 ≤ n) (hnW : n ≤ 3 * W)
    (hC : 0 ≤ C) (hc : 0 < c) :
    cookFailureBound C c n ≤ uniformCookFailureBound C c W := by
  have hWposNat : 0 < W := lt_of_lt_of_le (by norm_num) hW
  have hnLower : 3 ≤ n := by omega
  have hnposNat : 0 < n := lt_of_lt_of_le (by norm_num) hnLower
  have hWpos : 0 < (W : ℝ) := by exact_mod_cast hWposNat
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
  have hWn : W ≤ 4 * n := by omega
  have hWnReal : (W : ℝ) ≤ 4 * (n : ℝ) := by exact_mod_cast hWn
  have hnWReal : (n : ℝ) ≤ 3 * (W : ℝ) := by exact_mod_cast hnW
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hthreeW_pos : 0 < 3 * (W : ℝ) := mul_pos (by norm_num) hWpos
  have hlogthreeW_nonneg : 0 ≤ Real.log (3 * (W : ℝ)) :=
    Real.log_nonneg (by
      have : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast (show 1 ≤ W by omega)
      nlinarith)
  have hlog : Real.log (n : ℝ) ≤ Real.log (3 * (W : ℝ)) :=
    Real.log_le_log hnpos hnWReal
  have hquotient :
      Real.log (n : ℝ) / (n : ℝ) ≤
        9 * Real.log (3 * (W : ℝ)) / (W : ℝ) := by
    calc
      Real.log (n : ℝ) / (n : ℝ) ≤
          Real.log (3 * (W : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog hnpos.le
      _ ≤ 4 * Real.log (3 * (W : ℝ)) / (W : ℝ) := by
        apply (div_le_div_iff₀ hnpos hWpos).2
        have hmul := mul_le_mul_of_nonneg_left hWnReal hlogthreeW_nonneg
        nlinarith
      _ ≤ 9 * Real.log (3 * (W : ℝ)) / (W : ℝ) := by
        apply div_le_div_of_nonneg_right _ hWpos.le
        nlinarith
  have hsqrt :
      Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) ≤
        Real.sqrt (9 * Real.log (3 * (W : ℝ)) / (W : ℝ)) :=
    Real.sqrt_le_sqrt hquotient
  have hmain :
      C * Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) ≤
        C * Real.sqrt (9 * Real.log (3 * (W : ℝ)) / (W : ℝ)) :=
    mul_le_mul_of_nonneg_left hsqrt hC
  have hexponent : -c * (n : ℝ) ≤ -c * (W : ℝ) / 4 := by
    nlinarith [mul_pos hc hWpos]
  have hexp : Real.exp (-c * (n : ℝ)) ≤ Real.exp (-c * (W : ℝ) / 4) :=
    Real.exp_le_exp.mpr hexponent
  simpa [cookFailureBound, uniformCookFailureBound] using add_le_add hmain hexp

/-- The sum of two Cook errors at possibly different comparable dimensions,
with unrelated constants, is controlled by the sum of their uniform bounds. -/
theorem twoCookFailureBounds_le_uniform
    (C₁ c₁ C₂ c₂ : ℝ) (W n₁ n₂ : ℕ)
    (hW : 9 ≤ W)
    (hWdivn₁ : W / 3 ≤ n₁) (hn₁W : n₁ ≤ 3 * W)
    (hWdivn₂ : W / 3 ≤ n₂) (hn₂W : n₂ ≤ 3 * W)
    (hC₁ : 0 ≤ C₁) (hc₁ : 0 < c₁)
    (hC₂ : 0 ≤ C₂) (hc₂ : 0 < c₂) :
    cookFailureBound C₁ c₁ n₁ + cookFailureBound C₂ c₂ n₂ ≤
      uniformCookFailureBound C₁ c₁ W + uniformCookFailureBound C₂ c₂ W := by
  exact add_le_add
    (cookFailureBound_le_uniform C₁ c₁ W n₁ hW hWdivn₁ hn₁W hC₁ hc₁)
    (cookFailureBound_le_uniform C₂ c₂ W n₂ hW hWdivn₂ hn₂W hC₂ hc₂)

/-- The preceding two-block estimate specialized to Cook's constants at two
possibly different deformation exponents. -/
theorem twoCookFailureBounds_le_uniform_of_input
    (cook : CookDeformedSquareInput) (L₁ L₂ : ℝ) (W n₁ n₂ : ℕ)
    (hW : 9 ≤ W)
    (hWdivn₁ : W / 3 ≤ n₁) (hn₁W : n₁ ≤ 3 * W)
    (hWdivn₂ : W / 3 ≤ n₂) (hn₂W : n₂ ≤ 3 * W) :
    cookFailureBound (cook.cookC L₁) (cook.cookc L₁) n₁ +
        cookFailureBound (cook.cookC L₂) (cook.cookc L₂) n₂ ≤
      uniformCookFailureBound (cook.cookC L₁) (cook.cookc L₁) W +
        uniformCookFailureBound (cook.cookC L₂) (cook.cookc L₂) W := by
  exact twoCookFailureBounds_le_uniform
    (cook.cookC L₁) (cook.cookc L₁)
    (cook.cookC L₂) (cook.cookc L₂) W n₁ n₂ hW
    hWdivn₁ hn₁W hWdivn₂ hn₂W
    (cook.C_nonneg L₁) (cook.c_pos L₁)
    (cook.C_nonneg L₂) (cook.c_pos L₂)

end BernoulliSection9
