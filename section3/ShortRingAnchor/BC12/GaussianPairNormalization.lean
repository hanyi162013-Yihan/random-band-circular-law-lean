import ShortRingAnchor.BC12.GaussianEntryLawBridge

/-!
# Exact Gaussian-pair normalization shared by downstream chapters

The real coordinates of the normalized standard circular complex Gaussian
have variance `1/(2N)`. This is an elementary law identity, not an assumed
Ginibre estimate. Sections 8 and 10 use this same checked normalization.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace ShortRingAnchor.BC12

/-- Ginibre normalization in the Section 3.8 reference:
`(X+iY)/sqrt(N)`, with independent `N(0,1/2)` coordinates. -/
theorem normalizedGaussianPair_map {N : ℕ} (hN : 0 < N) :
    ((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))).map
      (fun p => Complex.measurableEquivRealProd.symm p / (Real.sqrt (N : ℝ) : ℂ)) =
      Ginibre.gaussianEntryLaw N := by
  let r : ℝ := (Real.sqrt (N : ℝ))⁻¹
  let v : ℝ≥0 := NNReal.mk (r ^ 2 / 2) (div_nonneg (sq_nonneg r) (by norm_num))
  have hr : 0 < r := by dsimp [r]; positivity
  have hv : 0 < v := by
    change (0 : ℝ) < r ^ 2 / 2
    exact div_pos (sq_pos_of_pos hr) (by norm_num)
  have hav : 2 * (v : ℝ) = (N : ℝ)⁻¹ := by
    change 2 * (r ^ 2 / 2) = (N : ℝ)⁻¹
    dsimp only [r]
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  have hreal : (gaussianReal 0 (1 / 2)).map (fun x => r * x) = gaussianReal 0 v := by
    have hvar : NNReal.mk (r ^ 2) (sq_nonneg r) * (1 / 2) = v := by
      apply NNReal.coe_injective
      change r ^ 2 * (1 / 2 : ℝ) = r ^ 2 / 2
      ring
    have h := (gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 (1 / 2))) r).map_eq
    simpa only [id_eq, mul_zero, hvar] using h
  rw [gaussianEntryLaw_eq_realPair (by exact_mod_cast hN) hv hav,
    ← hreal, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map Complex.measurableEquivRealProd.symm.measurable (by fun_prop)]
  congr 1
  funext p
  change Complex.measurableEquivRealProd.symm p / (Real.sqrt (N : ℝ) : ℂ) =
    Complex.measurableEquivRealProd.symm (r * p.1, r * p.2)
  rw [div_eq_mul_inv, ← Complex.ofReal_inv]
  change Complex.measurableEquivRealProd.symm p * (r : ℂ) =
    Complex.measurableEquivRealProd.symm (r * p.1, r * p.2)
  simp only [Complex.measurableEquivRealProd_symm_apply,
    Complex.mk_eq_add_mul_I, Complex.ofReal_mul]
  ring

end ShortRingAnchor.BC12
