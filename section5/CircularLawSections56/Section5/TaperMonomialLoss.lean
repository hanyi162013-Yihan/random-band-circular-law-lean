import CircularLawSections56.Section5.TaperLiteralProfile

/-! # The explicit exponential lower bound for selected taper amplitudes

Selecting one deterministic amplitude from each of the `2W` fresh rows costs
at most `Cκ W log(eW)` in the logarithm. Repeated offset selections are allowed,
as they are in the isolated-monomial word argument.
-/

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

theorem selected_amplitude_product_lower_logarithmic
    (d W : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    {c₀ C₀ A : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hA : 0 ≤ A)
    (hc : |Real.log c₀| ≤ A * dimensionLogScale d)
    (slot : Fin (d + 1) → Fin (d + 2)) :
    Real.exp (-(3 * (A + 1)) * (W : ℝ) * Real.log (Real.exp 1 * (W : ℝ))) ≤
      ∏ j, ‖profile.b (slot j)‖ := by
  have hpos (j : Fin (d + 1)) : 0 < ‖profile.b (slot j)‖ :=
    norm_pos_iff.2 (profile.b_ne_zero hc₀ _)
  have hterm (j : Fin (d + 1)) :
      -((A + 1) * dimensionLogScale d / 2) ≤ Real.log ‖profile.b (slot j)‖ := by
    have h := negativeLog_profile_b_le_logarithmic d profile hc₀ A hA hc (slot j)
    have hl : -Real.log ‖profile.b (slot j)‖ ≤ negativeLog ‖profile.b (slot j)‖ :=
      le_max_right _ _
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hterm j)
  have hd' : (d : ℝ) + 1 = 2 * (W : ℝ) := by exact_mod_cast hd
  have hscale := mul_le_mul_of_nonneg_left (dimensionLogScale_le_logEW d W hW hd)
    (mul_nonneg (show 0 ≤ A + 1 by linarith) (Nat.cast_nonneg W))
  have hprodpos : 0 < ∏ j, ‖profile.b (slot j)‖ := Finset.prod_pos (fun j _ => hpos j)
  rw [← Real.exp_log hprodpos]
  apply Real.exp_le_exp.2
  rw [Real.log_prod (fun j _ => (hpos j).ne')]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at hsum
  rw [hd'] at hsum
  nlinarith only [hsum, hscale]

theorem PolynomialTaperProfile.selected_amplitude_exponential_lower
    (p : PolynomialTaperProfile) (W : ℕ) (hW : 0 < W)
    (slot : Fin (taperStateDimension W + 1) → Fin (taperStateDimension W + 2)) :
    Real.exp (-(3 * (p.logarithmicWeightConstant + 1)) * (W : ℝ) *
      Real.log (Real.exp 1 * (W : ℝ))) ≤
        ∏ j, ‖(p.literalWeights W hW).b (slot j)‖ :=
  selected_amplitude_product_lower_logarithmic (taperStateDimension W) W hW
    (taperStateDimension_succ W hW) (p.literalWeights W hW) (p.lowerParameter_pos W)
    p.logarithmicWeightConstant_nonneg (p.literalWeights_logarithmic W hW) slot

end CircularLawSections56.Section5
