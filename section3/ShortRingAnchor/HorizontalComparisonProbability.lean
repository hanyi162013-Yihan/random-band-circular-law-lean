import ShortRingAnchor.HorizontalPolynomialNet

/-!
# Lemma 3.5: complete pointwise-to-compact probability conversion

This packages the arbitrary-radius grid, the interpolation error, and its
polynomial union-bound budget. Pointwise random-matrix estimates remain
arguments at this layer. In the two-ensemble application the factor `Q`
is `2`, accounting for comparison of both ensembles to their common reference.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace ShortRingAnchor

/-- Lemma 3.5's compact-net step, with no radius-five restriction. The failure
bound is explicit and the comparison exponent is common to all grid points. -/
theorem measure_horizontal_comparison_bad_polynomial_le
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {N R L d : ℝ} (hN : 1 ≤ N) (hR : 0 ≤ R)
    (hL0 : 0 ≤ L) (hL : L ≤ N) (hd : d ≤ 1)
    (f g : Omega → ℝ → ℂ) (Q : ℝ≥0∞)
    (hf : ∀ sample u w, ‖f sample u - f sample w‖ ≤ L * |u - w|)
    (hg : ∀ sample u w, ‖g sample u - g sample w‖ ≤ L * |u - w|)
    (hpoint : ∀ i : Fin (horizontalGridSize R (N ^ (-(2 : ℝ)))),
      mu {sample | 2 * N ^ (-d) <
        ‖f sample (horizontalGridCenter R (N ^ (-(2 : ℝ))) i) -
          g sample (horizontalGridCenter R (N ^ (-(2 : ℝ))) i)‖} ≤
        Q * ENNReal.ofReal (N ^ (-(10 : ℝ)))) :
    mu {sample | ∃ u ∈ Icc (-R) R, 4 * N ^ (-d) < ‖f sample u - g sample u‖} ≤
      Q * ENNReal.ofReal ((2 * R + 2) * N ^ (-(8 : ℝ))) := by
  have hdelta : 0 < N ^ (-(2 : ℝ)) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hN) _
  have herror := horizontalPolynomial_interpolation_error_le hN hL hd
  have hbound := measure_horizontal_comparison_bad_le mu hdelta hL0 f g
    (Q * ENNReal.ofReal (N ^ (-(10 : ℝ)))) hf hg hpoint
  calc
    _ ≤ mu {sample | ∃ u ∈ Icc (-R) R,
        2 * N ^ (-d) + 2 * L * N ^ (-(2 : ℝ)) < ‖f sample u - g sample u‖} := by
      apply measure_mono
      rintro sample ⟨u, hu, hsample⟩
      exact ⟨u, hu, lt_of_le_of_lt (by linarith) hsample⟩
    _ ≤ (horizontalGridSize R (N ^ (-(2 : ℝ))) : ℝ≥0∞) *
        (Q * ENNReal.ofReal (N ^ (-(10 : ℝ)))) := hbound
    _ = Q * ((horizontalGridSize R (N ^ (-(2 : ℝ))) : ℝ≥0∞) *
        ENNReal.ofReal (N ^ (-(10 : ℝ)))) := by ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl (horizontalPolynomial_failure_budget hN hR)

end ShortRingAnchor
