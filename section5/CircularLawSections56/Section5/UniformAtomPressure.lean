import CircularLawSections56.Section5.AtomFreshFinite

/-! # The two literal transfer estimates with one fixed constant -/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1000000

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

theorem literal_cell_error_le_atomTransferConstant
    (d W : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    {c₀ C₀ A J K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hA : 0 ≤ A) (hc : |Real.log c₀| ≤ A * dimensionLogScale d)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ) (q : ExteriorDegree (d + 1))
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hν : AtomTransferControl ν J K) :
    max (paperProjectiveCoefficientLogLoss d c₀ q + J * (d + 1 : ℝ) * dimensionLogScale d)
      (∫ ω, Real.log ‖literalPaperExteriorCell profile center z q ω‖
        ∂literalPaperExteriorCellMeasure d ν) ≤
      atomTransferConstant A J K z * ((W : ℝ) * Real.log (Real.exp 1 * (W : ℝ))) := by
  have hJ := hν.fresh_constant_nonneg
  have hK := hν.atom_constant_nonneg
  have hH := (zero_le_one.trans (one_le_dimensionLogScale d))
  have hD : (0 : ℝ) ≤ d + 1 := by positivity
  have hcoef := paperProjectiveCoefficientLogLoss_le_logarithmic d c₀ A hc₀ hA hc q
  have hfresh := literal_fresh_mean_le_of_atom_log d ν profile hc₀ center hcenter z q hν.logarithmic
  let S := A + J + 3 * ‖z‖ + 7
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hraw : max
      (paperProjectiveCoefficientLogLoss d c₀ q + J * (d + 1 : ℝ) * dimensionLogScale d)
      (∫ ω, Real.log ‖literalPaperExteriorCell profile center z q ω‖
        ∂literalPaperExteriorCellMeasure d ν) ≤ S * (d + 1 : ℝ) * dimensionLogScale d := by
    apply max_le
    · have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show A + 4 + J ≤ S by dsimp [S]; linarith [norm_nonneg z]) hD) hH
      nlinarith only [hcoef, h]
    · have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (show 3 * ‖z‖ + 3 ≤ S by dsimp [S]; linarith) hD) hH
      nlinarith only [hfresh, h]
  have hlog := dimensionLogScale_le_logEW d W hW hd
  have hd' : (d : ℝ) + 1 = 2 * (W : ℝ) := by exact_mod_cast hd
  have hlog0 : 0 ≤ Real.log (Real.exp 1 * (W : ℝ)) := by
    linarith [one_le_dimensionLogScale d]
  have hscaled := mul_le_mul_of_nonneg_left hlog (mul_nonneg hS hD)
  have hconst : 6 * S ≤ atomTransferConstant A J K z := by
    unfold atomTransferConstant S
    linarith [norm_nonneg z]
  apply hraw.trans
  calc
    _ ≤ 6 * S * ((W : ℝ) * Real.log (Real.exp 1 * (W : ℝ))) := by
      rw [hd'] at hscaled ⊢
      nlinarith only [hscaled]
    _ ≤ _ := mul_le_mul_of_nonneg_right hconst (mul_nonneg (Nat.cast_nonneg _) hlog0)

theorem literal_physical_telescope_uniform_atom
    (ell cellCount d W : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    {c₀ C₀ A J K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hA : 0 ≤ A) (hc : |Real.log c₀| ≤ A * dimensionLogScale d)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ) (q : ExteriorDegree (d + 1))
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hν : AtomTransferControl ν J K) :
    let base := literalOpenMeanPressure d ell ν profile center z q
    let error := atomTransferConstant A J K z * ((W : ℝ) * Real.log (Real.exp 1 * (W : ℝ)))
    (cellCount : ℝ) * (base - error) ≤
        literalOpenMeanPressure d (cellCount * ((d + 1) + ell)) ν profile center z q ∧
      literalOpenMeanPressure d (cellCount * ((d + 1) + ell)) ν profile center z q ≤
        (cellCount : ℝ) * (base + error) := by
  have ht := literal_physical_telescope_of_atom_log ell cellCount d profile hc₀
    center hcenter z q ν hν.logarithmic _ (hν.projective d c₀ C₀ profile hc₀ center z q)
  have he := literal_cell_error_le_atomTransferConstant d W hW hd profile hc₀ hA hc
    center hcenter z q ν hν
  exact ⟨(mul_le_mul_of_nonneg_left (sub_le_sub_left he _) (Nat.cast_nonneg cellCount)).trans ht.1,
    ht.2.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl he) (Nat.cast_nonneg cellCount))⟩

theorem literal_row_increment_uniform_atom
    (d W n : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    {c₀ C₀ A J K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hA : 0 ≤ A) (hc : |Real.log c₀| ≤ A * dimensionLogScale d)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ) (q : ExteriorDegree (d + 1))
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hν : AtomTransferControl ν J K) :
    |literalOpenMeanPressure d (n + 1) ν profile center z q -
        literalOpenMeanPressure d n ν profile center z q| ≤
      atomTransferConstant A J K z * Real.log (Real.exp 1 * (W : ℝ)) := by
  have hJ := hν.fresh_constant_nonneg
  have hK := hν.atom_constant_nonneg
  have hrow := literal_open_mean_pressure_succ_of_atom_log d n profile hc₀ center hcenter z q ν
    hν.logarithmic
  have hcost := literalAtomRowCostBound_le_logarithmic d profile hc₀ A K hA hK hc z
  have hlog := dimensionLogScale_le_logEW d W hW hd
  have hlog0 : 0 ≤ Real.log (Real.exp 1 * (W : ℝ)) := by
    linarith [one_le_dimensionLogScale d]
  have hconst : 3 * (6 * ‖z‖ + 7 + A + 2 * K) ≤ atomTransferConstant A J K z := by
    unfold atomTransferConstant
    linarith [norm_nonneg z]
  apply (hrow.trans hcost).trans
  calc
    _ ≤ (6 * ‖z‖ + 7 + A + 2 * K) *
        (3 * Real.log (Real.exp 1 * (W : ℝ))) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ _ := by
      nlinarith only [mul_le_mul_of_nonneg_right hconst hlog0]

end CircularLawSections56.Section5
