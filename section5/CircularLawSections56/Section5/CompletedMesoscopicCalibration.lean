import CircularLawSections56.Section5.Section4CompletedAssembly
import CircularLawSections56.Section5.PaperMesoscopicScaleLimits
import CircularLawSections56.Section5.UniformMesoscopicCalibration

/-! # Uniform mesoscopic calibration directly from finite Section 4 estimates

The normalized error rates and finite maximum fluctuation are derived here.
The caller supplies only the accepted short-ring limit for each admissible
length choice and the unnormalized finite Section 4 pressure estimates.
-/

open Filter MeasureTheory Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option autoImplicit false

namespace CircularLawSections56.Section5

universe u v
variable {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
    {ι : ℕ → Type v} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]

theorem paperMesoscopicCellLength_pos_of_bandwidth_pos
    (δ : ℝ) (W : ℕ → ℕ) (n : ℕ) (hW : 0 < W n) :
    0 < paperMesoscopicCellLength δ W n := by
  exact Nat.ceil_pos.2 (Real.rpow_pos_of_pos (Nat.cast_pos.2 hW) _)

theorem completedSection4_mesoscopic_calibration
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (raw : ∀ n, Ω n → ℝ) (Y : ∀ n, ι n → Ω n → ℝ)
    (m W : ℕ → ℕ) (δ C target : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hW : Tendsto W atTop atTop) (hWpos : ∀ n, 0 < W n)
    (hm : ∀ n, paperMesoscopicCellLength δ W n ≤ m n)
    (h4 : CompletedSection4PressureInput μ (fun _ => true) raw Y m W C)
    (h3 : TendstoInProbabilityTri μ (fun n ω => raw n ω / (m n : ℝ)) target) :
    Tendsto (fun n => coordinateMeanFiniteSignedMaxTri μ Y n / (m n : ℝ))
      atTop (𝓝 target) := by
  have hm₀ (n : ℕ) : 0 < paperMesoscopicCellLength δ W n :=
    paperMesoscopicCellLength_pos_of_bandwidth_pos δ W n (hWpos n)
  have hmp (n : ℕ) : 0 < (m n : ℝ) := Nat.cast_pos.2 ((hm₀ n).trans_le (hm n))
  have hlog (n : ℕ) : 0 ≤ paperLogEW W n :=
    zero_le_one.trans (one_le_paperLogEW_of_bandwidth_pos W n (hWpos n))
  apply deterministic_center_tendsto_of_tri_anchor_and_two_L1_seams μ
    (fun n ω => raw n ω / (m n : ℝ))
    (fun n ω => randomFiniteSignedMaxTri Y n ω / (m n : ℝ))
    (fun n => coordinateMeanFiniteSignedMaxTri μ Y n / (m n : ℝ))
    (fun n => C * paperCalibrationSeamRate δ W n)
    (fun n => C * paperCalibrationPressureRate δ W n) target h3
  · intro n
    exact integrable_abs_div_sub_div (μ n) _ _ _ (hmp n) (h4.seam_integrable n rfl)
  · intro n
    apply (integral_abs_div_sub_div_le (μ n) _ _ _ _ (hmp n) (h4.seam_bound n rfl)).trans
    have h := div_le_div_of_nonneg_left
      (mul_nonneg hC (mul_nonneg (Nat.cast_nonneg (W n)) (hlog n)))
      (Nat.cast_pos.2 (hm₀ n)) (Nat.cast_le.2 (hm n))
    simpa only [paperCalibrationSeamRate, paperCellErrorScale, mul_div_assoc] using h
  · intro n
    exact integrable_abs_div_sub_div (μ n) _ _ _ (hmp n)
      (integrable_abs_randomFiniteSignedMax_sub_mean (μ n) (Y n) (h4.pressure_memLp n rfl))
  · intro n
    have hraw := (integral_abs_randomFiniteSignedMax_sub_mean_le_maxCenteredAbs
      (μ n) (Y n) (h4.pressure_memLp n rfl)).trans (h4.pressure_bound n rfl)
    apply (integral_abs_div_sub_div_le (μ n) _ _ _ _ (hmp n) hraw).trans
    rw [sqrt_mul_eq_scale_mul_sqrt_div _ _ (Nat.cast_nonneg _) (hmp n)]
    have he : C * ((m n : ℝ) * Real.sqrt ((W n : ℝ) / m n)) * paperLogEW W n /
        (m n : ℝ) = C * (Real.sqrt ((W n : ℝ) / m n) * paperLogEW W n) := by
      field_simp [(hmp n).ne']
    rw [he]
    exact mul_le_mul_of_nonneg_left (calibration_sqrt_rate_le δ W m n (hWpos n) (hm n)) hC
  · simpa only [mul_zero, paperCalibrationSeamRate] using
      (paperCellErrorScale_div_mesoscopicLength_tendsto_zero δ W hδ hW).const_mul C
  · simpa only [mul_zero, paperCalibrationPressureRate] using
      (paperLogEW_div_rpow_tendsto_zero W hW (half_pos hδ)).const_mul C

theorem completedSection4_uniform_mesoscopic_calibration
    {Ωm : ℕ → ℕ → Type u} [∀ n m, MeasurableSpace (Ωm n m)]
    (μ : ∀ n m, Measure (Ωm n m)) [∀ n m, IsProbabilityMeasure (μ n m)]
    (raw : ∀ n m, Ωm n m → ℝ) (Y : ∀ n m, ι n → Ωm n m → ℝ)
    (W : ℕ → ℕ) (δ C target : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hW : Tendsto W atTop atTop) (hWpos : ∀ n, 0 < W n)
    (h4 : ∀ m : ℕ → ℕ,
      (∀ n, paperMesoscopicCellLength δ W n ≤ m n ∧ m n ≤ 2 * paperMesoscopicCellLength δ W n) →
      CompletedSection4PressureInput (fun n => μ n (m n)) (fun _ => true)
        (fun n => raw n (m n)) (fun n => Y n (m n)) m W C)
    (h3 : ∀ m : ℕ → ℕ,
      (∀ n, paperMesoscopicCellLength δ W n ≤ m n ∧ m n ≤ 2 * paperMesoscopicCellLength δ W n) →
      TendstoInProbabilityTri (fun n => μ n (m n))
        (fun n ω => raw n (m n) ω / (m n : ℝ)) target) :
    Tendsto (fun n => finiteSignedMax
      (Finset.Icc (paperMesoscopicCellLength δ W n) (2 * paperMesoscopicCellLength δ W n))
      (mesoscopic_interval_nonempty _) (fun m =>
        |finiteSignedMax Finset.univ Finset.univ_nonempty
          (fun r => ∫ ω, Y n m r ω ∂μ n m) / (m : ℝ) - target|)) atTop (𝓝 0) := by
  apply mesoscopic_supremum_zero_of_all_length_calibrations (paperMesoscopicCellLength δ W)
    (fun n m => finiteSignedMax Finset.univ Finset.univ_nonempty
      (fun r => ∫ ω, Y n m r ω ∂μ n m) / (m : ℝ)) target
  intro m hm
  exact completedSection4_mesoscopic_calibration (fun n => μ n (m n))
    (fun n => raw n (m n)) (fun n => Y n (m n)) m W δ C target hδ hC hW hWpos
    (fun n => (hm n).1) (h4 m hm) (h3 m hm)

end CircularLawSections56.Section5
