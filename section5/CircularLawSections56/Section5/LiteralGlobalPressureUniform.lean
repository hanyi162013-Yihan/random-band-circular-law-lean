import CircularLawSections56.Section5.LiteralUniformMesoscopic

/-! # Global actual pressure, uniformly in every positive cell count

The common error bound is independent of `q`. Uniform mesoscopic calibration
therefore gives the manuscript's two-parameter uniform conclusion, not only
convergence along one previously selected balanced cell sequence.
-/

open Filter MeasureTheory Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

theorem literal_max_pressure_lift_uniform
    (d W m q : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    (hm : d + 1 ≤ m) (hq : 0 < q)
    {c₀ C₀ A J K : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hA : 0 ≤ A) (hc : |Real.log c₀| ≤ A * dimensionLogScale d)
    (center : Fin (d + 1)) (hcenter : center ≠ 0) (z : ℂ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hν : AtomTransferControl ν J K) :
    |finiteSignedMax Finset.univ Finset.univ_nonempty
        (fun r => literalOpenMeanPressure d (q * m) ν profile center z r) / ((q * m : ℕ) : ℝ) -
      finiteSignedMax Finset.univ Finset.univ_nonempty
        (fun r => literalOpenMeanPressure d (m - (d + 1)) ν profile center z r) / (m : ℝ)| ≤
      atomTransferConstant A J K z * ((W : ℝ) * Real.log (Real.exp 1 * (W : ℝ))) / (m : ℝ) := by
  have hmp : 0 < m := lt_of_lt_of_le (Nat.succ_pos d) hm
  have hlen : d + 1 + (m - (d + 1)) = m := Nat.add_sub_of_le hm
  simp only [Nat.cast_mul]
  apply max_pressure_lift Finset.univ_nonempty _ _ q m _ hq hmp
  intro r _
  simpa only [hlen] using literal_physical_telescope_uniform_atom (m - (d + 1)) q d W
    hW hd profile hc₀ hA hc center hcenter z r ν hν

theorem eventually_mesoscopic_reserve_fits
    (W : ℕ → ℕ) (δ : ℝ) (hδ : 0 < δ) (hW : Tendsto W atTop atTop) :
    ∀ᶠ n in atTop, 2 * W n ≤ paperMesoscopicCellLength δ W n := by
  have hWr : Tendsto (fun n => (W n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hW
  have hlarge := ((tendsto_rpow_atTop hδ).comp hWr).eventually_ge_atTop 2
  filter_upwards [hlarge, hW.eventually_ge_atTop 1] with n hn hpos
  change 2 ≤ (W n : ℝ) ^ δ at hn
  have hw : 0 < (W n : ℝ) := Nat.cast_pos.2 (by omega)
  have hmul := mul_le_mul_of_nonneg_left hn hw.le
  have hpow : (W n : ℝ) ^ (1 + δ) = (W n : ℝ) * (W n : ℝ) ^ δ := by
    rw [Real.rpow_add hw, Real.rpow_one]
  have hceil : (W n : ℝ) ^ (1 + δ) ≤ (paperMesoscopicCellLength δ W n : ℝ) := Nat.le_ceil _
  rw [hpow] at hceil
  have hbound : (2 : ℝ) * W n ≤ (paperMesoscopicCellLength δ W n : ℝ) := by
    linarith only [hmul, hceil]
  exact_mod_cast hbound

theorem literal_global_pressure_uniform_in_cells
    (d W : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (δ A J K target : ℝ) (z : ℂ)
    (hδ : 0 < δ) (hA : 0 ≤ A) (hJ : 0 ≤ J) (hK : 0 ≤ K)
    (hW : Tendsto W atTop atTop) (hWpos : ∀ n, 0 < W n)
    (hd : ∀ n, d n + 1 = 2 * W n) (hc₀ : ∀ n, 0 < c₀ n)
    (hProfile : ∀ n, |Real.log (c₀ n)| ≤ A * dimensionLogScale (d n))
    (hcenter : ∀ n, center n ≠ 0) (hAtom : ∀ n, AtomTransferControl (ν n) J K)
    (hCalibration : Tendsto (fun n => finiteSignedMax
      (Finset.Icc (paperMesoscopicCellLength δ W n) (2 * paperMesoscopicCellLength δ W n))
      (mesoscopic_interval_nonempty _)
      (fun m => |literalMesoscopicMean d ν profile center z n m - target|)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ q m : ℕ, 0 < q →
      paperMesoscopicCellLength δ W n ≤ m → m ≤ 2 * paperMesoscopicCellLength δ W n →
      |finiteSignedMax Finset.univ Finset.univ_nonempty
        (fun r => literalOpenMeanPressure (d n) (q * m) (ν n) (profile n) (center n) z r) /
          ((q * m : ℕ) : ℝ) - target| < ε := by
  let C := atomTransferConstant A J K z
  let S := fun n => finiteSignedMax
    (Finset.Icc (paperMesoscopicCellLength δ W n) (2 * paperMesoscopicCellLength δ W n))
    (mesoscopic_interval_nonempty _)
    (fun m => |literalMesoscopicMean d ν profile center z n m - target|)
  have hC : 0 ≤ C := atomTransferConstant_nonneg A J K z hA hJ hK
  have hRate : Tendsto (fun n => C * paperCalibrationSeamRate δ W n) atTop (𝓝 0) := by
    simpa only [paperCalibrationSeamRate, mul_zero] using
      (paperCellErrorScale_div_mesoscopicLength_tendsto_zero δ W hδ hW).const_mul C
  have hError : Tendsto (fun n => S n + C * paperCalibrationSeamRate δ W n) atTop (𝓝 0) := by
    simpa only [add_zero] using hCalibration.add hRate
  intro ε hε
  filter_upwards [eventually_mesoscopic_reserve_fits W δ hδ hW,
    (tendsto_order.1 hError).2 ε hε] with n hwidth hsmall q m hq hmLower hmUpper
  have hm₀ : 0 < paperMesoscopicCellLength δ W n :=
    paperMesoscopicCellLength_pos_of_bandwidth_pos δ W n (hWpos n)
  have hm : 0 < m := hm₀.trans_le hmLower
  have hdm : d n + 1 ≤ m := (hd n).trans_le (hwidth.trans hmLower)
  have hlift := literal_max_pressure_lift_uniform (d n) (W n) m q (hWpos n) (hd n)
    hdm hq (profile n) (hc₀ n) hA (hProfile n) (center n) (hcenter n) z (ν n) (hAtom n)
  have hbase : |literalMesoscopicMean d ν profile center z n m - target| ≤ S n :=
    le_finiteSignedMax (mesoscopic_interval_nonempty _)
      (fun m => |literalMesoscopicMean d ν profile center z n m - target|)
      (Finset.mem_Icc.2 ⟨hmLower, hmUpper⟩)
  have hlog : 0 ≤ paperLogEW W n :=
    zero_le_one.trans (one_le_paperLogEW_of_bandwidth_pos W n (hWpos n))
  have hden := div_le_div_of_nonneg_left
    (mul_nonneg hC (mul_nonneg (Nat.cast_nonneg (W n)) hlog))
    (Nat.cast_pos.2 hm₀) (Nat.cast_le.2 hmLower)
  have hrate : C * ((W n : ℝ) * Real.log (Real.exp 1 * (W n : ℝ))) / (m : ℝ) ≤
      C * paperCalibrationSeamRate δ W n := by
    simpa only [paperCalibrationSeamRate, paperCellErrorScale, paperLogEW, mul_div_assoc] using hden
  have htriangle := abs_sub_le
    (finiteSignedMax Finset.univ Finset.univ_nonempty
      (fun r => literalOpenMeanPressure (d n) (q * m) (ν n) (profile n) (center n) z r) /
        ((q * m : ℕ) : ℝ)) (literalMesoscopicMean d ν profile center z n m) target
  change |(_ : ℝ) - literalMesoscopicMean d ν profile center z n m| ≤ _ at hlift
  linarith only [htriangle, hlift, hbase, hrate, hsmall]

end CircularLawSections56.Section5
