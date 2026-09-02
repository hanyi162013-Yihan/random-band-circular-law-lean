import CircularLawSections56.Section5.Section4CompletedInverse

/-!
# Closure relative to the completed finite Section 4 estimates

This entry point accepts finite, unnormalized Section 4 estimates.  It proves
all normalization, balanced geometry, maximum/remainder, inactive-branch and
asymptotic receiver fields.  Section 3 is the separate known calibration input.
The physical cell and row hypotheses below have constructors in the literal
cell and inverse modules; they are not new convergence hypotheses.
-/

open scoped BigOperators ENNReal MeasureTheory
open Filter MeasureTheory Topology

noncomputable section

namespace CircularLawSections56.Section5

universe u v
variable {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
variable {ι : ℕ → Type v} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]

/-- The two completed Section 4 estimates at a physical length.  No normalized
rate, pressure limit, or Section 5 conclusion is included in this contract. -/
structure CompletedSection4PressureInput
    (μ : ∀ n, Measure (Ω n)) (active : ℕ → Bool)
    (raw : ∀ n, Ω n → ℝ) (Y : ∀ n, ι n → Ω n → ℝ)
    (scale W : ℕ → ℕ) (C : ℝ) : Prop where
  seam_integrable : ∀ n, active n = true →
    Integrable (fun ω => |raw n ω - randomFiniteSignedMaxTri Y n ω|) (μ n)
  seam_bound : ∀ n, active n = true →
    (∫ ω, |raw n ω - randomFiniteSignedMaxTri Y n ω| ∂μ n) ≤ C * paperCellErrorScale W n
  pressure_memLp : ∀ n, active n = true → ∀ r, MemLp (Y n r) 2 (μ n)
  pressure_bound : ∀ n, active n = true →
    (∫ ω, CircularLawSection4.maxCenteredAbs (μ n) (Y n) ω ∂μ n) ≤
      C * Real.sqrt ((W n : ℝ) * (scale n : ℝ)) * paperLogEW W n

theorem sqrt_mul_eq_scale_mul_sqrt_div (w s : ℝ) (hw : 0 ≤ w) (hs : 0 < s) :
    Real.sqrt (w * s) = s * Real.sqrt (w / s) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hs.le (Real.sqrt_nonneg _))).1
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hw hs.le), Real.sq_sqrt (div_nonneg hw hs.le)]
  field_simp [hs.ne']

theorem calibration_sqrt_rate_le (δ : ℝ) (W m : ℕ → ℕ) (n : ℕ)
    (hW : 0 < W n) (hm : paperMesoscopicCellLength δ W n ≤ m n) :
    Real.sqrt ((W n : ℝ) / (m n : ℝ)) * paperLogEW W n ≤
      paperCalibrationPressureRate δ W n := by
  have hw : 0 < (W n : ℝ) := Nat.cast_pos.2 hW
  have hp : 0 < (W n : ℝ) ^ (1 + δ) := Real.rpow_pos_of_pos hw _
  have hceil : (W n : ℝ) ^ (1 + δ) ≤ (m n : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.2 hm)
  have hlog : 0 ≤ paperLogEW W n :=
    zero_le_one.trans (one_le_paperLogEW_of_bandwidth_pos W n hW)
  calc
    _ ≤ Real.sqrt ((W n : ℝ) / (W n : ℝ) ^ (1 + δ)) * paperLogEW W n :=
      mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hw.le hp hceil)) hlog
    _ = paperCalibrationPressureRate δ W n := by
      have hquot : (W n : ℝ) / (W n : ℝ) ^ (1 + δ) = (W n : ℝ) ^ (-δ) := by
        calc
          _ = (W n : ℝ) ^ 1 / (W n : ℝ) ^ (1 + δ) := by rw [Real.rpow_one]
          _ = (W n : ℝ) ^ (1 - (1 + δ)) := (Real.rpow_sub hw _ _).symm
          _ = _ := by congr 1; ring
      rw [hquot, Real.sqrt_eq_rpow, ← Real.rpow_mul hw.le]
      rw [show (-δ) * (1 / 2 : ℝ) = -(δ / 2) by ring, Real.rpow_neg hw.le]
      unfold paperCalibrationPressureRate
      ring

/-- Finite input ledger.  Balanced sizes and endpoint identifications are
deterministic bookkeeping.  `cells` is the already proved physical IID cell
telescope; `row_increment` follows from the completed Section 4 inverse bound.
Unlike the old receiver, this contains no normalized remainder or rate limits. -/
structure CompletedSection4LongBranchData
    (μ : ∀ n, Measure (Ω n)) (active : ℕ → Bool)
    (calibrationRaw finalRaw : ∀ n, Ω n → ℝ)
    (calibrationY finalY : ∀ n, ι n → Ω n → ℝ)
    (lifted : ∀ n, ι n → ℝ) (q m N W : ℕ → ℕ) (δ C : ℝ) where
  constant_nonneg : 0 ≤ C
  bandwidth_pos : ∀ n, active n = true → 0 < W n
  base_length_pos : ∀ n, active n = true → 0 < paperMesoscopicCellLength δ W n
  reserve : ∀ n, active n = true → 2 * W n ≤ N n
  fit : ∀ n, active n = true → 2 * paperMesoscopicCellLength δ W n ≤ N n - 2 * W n
  count_eq : ∀ n, active n = true →
    q n = balancedCellCount (N n - 2 * W n) (paperMesoscopicCellLength δ W n)
  length_eq : ∀ n, active n = true →
    m n = balancedCellLength (N n - 2 * W n) (paperMesoscopicCellLength δ W n)
  calibration : CompletedSection4PressureInput μ active calibrationRaw calibrationY m W C
  final : CompletedSection4PressureInput μ active finalRaw finalY N W C
  cells : ∀ n, active n = true → ∀ r,
    (q n : ℝ) * (literalCoordinateMeanPressure μ calibrationY n r - C * paperCellErrorScale W n) ≤
      lifted n r ∧ lifted n r ≤
        (q n : ℝ) * (literalCoordinateMeanPressure μ calibrationY n r + C * paperCellErrorScale W n)
  terminalPressure : ∀ n, ι n → ℕ → ℝ
  terminal_start : ∀ n, active n = true → ∀ r, terminalPressure n r 0 = lifted n r
  terminal_end : ∀ n, active n = true → ∀ r,
    terminalPressure n r (balancedCellRemainder (N n - 2 * W n)
      (paperMesoscopicCellLength δ W n)) = literalCoordinateMeanPressure μ finalY n r
  row_increment : ∀ n, active n = true → ∀ r,
    ∀ j < balancedCellRemainder (N n - 2 * W n) (paperMesoscopicCellLength δ W n),
      |terminalPressure n r (j + 1) - terminalPressure n r j| ≤ C * paperLogEW W n

/-- Every original physical receiver field is now constructed from the finite
ledger.  In particular the normalized inverse-row remainder is not supplied. -/
theorem CompletedSection4LongBranchData.toPhysical
    {μ : ∀ n, Measure (Ω n)} {active : ℕ → Bool}
    {calibrationRaw finalRaw : ∀ n, Ω n → ℝ}
    {calibrationY finalY : ∀ n, ι n → Ω n → ℝ}
    {lifted : ∀ n, ι n → ℝ} {q m N W : ℕ → ℕ} {δ C : ℝ}
    (h : CompletedSection4LongBranchData μ active calibrationRaw finalRaw
      calibrationY finalY lifted q m N W δ C) :
    PaperPhysicalLiteralLongBranchInputTri μ active calibrationRaw finalRaw calibrationY finalY
      lifted q m N (fun n => C * paperCellErrorScale W n)
      (fun n => balancedPhysicalLengthRatio (N n) (W n) (paperMesoscopicCellLength δ W n))
      δ W C C C C C C := by
  have hgeom := fun n hn => balanced_physical_division_spec (N n) (W n)
    (paperMesoscopicCellLength δ W n) (h.bandwidth_pos n hn) (h.base_length_pos n hn)
    (h.reserve n hn) (h.fit n hn)
  have hm : ∀ n, active n = true → paperMesoscopicCellLength δ W n ≤ m n := by
    intro n hn
    rw [h.length_eq n hn]
    exact (hgeom n hn).2.1
  have hmp : ∀ n, active n = true → 0 < m n :=
    fun n hn => (h.base_length_pos n hn).trans_le (hm n hn)
  have hNp : ∀ n, active n = true → 0 < N n := by
    intro n hn
    have := h.bandwidth_pos n hn
    have := h.reserve n hn
    omega
  have hlog : ∀ n, active n = true → 0 ≤ paperLogEW W n :=
    fun n hn => zero_le_one.trans (one_le_paperLogEW_of_bandwidth_pos W n (h.bandwidth_pos n hn))
  refine
    { calibration_scale_pos := hmp
      final_scale_pos := hNp
      calibration_seam_integrable := h.calibration.seam_integrable
      calibration_seam_bound := ?_
      calibration_pressure_memLp := h.calibration.pressure_memLp
      calibration_pressure_bound := ?_
      final_seam_integrable := h.final.seam_integrable
      final_seam_bound := ?_
      final_pressure_memLp := h.final.pressure_memLp
      final_pressure_bound := ?_
      cell_scale := Filter.Eventually.of_forall ?_
      cell_bounds := h.cells
      cell_length_lower := Filter.Eventually.of_forall hm
      cell_error_nonneg := Filter.Eventually.of_forall ?_
      cell_error_bound := Filter.Eventually.of_forall (fun _ _ => le_rfl)
      ratio_nonneg := fun n hn => (hgeom n hn).2.2.1
      ratio_le_one := fun n hn => (hgeom n hn).2.2.2.1
      inverse_row_remainder := ?_
      length_ratio_bound := ?_ }
  · intro n hn
    have hscale : 0 ≤ C * paperCellErrorScale W n :=
      mul_nonneg h.constant_nonneg (mul_nonneg (Nat.cast_nonneg _) (hlog n hn))
    have hd := div_le_div_of_nonneg_left hscale
      (Nat.cast_pos.2 (h.base_length_pos n hn)) (Nat.cast_le.2 (hm n hn))
    have hb := (div_le_div_of_nonneg_right (h.calibration.seam_bound n hn)
      (Nat.cast_nonneg (m n))).trans hd
    have hh := (div_le_iff₀ (Nat.cast_pos.2 (hmp n hn))).1 hb
    simpa only [paperCalibrationSeamRate, mul_div_assoc, mul_comm] using hh
  · intro n hn
    have hb := mul_le_mul_of_nonneg_left
      (calibration_sqrt_rate_le δ W m n (h.bandwidth_pos n hn) (hm n hn))
      (mul_nonneg (Nat.cast_nonneg (m n)) h.constant_nonneg)
    have heq := sqrt_mul_eq_scale_mul_sqrt_div (W n : ℝ) (m n : ℝ)
      (Nat.cast_nonneg _) (Nat.cast_pos.2 (hmp n hn))
    have hi := h.calibration.pressure_bound n hn
    rw [heq] at hi
    nlinarith only [hi, hb]
  · intro n hn
    have hx : 0 ≤ C * Real.sqrt ((W n : ℝ) / (N n : ℝ)) * paperLogEW W n :=
      mul_nonneg (mul_nonneg h.constant_nonneg (Real.sqrt_nonneg _)) (hlog n hn)
    have heq : (N n : ℝ) * (C * paperFinalSeamRate W N n) =
        C * paperCellErrorScale W n +
          (N n : ℝ) * (C * Real.sqrt ((W n : ℝ) / (N n : ℝ)) * paperLogEW W n) := by
      unfold paperFinalSeamRate
      field_simp [Nat.cast_ne_zero.mpr (hNp n hn).ne']
    rw [heq]
    exact (h.final.seam_bound n hn).trans (le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) hx))
  · intro n hn
    have hscale : 0 ≤ C * paperCellErrorScale W n :=
      mul_nonneg h.constant_nonneg (mul_nonneg (Nat.cast_nonneg _) (hlog n hn))
    have hi := h.final.pressure_bound n hn
    rw [sqrt_mul_eq_scale_mul_sqrt_div _ _ (Nat.cast_nonneg _)
      (Nat.cast_pos.2 (hNp n hn))] at hi
    have heq : (N n : ℝ) * (C * paperFinalSeamRate W N n) =
        C * paperCellErrorScale W n +
          C * ((N n : ℝ) * Real.sqrt ((W n : ℝ) / (N n : ℝ))) * paperLogEW W n := by
      unfold paperFinalSeamRate
      field_simp [Nat.cast_ne_zero.mpr (hNp n hn).ne']
    rw [heq]
    linarith
  · intro n hn
    exact ⟨by rw [h.count_eq n hn]; exact (hgeom n hn).1, hmp n hn⟩
  · intro n hn
    exact mul_nonneg h.constant_nonneg (mul_nonneg (Nat.cast_nonneg _) (hlog n hn))
  · intro n hn
    have hr := balanced_pressure_remainder_of_row_increments δ W N n
      (h.bandwidth_pos n hn) (h.base_length_pos n hn) (h.reserve n hn) (h.fit n hn)
      (h.terminalPressure n) C h.constant_nonneg (h.row_increment n hn)
    simp only [h.terminal_start n hn, h.terminal_end n hn] at hr
    simpa only [coordinateMeanFiniteSignedMaxTri, literalLiftedPressureMaximum,
      literalCoordinateMeanPressure, cellNormalizedPressureVarying,
      scalarPressureDegrees, scalarPressureFamily, finiteSignedMax, Finset.sup'_singleton,
      h.count_eq n hn, h.length_eq n hn, Nat.cast_mul] using hr
  · intro n hn
    exact balanced_physical_lengthRatio_error_le_paperRate δ W N n
      (h.bandwidth_pos n hn) (h.base_length_pos n hn) (h.reserve n hn) (h.fit n hn)

/-- Conditional end-to-end Section 5 certificate with Section 4 and Section 3
explicitly designated as preinputs, and every rate limit proved internally. -/
def completedSection4_literalCertificate
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (shortBranch : ℕ → Bool) (shortLogPotential : ∀ n, Ω n → ℝ)
    (calibrationRaw finalRaw : ∀ n, Ω n → ℝ)
    (calibrationY finalY : ∀ n, ι n → Ω n → ℝ)
    (lifted : ∀ n, ι n → ℝ) (q m N W : ℕ → ℕ) (target δ γ C : ℝ)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8)
    (hW : Tendsto W atTop atTop)
    (hLong : ∀ᶠ n in atTop, literalLongActive shortBranch n = true →
      (W n : ℝ) ^ (1 + γ) < (N n : ℝ))
    (h4 : CompletedSection4LongBranchData μ (literalLongActive shortBranch)
      calibrationRaw finalRaw calibrationY finalY lifted q m N W δ C)
    (h3 : Section3IndicatorAnchorsTri μ shortLogPotential
      (literalActiveNormalizedObservable (literalLongActive shortBranch) calibrationRaw m target) target) :
    LiteralFinalClosureCertificateTri μ
      (literalActiveNormalizedObservable (literalLongActive shortBranch) finalRaw N target)
      (literalActiveNormalizedMeanPressure μ (literalLongActive shortBranch) finalY N target) target :=
  literalNearEndToEndCertificate μ shortBranch shortLogPotential calibrationRaw finalRaw
    calibrationY finalY lifted q m N W (fun n => C * paperCellErrorScale W n)
    (fun n => balancedPhysicalLengthRatio (N n) (W n) (paperMesoscopicCellLength δ W n))
    target δ γ C C C C C C hδ hδγ hγ hW hLong h4.toPhysical h3

end CircularLawSections56.Section5
