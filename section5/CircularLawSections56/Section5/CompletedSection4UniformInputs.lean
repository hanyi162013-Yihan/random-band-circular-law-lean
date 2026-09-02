import CircularLawSections56.Section5.Section4CompletedAssembly
import CircularLawSections56.Section5.LiteralPhysicalPressureFluctuation

/-! # A single constant for all finite inputs of the completed Section 4 receiver -/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

def completedLiteralConstant (c₀ L : ℝ) (z : ℂ) : ℝ :=
  uniformLiteralConstant c₀ L z + Real.sqrt (6 * uniformLiteralConstant c₀ L z) +
    uniformInverseRowConstant c₀ L z

theorem completedLiteralConstant_bounds (c₀ L : ℝ) (z : ℂ) :
    0 ≤ completedLiteralConstant c₀ L z ∧
    uniformLiteralConstant c₀ L z ≤ completedLiteralConstant c₀ L z ∧
    Real.sqrt (6 * uniformLiteralConstant c₀ L z) ≤ completedLiteralConstant c₀ L z ∧
    uniformInverseRowConstant c₀ L z ≤ completedLiteralConstant c₀ L z := by
  have hu := (uniformLiteralConstant_pos c₀ L z).le
  have hr := uniformInverseRowConstant_nonneg c₀ L z
  have hs := Real.sqrt_nonneg (6 * uniformLiteralConstant c₀ L z)
  unfold completedLiteralConstant
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Convert the literal Section 4 fiber-variance expression into the common
unnormalized pressure bound.  The outside length is only required to be at
most the physical scale; it is never identified with the full cell length. -/
theorem literal_fluctuation_le_completed_constant
    (d W ell scale : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W) (hell : ell ≤ scale)
    (c₀ L : ℝ) (z : ℂ) (hc₀ : 0 < c₀) :
    Real.sqrt ((d + 2 : ℝ) * 2 * (ell : ℝ) * complexPaperPressureFiberL2Bound d c₀ L z) ≤
      completedLiteralConstant c₀ L z * Real.sqrt ((W : ℝ) * (scale : ℝ)) *
        Real.log (Real.exp 1 * (W : ℝ)) := by
  let U := uniformLiteralConstant c₀ L z
  let H := Real.log (Real.exp 1 * (W : ℝ))
  have hU : 0 ≤ U := (uniformLiteralConstant_pos c₀ L z).le
  have hH : 0 ≤ H := by
    have ha := dimensionLogScale_le_logEW d W hW hd
    have hb := one_le_dimensionLogScale d
    dsimp only [H]
    linarith
  have hd' : (d : ℝ) + 1 = 2 * (W : ℝ) := by exact_mod_cast hd
  have hw : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hdim : (d + 2 : ℝ) * 2 ≤ 6 * (W : ℝ) := by linarith
  have hlength : ((d + 2 : ℝ) * 2) * (ell : ℝ) ≤ 6 * (W : ℝ) * (scale : ℝ) :=
    mul_le_mul hdim (Nat.cast_le.2 hell) (Nat.cast_nonneg _) (by positivity)
  have hraw : (d + 2 : ℝ) * 2 * (ell : ℝ) * complexPaperPressureFiberL2Bound d c₀ L z ≤
      (6 * U) * ((W : ℝ) * (scale : ℝ)) * H ^ 2 := by
    calc
      _ ≤ ((d + 2 : ℝ) * 2 * (ell : ℝ)) * (U * H ^ 2) :=
        mul_le_mul_of_nonneg_left (fiberSquare_le_uniform_logEW d W hW hd c₀ L z hc₀)
          (by positivity)
      _ ≤ (6 * (W : ℝ) * (scale : ℝ)) * (U * H ^ 2) :=
        mul_le_mul_of_nonneg_right hlength (mul_nonneg hU (sq_nonneg _))
      _ = _ := by ring
  calc
    _ ≤ Real.sqrt ((6 * U) * ((W : ℝ) * (scale : ℝ)) * H ^ 2) := Real.sqrt_le_sqrt hraw
    _ = Real.sqrt (6 * U) * Real.sqrt ((W : ℝ) * (scale : ℝ)) * H := by
      rw [Real.sqrt_mul (mul_nonneg (by positivity) (by positivity)),
        Real.sqrt_mul (by positivity), Real.sqrt_sq hH]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (completedLiteralConstant_bounds c₀ L z).2.2.1
        (Real.sqrt_nonneg _)) hH

/-- Exact literal seam and fluctuation estimates assemble the named completed
Section 4 pressure contract with the same constant used by the cells and rows. -/
theorem completedSection4PressureInput_of_literal_bounds
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (active : ℕ → Bool) (d ell scale W : ℕ → ℕ)
    (raw : ∀ n, Ω n → ℝ) (Y : ∀ n, ExteriorDegree (d n + 1) → Ω n → ℝ)
    (c₀ L : ℝ) (z : ℂ) (hc₀ : 0 < c₀)
    (hW : ∀ n, active n = true → 0 < W n)
    (hd : ∀ n, active n = true → d n + 1 = 2 * W n)
    (hell : ∀ n, active n = true → ell n ≤ scale n)
    (hSeamInt : ∀ n, active n = true →
      Integrable (fun ω => |raw n ω - randomFiniteSignedMaxTri Y n ω|) (μ n))
    (hSeam : ∀ n, active n = true →
      (∫ ω, |raw n ω - randomFiniteSignedMaxTri Y n ω| ∂μ n) ≤
        paperIsolatedCoefficientLoss (d n) c₀ + complexFreshNegativeBound (d n) L +
          paperFreshPositiveBound (d n) z)
    (hLp : ∀ n, active n = true → ∀ r, MemLp (Y n r) 2 (μ n))
    (hFluct : ∀ n, active n = true →
      (∫ ω, maxCenteredAbs (μ n) (Y n) ω ∂μ n) ≤
        Real.sqrt ((d n + 2 : ℝ) * 2 * (ell n : ℝ) * complexPaperPressureFiberL2Bound (d n) c₀ L z)) :
    CompletedSection4PressureInput μ active raw Y scale W (completedLiteralConstant c₀ L z) where
  seam_integrable := hSeamInt
  seam_bound := by
    intro n hn
    have hlog : 0 ≤ paperLogEW W n := zero_le_one.trans
      (one_le_paperLogEW_of_bandwidth_pos W n (hW n hn))
    apply (hSeam n hn).trans ((rawSeamLoss_le_uniform_logEW (d n) (W n)
      (hW n hn) (hd n hn) c₀ L z hc₀).trans ?_)
    exact mul_le_mul_of_nonneg_right (completedLiteralConstant_bounds c₀ L z).2.1
      (mul_nonneg (Nat.cast_nonneg _) hlog)
  pressure_memLp := hLp
  pressure_bound := fun n hn => (hFluct n hn).trans
    (literal_fluctuation_le_completed_constant (d n) (W n) (ell n) (scale n)
      (hW n hn) (hd n hn) (hell n hn) c₀ L z hc₀)

/-- The `cells` field of the completed receiver is obtained from the actual
physical IID telescope, with its fresh mean bound discharged here. -/
theorem completedLiteral_physical_cell_bounds
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) (active : ℕ → Bool) (d ell q W : ℕ → ℕ)
    {c₀ C₀ : ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) c₀ C₀)
    (center : ∀ n, Fin (d n + 1)) (z : ℂ) (L : ℝ)
    (f : ℕ → ℂ → ℝ≥0∞) [∀ n, IsProbabilityMeasure (volume.withDensity (f n))]
    (restriction : ∀ n, Ω n → LiteralPhysicalOutsideRows (ell n) (d n))
    (calibrationY : ∀ n, ExteriorDegree (d n + 1) → Ω n → ℝ)
    (hRestriction : ∀ n, active n = true → MeasurePreserving (restriction n) (μ n)
      (paperIndicatorOpenRowSampleMeasure (ell n) (d n) (volume.withDensity (f n))))
    (hCalibration : ∀ n, active n = true → ∀ r,
      calibrationY n r =ᵐ[μ n]
        literalPhysicalCalibrationPressureSequence d ell profile center (fun _ => z) restriction n r)
    (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (hW : ∀ n, active n = true → 0 < W n)
    (hd : ∀ n, active n = true → d n + 1 = 2 * W n)
    (hsqrt : ∀ n, active n = true → Real.sqrt (c₀ / (d n + 2 : ℝ)) ≤ 1)
    (hcenter : ∀ n, active n = true → center n ≠ 0)
    (hf : ∀ n, active n = true → ∀ᵐ w ∂(volume : Measure ℂ), f n w ≤ ENNReal.ofReal L)
    (hInt : ∀ n, active n = true → Integrable (fun u : ℂ => ‖u‖ ^ 2) (volume.withDensity (f n)))
    (hSecond : ∀ n, active n = true → (∫ u : ℂ, ‖u‖ ^ 2 ∂volume.withDensity (f n)) ≤ 1) :
    ∀ n, active n = true → ∀ r,
      (q n : ℝ) * (literalCoordinateMeanPressure μ calibrationY n r -
          completedLiteralConstant c₀ L z * paperCellErrorScale W n) ≤
        literalPhysicalLiftedMeanSequence d ell q (fun n => volume.withDensity (f n))
          profile center (fun _ => z) n r ∧
      literalPhysicalLiftedMeanSequence d ell q (fun n => volume.withDensity (f n))
          profile center (fun _ => z) n r ≤
        (q n : ℝ) * (literalCoordinateMeanPressure μ calibrationY n r +
          completedLiteralConstant c₀ L z * paperCellErrorScale W n) := by
  apply complex_literalPhysicalPressureSequence_cell_bounds μ active d ell q profile center
    (fun _ => z) f (fun _ => L) (fun n => completedLiteralConstant c₀ L z * paperCellErrorScale W n)
    restriction calibrationY hRestriction hCalibration (fun _ _ => hc₀) hsqrt hcenter
    (fun _ _ => hL) hf hInt hSecond
  intro n hn r
  have hb := literalPhysicalCellError_le_uniform_logEW (d n) (W n) (hW n hn) (hd n hn)
    (volume.withDensity (f n)) (profile n) hc₀ (hsqrt n hn) hL
    (complexBallBound_withDensity (hf n hn)) (center n) z r (hInt n hn) (hSecond n hn)
  have hlog : 0 ≤ paperLogEW W n := zero_le_one.trans
    (one_le_paperLogEW_of_bandwidth_pos W n (hW n hn))
  exact hb.trans (mul_le_mul_of_nonneg_right (completedLiteralConstant_bounds c₀ L z).2.1
    (mul_nonneg (Nat.cast_nonneg _) hlog))

/-- Actual terminal matrix products provide `row_increment` in the receiver.
Only the pathwise multiplication identity and the completed Section 4 inverse
bound enter; the caller supplies no expected pressure-increment estimate. -/
theorem completedLiteral_terminal_matrix_increments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d W steps : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hL : 0 ≤ L) (hν : ComplexBallBound ν (ENNReal.ofReal L))
    (center : Fin (d + 1)) (z : ℂ) (r : ExteriorDegree (d + 1))
    (rows : ℕ → Ω → PaperIndicatorAtomRow d)
    (P : ℕ → Ω → Matrix (ExteriorIndex (d + 1) r) (ExteriorIndex (d + 1) r) ℂ)
    (hRows : ∀ j < steps, Measurable (rows j))
    (hMarginal : ∀ j < steps, ∀ s, MeasurePreserving (fun ω => rows j ω s) μ ν)
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1)
    (hUnit : ∀ j < steps, ∀ᵐ ω ∂μ,
      IsUnit (profile.paperIndicatorOpenExteriorRow center z r (rows j ω)))
    (hBase : ∀ j < steps, ∀ᵐ ω ∂μ, P j ω ≠ 0)
    (hInverse : ∀ j < steps, Section4ComplementaryInverseInput μ d profile center z r (rows j))
    (hProduct : ∀ j < steps, ∀ᵐ ω ∂μ,
      P (j + 1) ω = profile.paperIndicatorOpenExteriorRow center z r (rows j ω) * P j ω)
    (hPressureInt : ∀ j ≤ steps, Integrable (fun ω => Real.log ‖P j ω‖) μ) :
    ∀ j < steps,
      |(∫ ω, Real.log ‖P (j + 1) ω‖ ∂μ) - (∫ ω, Real.log ‖P j ω‖ ∂μ)| ≤
        completedLiteralConstant c₀ L z * Real.log (Real.exp 1 * (W : ℝ)) := by
  intro j hj
  have heq : (fun ω => Real.log ‖P (j + 1) ω‖) =ᵐ[μ]
      (fun ω => Real.log ‖profile.paperIndicatorOpenExteriorRow center z r (rows j ω) * P j ω‖) :=
    (hProduct j hj).mono (fun _ hω => congrArg (fun A => Real.log ‖A‖) hω)
  have hi := (hPressureInt (j + 1) (by omega)).congr heq
  rw [integral_congr_ae heq]
  apply (literal_row_pressure_increment_of_section4_inverse μ d W hW hd ν profile hc₀ hL hν
    center z r (rows j) (hRows j hj) (hMarginal j hj) hInt hSecond (P j)
    (hUnit j hj) (hBase j hj) (hInverse j hj) hi (hPressureInt j (by omega))).trans
  have ha := dimensionLogScale_le_logEW d W hW hd
  have hb := one_le_dimensionLogScale d
  exact mul_le_mul_of_nonneg_right (completedLiteralConstant_bounds c₀ L z).2.2.2 (by linarith)

end CircularLawSections56.Section5
