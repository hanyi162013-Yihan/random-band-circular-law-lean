import CircularLawSection4.PaperPressureComplexL2
import CircularLawSection4.PaperPressureMeasurable
import CircularLawSection4.IIDFiberMemLpResampling
import CircularLawSection4.UnboundedRawContinuousEfronStein

/-!
# Complex-input concentration for the paper's random open pressure

This module applies the row-fiber logarithmic estimate to the literal IID
row sample of the indicator random matrix.  It gives the raw replacement
energy of one matrix row, the variance of one exterior pressure, and the
expected maximum over all exterior degrees.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace PaperIndicatorWeights

variable {m n : ℕ} {c₀ C₀ : ℝ}

noncomputable instance paperIndicatorRowMeasure_sFinite
    (m : ℕ) (ν : Measure ℂ) [SFinite ν] [IsProbabilityMeasure ν] :
    SFinite (paperIndicatorRowMeasure m ν) := by
  letI : IsProbabilityMeasure (iidMeasure ν (m + 2)) :=
    iidMeasure_isProbability ν (m + 2)
  unfold paperIndicatorRowMeasure
  infer_instance

/-- The explicit one-row `L²` constant in the complex bounded-density
branch of the paper. -/
def complexPaperPressureFiberL2Bound (m : ℕ) (c₀ L : ℝ) (z : ℂ) : ℝ :=
  2 * oneSidedLogSecondMomentBound
      ((max 1 (Real.pi * L)) /
        ((1 / 2 : ℝ) * Real.sqrt (c₀ / (m + 2 : ℝ)))) 1 +
    2 * (3 * (Real.log (m + 2 : ℝ)) ^ 2 + 3 * 1 + 3 * ‖z‖ ^ 2)

/-- For a fixed outside sample, replacing one literal matrix row has a
square-integrable pressure difference. -/
theorem complex_paperIndicatorOpenPressure_replacement_sq_integrable
    {L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin (n + 1) → PaperIndicatorAtomRow m) (i : Fin (n + 1))
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    Integrable (fun a : PaperIndicatorAtomRow m =>
      (profile.paperIndicatorOpenPressure center z q rows -
        profile.paperIndicatorOpenPressure center z q
          (Function.update rows i a)) ^ 2)
      (paperIndicatorRowMeasure m ν) := by
  let μ := paperIndicatorRowMeasure m ν
  letI : IsProbabilityMeasure μ := iidMeasure_isProbability ν (m + 2)
  let scale := profile.paperPressureRowScale center q
    (profile.paperPressureLeftHistory center z q rows i)
    (profile.paperPressureRightHistory center z q rows i)
  let g : PaperIndicatorAtomRow m → ℝ := fun a =>
    profile.paperIndicatorOpenPressure center z q (Function.update rows i a)
  have hfiber :=
    profile.complex_paperIndicatorOpenPressure_fiber_memLp_two_and_integral_sq_all_scales
      ν hν hL hc₀ hsqrt center z q rows i hνInt hνSecond
  have hgMeas : Measurable g := by
    dsimp only [g]
    exact (profile.measurable_paperIndicatorOpenPressure center z q (n + 1)).comp
      (by fun_prop)
  have herr : MemLp (fun a => g a - Real.log scale) 2 μ := by
    apply (memLp_norm_iff
      (hgMeas.sub measurable_const).aestronglyMeasurable).mp
    change MemLp (fun a => |g a - Real.log scale|) 2 μ
    simpa only [μ, g, scale] using hfiber.1
  have hdiff : MemLp (fun a =>
      (profile.paperIndicatorOpenPressure center z q rows - Real.log scale) -
        (g a - Real.log scale)) 2 μ :=
    (memLp_const
      (profile.paperIndicatorOpenPressure center z q rows - Real.log scale)).sub herr
  have hint := hdiff.integrable_sq
  convert hint using 1
  funext a
  dsimp only [g]
  ring

/-- The raw Efron--Stein energy of replacing any one complete complex row of
the actual indicator matrix is at most four times the paper row-fiber
constant. -/
theorem complex_paperIndicatorOpenPressure_rawResamplingEnergy_le
    {L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1)) (i : Fin (n + 1))
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1)
    (hrawOuter : Integrable (fun rows => ∫ a,
      (profile.paperIndicatorOpenPressure center z q rows -
        profile.paperIndicatorOpenPressure center z q
          (Function.update rows i a)) ^ 2 ∂paperIndicatorRowMeasure m ν)
      (paperIndicatorOpenRowSampleMeasure (n + 1) m ν)) :
    iidRawResamplingEnergy (paperIndicatorRowMeasure m ν)
        (profile.paperIndicatorOpenPressure center z q) i ≤
      4 * complexPaperPressureFiberL2Bound m c₀ L z := by
  let μ := paperIndicatorRowMeasure m ν
  letI : IsProbabilityMeasure μ := iidMeasure_isProbability ν (m + 2)
  let f : (Fin (n + 1) → PaperIndicatorAtomRow m) → ℝ :=
    profile.paperIndicatorOpenPressure center z q
  let fiberCenter : (Fin n → PaperIndicatorAtomRow m) → ℝ := fun y =>
    Real.log (profile.paperPressureRowScale center q
      (profile.paperPressureLeftHistory center z q
        (i.insertNth (0 : PaperIndicatorAtomRow m) y) i)
      (profile.paperPressureRightHistory center z q
        (i.insertNth (0 : PaperIndicatorAtomRow m) y) i))
  apply iidRawResamplingEnergy_le_four_mul_of_fiber_memLp
    μ f i fiberCenter
  · simpa only [μ, f, paperIndicatorOpenRowSampleMeasure] using hrawOuter
  · intro y
    let rows₀ : Fin (n + 1) → PaperIndicatorAtomRow m :=
      i.insertNth (0 : PaperIndicatorAtomRow m) y
    have hfiber :=
      profile.complex_paperIndicatorOpenPressure_fiber_memLp_two_and_integral_sq_all_scales
        ν hν hL hc₀ hsqrt center z q rows₀ i hνInt hνSecond
    have herrMeas : Measurable (fun a : PaperIndicatorAtomRow m =>
        f (i.insertNth a y) - fiberCenter y) := by
      exact ((profile.measurable_paperIndicatorOpenPressure center z q (n + 1)).comp
        (measurable_fin_insertNth_left i y)).sub_const _
    apply (memLp_norm_iff herrMeas.aestronglyMeasurable).mp
    simpa only [f, fiberCenter, rows₀, Fin.update_insertNth,
      Real.norm_eq_abs] using hfiber.1
  · intro y
    let rows₀ : Fin (n + 1) → PaperIndicatorAtomRow m :=
      i.insertNth (0 : PaperIndicatorAtomRow m) y
    have hfiber :=
      profile.complex_paperIndicatorOpenPressure_fiber_memLp_two_and_integral_sq_all_scales
        ν hν hL hc₀ hsqrt center z q rows₀ i hνInt hνSecond
    simpa only [f, fiberCenter, rows₀, Fin.update_insertNth, sq_abs,
      complexPaperPressureFiberL2Bound] using hfiber.2

/-- Variance bound for one exterior pressure of the actual complex
indicator random matrix.  The two remaining hypotheses are the standard
global `L²` and outer-Bochner-integrability assumptions of the unbounded
Efron--Stein theorem. -/
theorem variance_complex_paperIndicatorOpenPressure_le
    {L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1)
    (hpressureL2 : MemLp
      (profile.paperIndicatorOpenPressure center z q) 2
      (paperIndicatorOpenRowSampleMeasure (n + 1) m ν))
    (hrawOuter : ∀ i : Fin (n + 1), Integrable (fun rows => ∫ a,
      (profile.paperIndicatorOpenPressure center z q rows -
        profile.paperIndicatorOpenPressure center z q
          (Function.update rows i a)) ^ 2 ∂paperIndicatorRowMeasure m ν)
      (paperIndicatorOpenRowSampleMeasure (n + 1) m ν)) :
    variance (profile.paperIndicatorOpenPressure center z q)
        (paperIndicatorOpenRowSampleMeasure (n + 1) m ν) ≤
      2 * (n + 1 : ℝ) * complexPaperPressureFiberL2Bound m c₀ L z := by
  let μ := paperIndicatorRowMeasure m ν
  letI : IsProbabilityMeasure μ := iidMeasure_isProbability ν (m + 2)
  let f : (Fin (n + 1) → PaperIndicatorAtomRow m) → ℝ :=
    profile.paperIndicatorOpenPressure center z q
  have hmeas : Measurable f :=
    profile.measurable_paperIndicatorOpenPressure center z q (n + 1)
  have hES := variance_iidMeasure_le_half_sum_raw_memLp μ f hmeas
    (by simpa only [f, μ, paperIndicatorOpenRowSampleMeasure] using hpressureL2)
    (fun i rows => by
      simpa only [f, μ] using
        profile.complex_paperIndicatorOpenPressure_replacement_sq_integrable
          ν hν hL hc₀ hsqrt center z q rows i hνInt hνSecond)
    (fun i => by
      simpa only [f, μ, paperIndicatorOpenRowSampleMeasure] using hrawOuter i)
  calc
    variance (profile.paperIndicatorOpenPressure center z q)
        (paperIndicatorOpenRowSampleMeasure (n + 1) m ν) ≤
        (1 / 2 : ℝ) * ∑ i : Fin (n + 1),
          iidRawResamplingEnergy μ f i := by
      simpa only [f, μ, paperIndicatorOpenRowSampleMeasure] using hES
    _ ≤ (1 / 2 : ℝ) * ∑ _i : Fin (n + 1),
          (4 * complexPaperPressureFiberL2Bound m c₀ L z) := by
      gcongr with i
      exact profile.complex_paperIndicatorOpenPressure_rawResamplingEnergy_le
        ν hν hL hc₀ hsqrt center z q i hνInt hνSecond
          (hrawOuter i)
    _ = 2 * (n + 1 : ℝ) * complexPaperPressureFiberL2Bound m c₀ L z := by
      simp
      ring

/-- Expected maximal centered pressure over every exterior degree of the
actual complex indicator random matrix. -/
theorem integral_max_complex_paperIndicatorOpenPressure_le
    {L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1)
    (hpressureL2 : ∀ q : ExteriorDegree (m + 1), MemLp
      (profile.paperIndicatorOpenPressure center z q) 2
      (paperIndicatorOpenRowSampleMeasure (n + 1) m ν))
    (hrawOuter : ∀ (q : ExteriorDegree (m + 1)) (i : Fin (n + 1)),
      Integrable (fun rows => ∫ a,
        (profile.paperIndicatorOpenPressure center z q rows -
          profile.paperIndicatorOpenPressure center z q
            (Function.update rows i a)) ^ 2 ∂paperIndicatorRowMeasure m ν)
        (paperIndicatorOpenRowSampleMeasure (n + 1) m ν)) :
    let Y : ExteriorDegree (m + 1) →
        (Fin (n + 1) → PaperIndicatorAtomRow m) → ℝ := fun q =>
      profile.paperIndicatorOpenPressure center z q
    (∫ rows, maxCenteredAbs
        (paperIndicatorOpenRowSampleMeasure (n + 1) m ν) Y rows
      ∂paperIndicatorOpenRowSampleMeasure (n + 1) m ν) ≤
      Real.sqrt ((m + 2 : ℝ) *
        (2 * (n + 1 : ℝ) * complexPaperPressureFiberL2Bound m c₀ L z)) := by
  dsimp only
  let μrow := paperIndicatorRowMeasure m ν
  letI : IsProbabilityMeasure μrow := iidMeasure_isProbability ν (m + 2)
  let μrows := iidMeasure μrow (n + 1)
  letI : IsProbabilityMeasure μrows := iidMeasure_isProbability μrow (n + 1)
  let Y : ExteriorDegree (m + 1) →
      (Fin (n + 1) → PaperIndicatorAtomRow m) → ℝ := fun q =>
    profile.paperIndicatorOpenPressure center z q
  have hmax := integral_maxCenteredAbs_le_sqrt_card_mul
    (μ := μrows)
    (Y := Y)
    (fun q => by
      simpa only [Y, μrows, μrow, paperIndicatorOpenRowSampleMeasure] using
        hpressureL2 q)
    (fun q => by
      simpa only [Y, μrows, μrow, paperIndicatorOpenRowSampleMeasure] using
        profile.variance_complex_paperIndicatorOpenPressure_le
          ν hν hL hc₀ hsqrt center z q hνInt hνSecond
            (hpressureL2 q) (hrawOuter q))
  convert hmax using 1 <;>
    simp only [Y, μrows, μrow, paperIndicatorOpenRowSampleMeasure,
      Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] <;> ring

end PaperIndicatorWeights

end CircularLawSection4
