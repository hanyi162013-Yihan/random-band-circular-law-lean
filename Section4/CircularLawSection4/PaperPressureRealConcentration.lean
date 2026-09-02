import CircularLawSection4.PaperPressureRealL2
import CircularLawSection4.PaperPressureMeasurable
import CircularLawSection4.IIDFiberMemLpResampling
import CircularLawSection4.UnboundedRawContinuousEfronStein

/-!
# Real-input concentration for the paper's random open pressure

This module applies the real-row fiber logarithmic estimate to the literal
IID row sample of the indicator random matrix.  The transfer matrices remain
complex because the spectral parameter is complex; only the underlying atoms
and their product law are real.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace PaperIndicatorWeights

variable {m n : ℕ} {c₀ C₀ : ℝ}

noncomputable instance paperIndicatorRealRowMeasure_sFinite
    (m : ℕ) (ν : Measure ℝ) [SFinite ν] [IsProbabilityMeasure ν] :
    SFinite (paperIndicatorRealRowMeasure m ν) := by
  letI : IsProbabilityMeasure (paperIndicatorRealRowMeasure m ν) :=
    iidMeasure_isProbability ν (m + 2)
  infer_instance

/-- IID law of all complete real rows in the paper's open sample. -/
def paperIndicatorRealOpenRowSampleMeasure
    (n m : ℕ) (ν : Measure ℝ) [SFinite ν]
    [IsProbabilityMeasure ν] :
    Measure (Fin n → PaperIndicatorRealAtomRow m) :=
  let μ := paperIndicatorRealRowMeasure m ν
  letI : IsProbabilityMeasure μ := iidMeasure_isProbability ν (m + 2)
  iidMeasure μ n

/-- The real-input pressure is measurable on the literal row sample. -/
theorem measurable_paperIndicatorComplexifyRealRows (n m : ℕ) :
    Measurable (paperIndicatorComplexifyRealRows :
      (Fin n → PaperIndicatorRealAtomRow m) →
        Fin n → PaperIndicatorAtomRow m) := by
  unfold paperIndicatorComplexifyRealRows paperIndicatorComplexifyRealRow
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact Complex.measurable_ofReal.comp
    ((measurable_pi_apply j).comp (measurable_pi_apply i))

theorem measurable_paperIndicatorOpenPressureOfReal
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1)) (n : ℕ) :
    Measurable (fun rows : Fin n → PaperIndicatorRealAtomRow m =>
      profile.paperIndicatorOpenPressureOfReal center z q rows) := by
  unfold paperIndicatorOpenPressureOfReal
  exact (profile.measurable_paperIndicatorOpenPressure center z q n).comp
    (measurable_paperIndicatorComplexifyRealRows n m)

/-- The explicit one-row `L²` constant in the real bounded-density branch
of the paper. -/
def realPaperPressureFiberL2Bound
    (m : ℕ) (c₀ L : ℝ) (z : ℂ) (theta : ℝ) : ℝ :=
  2 * oneSidedLogSecondMomentBound
      ((4 * L) /
        (theta * Real.sqrt (c₀ / (m + 2 : ℝ)))) 1 +
    2 * (3 * (Real.log (m + 2 : ℝ)) ^ 2 + 3 + 3 * ‖z‖ ^ 2)

/-- For a fixed outside sample, replacing one literal real matrix row has a
square-integrable pressure difference. -/
theorem real_paperIndicatorOpenPressure_replacement_sq_integrable
    {L : ℝ}
    (ν : Measure ℝ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin (n + 1) → PaperIndicatorRealAtomRow m) (i : Fin (n + 1))
    (hνInt : Integrable (fun u : ℝ => u ^ 2) ν)
    (hνSecond : ∫ u : ℝ, u ^ 2 ∂ν = 1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    Integrable (fun a : PaperIndicatorRealAtomRow m =>
      (profile.paperIndicatorOpenPressureOfReal center z q rows -
        profile.paperIndicatorOpenPressureOfReal center z q
          (Function.update rows i a)) ^ 2)
      (paperIndicatorRealRowMeasure m ν) := by
  let μ := paperIndicatorRealRowMeasure m ν
  letI : IsProbabilityMeasure μ := iidMeasure_isProbability ν (m + 2)
  let scale := profile.paperPressureRowScaleOfReal center z q rows i
  let g : PaperIndicatorRealAtomRow m → ℝ := fun a =>
    profile.paperIndicatorOpenPressureOfReal center z q
      (Function.update rows i a)
  have hfiber :=
    profile.real_paperIndicatorOpenPressure_fiber_memLp_two_and_integral_sq_all_scales
      ν hν hL hc₀ hsqrt center z q rows i hνInt hνSecond
        theta htheta0 htheta1
  have hgMeas : Measurable g := by
    dsimp only [g]
    exact (profile.measurable_paperIndicatorOpenPressureOfReal
      center z q (n + 1)).comp (by fun_prop)
  have herr : MemLp (fun a => g a - Real.log scale) 2 μ := by
    apply (memLp_norm_iff
      ((hgMeas.sub_const (Real.log scale)).aestronglyMeasurable)).mp
    simpa only [μ, g, scale, Real.norm_eq_abs] using hfiber.1
  have hdiff : MemLp (fun a =>
      (profile.paperIndicatorOpenPressureOfReal center z q rows -
          Real.log scale) - (g a - Real.log scale)) 2 μ :=
    (memLp_const
      (profile.paperIndicatorOpenPressureOfReal center z q rows -
        Real.log scale)).sub herr
  have hint := hdiff.integrable_sq
  convert hint using 1
  funext a
  dsimp only [g]
  ring

/-- The raw Efron--Stein energy of replacing any one complete real row of
the actual indicator matrix is at most four times the real paper row-fiber
constant. -/
theorem real_paperIndicatorOpenPressure_rawResamplingEnergy_le
    {L : ℝ}
    (ν : Measure ℝ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1)) (i : Fin (n + 1))
    (hνInt : Integrable (fun u : ℝ => u ^ 2) ν)
    (hνSecond : ∫ u : ℝ, u ^ 2 ∂ν = 1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hrawOuter : Integrable (fun rows => ∫ a,
      (profile.paperIndicatorOpenPressureOfReal center z q rows -
        profile.paperIndicatorOpenPressureOfReal center z q
          (Function.update rows i a)) ^ 2 ∂paperIndicatorRealRowMeasure m ν)
      (paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν)) :
    iidRawResamplingEnergy (paperIndicatorRealRowMeasure m ν)
        (profile.paperIndicatorOpenPressureOfReal center z q) i ≤
      4 * realPaperPressureFiberL2Bound m c₀ L z theta := by
  let μ := paperIndicatorRealRowMeasure m ν
  letI : IsProbabilityMeasure μ := iidMeasure_isProbability ν (m + 2)
  let f : (Fin (n + 1) → PaperIndicatorRealAtomRow m) → ℝ :=
    profile.paperIndicatorOpenPressureOfReal center z q
  let fiberCenter : (Fin n → PaperIndicatorRealAtomRow m) → ℝ := fun y =>
    Real.log (profile.paperPressureRowScaleOfReal center z q
      (i.insertNth (0 : PaperIndicatorRealAtomRow m) y) i)
  apply iidRawResamplingEnergy_le_four_mul_of_fiber_memLp
    μ f i fiberCenter
  · simpa only [μ, f, paperIndicatorRealOpenRowSampleMeasure] using hrawOuter
  · intro y
    let rows₀ : Fin (n + 1) → PaperIndicatorRealAtomRow m :=
      i.insertNth (0 : PaperIndicatorRealAtomRow m) y
    have hfiber :=
      profile.real_paperIndicatorOpenPressure_fiber_memLp_two_and_integral_sq_all_scales
        ν hν hL hc₀ hsqrt center z q rows₀ i hνInt hνSecond
          theta htheta0 htheta1
    have herrMeas : Measurable (fun a : PaperIndicatorRealAtomRow m =>
        f (i.insertNth a y) - fiberCenter y) := by
      simpa only [f, Function.comp_apply] using
        (((profile.measurable_paperIndicatorOpenPressureOfReal
          center z q (n + 1)).comp
            (measurable_fin_insertNth_left (K := PaperIndicatorRealAtomRow m)
              i y)).sub_const (fiberCenter y))
    apply (memLp_norm_iff herrMeas.aestronglyMeasurable).mp
    simpa only [f, fiberCenter, rows₀, Fin.update_insertNth,
      Real.norm_eq_abs] using hfiber.1
  · intro y
    let rows₀ : Fin (n + 1) → PaperIndicatorRealAtomRow m :=
      i.insertNth (0 : PaperIndicatorRealAtomRow m) y
    have hfiber :=
      profile.real_paperIndicatorOpenPressure_fiber_memLp_two_and_integral_sq_all_scales
        ν hν hL hc₀ hsqrt center z q rows₀ i hνInt hνSecond
          theta htheta0 htheta1
    simpa only [f, fiberCenter, rows₀, Fin.update_insertNth, sq_abs,
      realPaperPressureFiberL2Bound] using hfiber.2

/-- Variance bound for one exterior pressure of the actual real indicator
random matrix.  The two remaining hypotheses are the standard global `L²`
and outer-Bochner-integrability assumptions of unbounded Efron--Stein. -/
theorem variance_real_paperIndicatorOpenPressure_le
    {L : ℝ}
    (ν : Measure ℝ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (hνInt : Integrable (fun u : ℝ => u ^ 2) ν)
    (hνSecond : ∫ u : ℝ, u ^ 2 ∂ν = 1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hpressureL2 : MemLp
      (profile.paperIndicatorOpenPressureOfReal center z q) 2
      (paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν))
    (hrawOuter : ∀ i : Fin (n + 1), Integrable (fun rows => ∫ a,
      (profile.paperIndicatorOpenPressureOfReal center z q rows -
        profile.paperIndicatorOpenPressureOfReal center z q
          (Function.update rows i a)) ^ 2 ∂paperIndicatorRealRowMeasure m ν)
      (paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν)) :
    variance (profile.paperIndicatorOpenPressureOfReal center z q)
        (paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν) ≤
      2 * (n + 1 : ℝ) *
        realPaperPressureFiberL2Bound m c₀ L z theta := by
  let μ := paperIndicatorRealRowMeasure m ν
  letI : IsProbabilityMeasure μ := iidMeasure_isProbability ν (m + 2)
  let f : (Fin (n + 1) → PaperIndicatorRealAtomRow m) → ℝ :=
    profile.paperIndicatorOpenPressureOfReal center z q
  have hmeas : Measurable f :=
    profile.measurable_paperIndicatorOpenPressureOfReal center z q (n + 1)
  have hES := variance_iidMeasure_le_half_sum_raw_memLp μ f hmeas
    (by simpa only [f, μ, paperIndicatorRealOpenRowSampleMeasure] using hpressureL2)
    (fun i rows => by
      simpa only [f, μ] using
        profile.real_paperIndicatorOpenPressure_replacement_sq_integrable
          ν hν hL hc₀ hsqrt center z q rows i hνInt hνSecond
            theta htheta0 htheta1)
    (fun i => by
      simpa only [f, μ, paperIndicatorRealOpenRowSampleMeasure] using hrawOuter i)
  calc
    variance (profile.paperIndicatorOpenPressureOfReal center z q)
        (paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν) ≤
        (1 / 2 : ℝ) * ∑ i : Fin (n + 1),
          iidRawResamplingEnergy μ f i := by
      simpa only [f, μ, paperIndicatorRealOpenRowSampleMeasure] using hES
    _ ≤ (1 / 2 : ℝ) * ∑ _i : Fin (n + 1),
          (4 * realPaperPressureFiberL2Bound m c₀ L z theta) := by
      gcongr with i
      exact profile.real_paperIndicatorOpenPressure_rawResamplingEnergy_le
        ν hν hL hc₀ hsqrt center z q i hνInt hνSecond theta
          htheta0 htheta1 (hrawOuter i)
    _ = 2 * (n + 1 : ℝ) *
          realPaperPressureFiberL2Bound m c₀ L z theta := by
      simp
      ring

/-- Expected maximal centered pressure over every exterior degree of the
actual real indicator random matrix. -/
theorem integral_max_real_paperIndicatorOpenPressure_le
    {L : ℝ}
    (ν : Measure ℝ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (hνInt : Integrable (fun u : ℝ => u ^ 2) ν)
    (hνSecond : ∫ u : ℝ, u ^ 2 ∂ν = 1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hpressureL2 : ∀ q : ExteriorDegree (m + 1), MemLp
      (profile.paperIndicatorOpenPressureOfReal center z q) 2
      (paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν))
    (hrawOuter : ∀ (q : ExteriorDegree (m + 1)) (i : Fin (n + 1)),
      Integrable (fun rows => ∫ a,
        (profile.paperIndicatorOpenPressureOfReal center z q rows -
          profile.paperIndicatorOpenPressureOfReal center z q
            (Function.update rows i a)) ^ 2
          ∂paperIndicatorRealRowMeasure m ν)
        (paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν)) :
    let Y : ExteriorDegree (m + 1) →
        (Fin (n + 1) → PaperIndicatorRealAtomRow m) → ℝ := fun q =>
      profile.paperIndicatorOpenPressureOfReal center z q
    (∫ rows, maxCenteredAbs
        (paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν) Y rows
      ∂paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν) ≤
      Real.sqrt ((m + 2 : ℝ) *
        (2 * (n + 1 : ℝ) *
          realPaperPressureFiberL2Bound m c₀ L z theta)) := by
  dsimp only
  let μrow := paperIndicatorRealRowMeasure m ν
  letI : IsProbabilityMeasure μrow := iidMeasure_isProbability ν (m + 2)
  let μrows := iidMeasure μrow (n + 1)
  letI : IsProbabilityMeasure μrows := iidMeasure_isProbability μrow (n + 1)
  let Y : ExteriorDegree (m + 1) →
      (Fin (n + 1) → PaperIndicatorRealAtomRow m) → ℝ := fun q =>
    profile.paperIndicatorOpenPressureOfReal center z q
  have hmax := integral_maxCenteredAbs_le_sqrt_card_mul
    (μ := μrows)
    (Y := Y)
    (fun q => by
      simpa only [Y, μrows, μrow,
        paperIndicatorRealOpenRowSampleMeasure] using hpressureL2 q)
    (fun q => by
      simpa only [Y, μrows, μrow,
        paperIndicatorRealOpenRowSampleMeasure] using
        profile.variance_real_paperIndicatorOpenPressure_le
          ν hν hL hc₀ hsqrt center z q hνInt hνSecond theta
            htheta0 htheta1 (hpressureL2 q) (hrawOuter q))
  simpa only [Y, μrows, μrow, paperIndicatorRealOpenRowSampleMeasure] using
    (show (∫ ω, maxCenteredAbs μrows Y ω ∂μrows) ≤
        Real.sqrt ((m + 2 : ℝ) *
          (2 * (n + 1 : ℝ) *
            realPaperPressureFiberL2Bound m c₀ L z theta)) by
      convert hmax using 1
      congr 2
      simp only [ExteriorDegree, Fintype.card_fin]
      push_cast
      ring)

end PaperIndicatorWeights

end CircularLawSection4
