import CircularLawSection4.IIDFiberOuterIntegrable
import CircularLawSection4.UnboundedRawContinuousMemLp
import CircularLawSection4.PaperIndicatorFlatConcentration

/-!
# Assumption-free concentration for the paper pressure

The basic unbounded Efron--Stein API exposes two technical hypotheses:
outer integrability of each raw replacement energy and global `L²` membership
of the observable.  For the paper's pressure both follow from the already
proved uniform one-row fiber estimate.  This module closes those hypotheses
and records the resulting row-wise and flat-random-matrix statements.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace PaperIndicatorWeights

variable {m n : ℕ} {c₀ C₀ : ℝ}

/-- The outer Bochner-integrability premise for a complex row replacement
is forced by the uniform one-row `L²` pressure estimate. -/
theorem complex_paperIndicatorOpenPressure_rawOuter_integrable
    {L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1)) (i : Fin (n + 1))
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    Integrable (fun rows => ∫ a,
      (profile.paperIndicatorOpenPressure center z q rows -
        profile.paperIndicatorOpenPressure center z q
          (Function.update rows i a)) ^ 2 ∂paperIndicatorRowMeasure m ν)
      (paperIndicatorOpenRowSampleMeasure (n + 1) m ν) := by
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
  apply iidRawResamplingOuter_integrable_of_fiber_memLp
    μ f
    (profile.measurable_paperIndicatorOpenPressure center z q (n + 1))
    i fiberCenter
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

/-- Real-input counterpart of
`complex_paperIndicatorOpenPressure_rawOuter_integrable`. -/
theorem real_paperIndicatorOpenPressure_rawOuter_integrable
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
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    Integrable (fun rows => ∫ a,
      (profile.paperIndicatorOpenPressureOfReal center z q rows -
        profile.paperIndicatorOpenPressureOfReal center z q
          (Function.update rows i a)) ^ 2
        ∂paperIndicatorRealRowMeasure m ν)
      (paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν) := by
  let μ := paperIndicatorRealRowMeasure m ν
  letI : IsProbabilityMeasure μ := iidMeasure_isProbability ν (m + 2)
  let f : (Fin (n + 1) → PaperIndicatorRealAtomRow m) → ℝ :=
    profile.paperIndicatorOpenPressureOfReal center z q
  let fiberCenter : (Fin n → PaperIndicatorRealAtomRow m) → ℝ := fun y =>
    Real.log (profile.paperPressureRowScaleOfReal center z q
      (i.insertNth (0 : PaperIndicatorRealAtomRow m) y) i)
  apply iidRawResamplingOuter_integrable_of_fiber_memLp
    μ f
    (profile.measurable_paperIndicatorOpenPressureOfReal center z q (n + 1))
    i fiberCenter
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

/-- The complex one-row raw resampling energy bound with its outer
integrability premise discharged by the uniform fiber `L²` estimate. -/
theorem complex_paperIndicatorOpenPressure_rawResamplingEnergy_le_auto
    {L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1)) (i : Fin (n + 1))
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    iidRawResamplingEnergy (paperIndicatorRowMeasure m ν)
        (profile.paperIndicatorOpenPressure center z q) i ≤
      4 * complexPaperPressureFiberL2Bound m c₀ L z := by
  apply profile.complex_paperIndicatorOpenPressure_rawResamplingEnergy_le
    ν hν hL hc₀ hsqrt center z q i hνInt hνSecond
  exact profile.complex_paperIndicatorOpenPressure_rawOuter_integrable
    ν hν hL hc₀ hsqrt center z q i hνInt hνSecond

/-- The real-input one-row raw resampling energy bound with its outer
integrability premise discharged by the uniform fiber `L²` estimate. -/
theorem real_paperIndicatorOpenPressure_rawResamplingEnergy_le_auto
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
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    iidRawResamplingEnergy (paperIndicatorRealRowMeasure m ν)
        (profile.paperIndicatorOpenPressureOfReal center z q) i ≤
      4 * realPaperPressureFiberL2Bound m c₀ L z theta := by
  apply profile.real_paperIndicatorOpenPressure_rawResamplingEnergy_le
    ν hν hL hc₀ hsqrt center z q i hνInt hνSecond
      theta htheta0 htheta1
  exact profile.real_paperIndicatorOpenPressure_rawOuter_integrable
    ν hν hL hc₀ hsqrt center z q i hνInt hνSecond
      theta htheta0 htheta1

/-- The complex paper pressure is globally square-integrable on the complete
IID row sample.  This is derived from finite row-replacement energy rather
than assumed as an Efron--Stein premise. -/
theorem complex_paperIndicatorOpenPressure_memLp_two
    {L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    MemLp (profile.paperIndicatorOpenPressure center z q) 2
      (paperIndicatorOpenRowSampleMeasure (n + 1) m ν) := by
  let μ := paperIndicatorRowMeasure m ν
  letI : IsProbabilityMeasure μ := iidMeasure_isProbability ν (m + 2)
  let f : (Fin (n + 1) → PaperIndicatorAtomRow m) → ℝ :=
    profile.paperIndicatorOpenPressure center z q
  have hf : Measurable f :=
    profile.measurable_paperIndicatorOpenPressure center z q (n + 1)
  apply memLp_two_of_iid_raw_replacement_integrable μ f hf
  · intro i rows
    simpa only [f, μ] using
      profile.complex_paperIndicatorOpenPressure_replacement_sq_integrable
        ν hν hL hc₀ hsqrt center z q rows i hνInt hνSecond
  · intro i
    simpa only [f, μ, paperIndicatorOpenRowSampleMeasure] using
      profile.complex_paperIndicatorOpenPressure_rawOuter_integrable
        ν hν hL hc₀ hsqrt center z q i hνInt hνSecond

/-- Real-input counterpart of
`complex_paperIndicatorOpenPressure_memLp_two`. -/
theorem real_paperIndicatorOpenPressure_memLp_two
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
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    MemLp (profile.paperIndicatorOpenPressureOfReal center z q) 2
      (paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν) := by
  let μ := paperIndicatorRealRowMeasure m ν
  letI : IsProbabilityMeasure μ := iidMeasure_isProbability ν (m + 2)
  let f : (Fin (n + 1) → PaperIndicatorRealAtomRow m) → ℝ :=
    profile.paperIndicatorOpenPressureOfReal center z q
  have hf : Measurable f :=
    profile.measurable_paperIndicatorOpenPressureOfReal center z q (n + 1)
  apply memLp_two_of_iid_raw_replacement_integrable μ f hf
  · intro i rows
    simpa only [f, μ] using
      profile.real_paperIndicatorOpenPressure_replacement_sq_integrable
        ν hν hL hc₀ hsqrt center z q rows i hνInt hνSecond
          theta htheta0 htheta1
  · intro i
    simpa only [f, μ, paperIndicatorRealOpenRowSampleMeasure] using
      profile.real_paperIndicatorOpenPressure_rawOuter_integrable
        ν hν hL hc₀ hsqrt center z q i hνInt hνSecond
          theta htheta0 htheta1

/-- Variance bound for one exterior pressure of the actual complex
indicator random matrix, with both technical Efron--Stein premises derived
from the paper's distributional hypotheses. -/
theorem variance_complex_paperIndicatorOpenPressure_le_auto
    {L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    variance (profile.paperIndicatorOpenPressure center z q)
        (paperIndicatorOpenRowSampleMeasure (n + 1) m ν) ≤
      2 * (n + 1 : ℝ) * complexPaperPressureFiberL2Bound m c₀ L z := by
  apply profile.variance_complex_paperIndicatorOpenPressure_le
    ν hν hL hc₀ hsqrt center z q hνInt hνSecond
  · exact profile.complex_paperIndicatorOpenPressure_memLp_two
      ν hν hL hc₀ hsqrt center z q hνInt hνSecond
  · intro i
    exact profile.complex_paperIndicatorOpenPressure_rawOuter_integrable
      ν hν hL hc₀ hsqrt center z q i hνInt hνSecond

/-- Real-input counterpart of
`variance_complex_paperIndicatorOpenPressure_le_auto`. -/
theorem variance_real_paperIndicatorOpenPressure_le_auto
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
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    variance (profile.paperIndicatorOpenPressureOfReal center z q)
        (paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν) ≤
      2 * (n + 1 : ℝ) *
        realPaperPressureFiberL2Bound m c₀ L z theta := by
  apply profile.variance_real_paperIndicatorOpenPressure_le
    ν hν hL hc₀ hsqrt center z q hνInt hνSecond theta htheta0 htheta1
  · exact profile.real_paperIndicatorOpenPressure_memLp_two
      ν hν hL hc₀ hsqrt center z q hνInt hνSecond theta htheta0 htheta1
  · intro i
    exact profile.real_paperIndicatorOpenPressure_rawOuter_integrable
      ν hν hL hc₀ hsqrt center z q i hνInt hνSecond
        theta htheta0 htheta1

/-- Expected maximal centered complex pressure over every exterior degree,
with all Efron--Stein analytic premises discharged. -/
theorem integral_max_complex_paperIndicatorOpenPressure_le_auto
    {L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    let Y : ExteriorDegree (m + 1) →
        (Fin (n + 1) → PaperIndicatorAtomRow m) → ℝ := fun q =>
      profile.paperIndicatorOpenPressure center z q
    (∫ rows, maxCenteredAbs
        (paperIndicatorOpenRowSampleMeasure (n + 1) m ν) Y rows
      ∂paperIndicatorOpenRowSampleMeasure (n + 1) m ν) ≤
      Real.sqrt ((m + 2 : ℝ) *
        (2 * (n + 1 : ℝ) * complexPaperPressureFiberL2Bound m c₀ L z)) := by
  apply profile.integral_max_complex_paperIndicatorOpenPressure_le
    ν hν hL hc₀ hsqrt center z hνInt hνSecond
  · intro q
    exact profile.complex_paperIndicatorOpenPressure_memLp_two
      ν hν hL hc₀ hsqrt center z q hνInt hνSecond
  · intro q i
    exact profile.complex_paperIndicatorOpenPressure_rawOuter_integrable
      ν hν hL hc₀ hsqrt center z q i hνInt hνSecond

/-- Real-input counterpart of
`integral_max_complex_paperIndicatorOpenPressure_le_auto`. -/
theorem integral_max_real_paperIndicatorOpenPressure_le_auto
    {L : ℝ}
    (ν : Measure ℝ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (hνInt : Integrable (fun u : ℝ => u ^ 2) ν)
    (hνSecond : ∫ u : ℝ, u ^ 2 ∂ν = 1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    let Y : ExteriorDegree (m + 1) →
        (Fin (n + 1) → PaperIndicatorRealAtomRow m) → ℝ := fun q =>
      profile.paperIndicatorOpenPressureOfReal center z q
    (∫ rows, maxCenteredAbs
        (paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν) Y rows
      ∂paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν) ≤
      Real.sqrt ((m + 2 : ℝ) *
        (2 * (n + 1 : ℝ) *
          realPaperPressureFiberL2Bound m c₀ L z theta)) := by
  apply profile.integral_max_real_paperIndicatorOpenPressure_le
    ν hν hL hc₀ hsqrt center z hνInt hνSecond theta htheta0 htheta1
  · intro q
    exact profile.real_paperIndicatorOpenPressure_memLp_two
      ν hν hL hc₀ hsqrt center z q hνInt hνSecond theta htheta0 htheta1
  · intro q i
    exact profile.real_paperIndicatorOpenPressure_rawOuter_integrable
      ν hν hL hc₀ hsqrt center z q i hνInt hνSecond
        theta htheta0 htheta1

/-- Flat-coordinate complex pressure variance with no separately assumed
global `L²` or outer-integrability premise. -/
theorem variance_complex_paperIndicatorFlatOpenPressure_le_auto
    {L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    variance (profile.paperIndicatorFlatOpenPressure center z q)
        (paperIndicatorSampleMeasure (n + 1) m ν) ≤
      2 * (n + 1 : ℝ) * complexPaperPressureFiberL2Bound m c₀ L z := by
  apply profile.variance_complex_paperIndicatorFlatOpenPressure_le
    ν hν hL hc₀ hsqrt center z q hνInt hνSecond
  · exact profile.complex_paperIndicatorOpenPressure_memLp_two
      ν hν hL hc₀ hsqrt center z q hνInt hνSecond
  · intro i
    exact profile.complex_paperIndicatorOpenPressure_rawOuter_integrable
      ν hν hL hc₀ hsqrt center z q i hνInt hνSecond

/-- Flat-coordinate real pressure counterpart of
`variance_complex_paperIndicatorFlatOpenPressure_le_auto`. -/
theorem variance_real_paperIndicatorFlatOpenPressure_le_auto
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
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    variance (profile.paperIndicatorRealFlatOpenPressure center z q)
        (paperIndicatorRealSampleMeasure (n + 1) m ν) ≤
      2 * (n + 1 : ℝ) *
        realPaperPressureFiberL2Bound m c₀ L z theta := by
  apply profile.variance_real_paperIndicatorFlatOpenPressure_le
    ν hν hL hc₀ hsqrt center z q hνInt hνSecond theta htheta0 htheta1
  · exact profile.real_paperIndicatorOpenPressure_memLp_two
      ν hν hL hc₀ hsqrt center z q hνInt hνSecond theta htheta0 htheta1
  · intro i
    exact profile.real_paperIndicatorOpenPressure_rawOuter_integrable
      ν hν hL hc₀ hsqrt center z q i hνInt hνSecond
        theta htheta0 htheta1

/-- Flat-coordinate expected maximal complex pressure, with both technical
premises supplied automatically. -/
theorem integral_max_complex_paperIndicatorFlatOpenPressure_le_auto
    {L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    (∫ ω, maxCenteredAbs
        (paperIndicatorSampleMeasure (n + 1) m ν)
        (fun q => profile.paperIndicatorFlatOpenPressure center z q) ω
      ∂paperIndicatorSampleMeasure (n + 1) m ν) ≤
      Real.sqrt ((m + 2 : ℝ) *
        (2 * (n + 1 : ℝ) * complexPaperPressureFiberL2Bound m c₀ L z)) := by
  apply profile.integral_max_complex_paperIndicatorFlatOpenPressure_le
    ν hν hL hc₀ hsqrt center z hνInt hνSecond
  · intro q
    exact profile.complex_paperIndicatorOpenPressure_memLp_two
      ν hν hL hc₀ hsqrt center z q hνInt hνSecond
  · intro q i
    exact profile.complex_paperIndicatorOpenPressure_rawOuter_integrable
      ν hν hL hc₀ hsqrt center z q i hνInt hνSecond

/-- Flat-coordinate real counterpart of
`integral_max_complex_paperIndicatorFlatOpenPressure_le_auto`. -/
theorem integral_max_real_paperIndicatorFlatOpenPressure_le_auto
    {L : ℝ}
    (ν : Measure ℝ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (hνInt : Integrable (fun u : ℝ => u ^ 2) ν)
    (hνSecond : ∫ u : ℝ, u ^ 2 ∂ν = 1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (∫ ω, maxCenteredAbs
        (paperIndicatorRealSampleMeasure (n + 1) m ν)
        (fun q => profile.paperIndicatorRealFlatOpenPressure center z q) ω
      ∂paperIndicatorRealSampleMeasure (n + 1) m ν) ≤
      Real.sqrt ((m + 2 : ℝ) *
        (2 * (n + 1 : ℝ) *
          realPaperPressureFiberL2Bound m c₀ L z theta)) := by
  apply profile.integral_max_real_paperIndicatorFlatOpenPressure_le
    ν hν hL hc₀ hsqrt center z hνInt hνSecond theta htheta0 htheta1
  · intro q
    exact profile.real_paperIndicatorOpenPressure_memLp_two
      ν hν hL hc₀ hsqrt center z q hνInt hνSecond theta htheta0 htheta1
  · intro q i
    exact profile.real_paperIndicatorOpenPressure_rawOuter_integrable
      ν hν hL hc₀ hsqrt center z q i hνInt hνSecond
        theta htheta0 htheta1

end PaperIndicatorWeights

end CircularLawSection4
