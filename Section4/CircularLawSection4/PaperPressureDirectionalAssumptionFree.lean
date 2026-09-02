import CircularLawSection4.PaperPressureDirectionalConcentration
import CircularLawSection4.IIDFiberOuterIntegrable
import CircularLawSection4.UnboundedRawContinuousMemLp
import CircularLawSection4.PaperIndicatorFlatConcentration

/-!
# Assumption-free directional concentration for the paper pressure

This module discharges the two technical hypotheses left visible in
`PaperPressureDirectionalConcentration`: outer integrability of the raw
row-replacement energy and global square integrability of the pressure.
It then transports the resulting variance and maximal-deviation estimates
to the literal flat atom sample used by the random-matrix definition.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace PaperIndicatorWeights

variable {m n : ℕ} {c₀ C₀ : ℝ}

/-- The outer Bochner-integrability premise for directional complex row
replacement follows from the uniform directional row-fiber `L²` bound. -/
theorem directional_paperIndicatorOpenPressure_rawOuter_integrable
    {L : ℝ} (atom : ProbabilityMeasure ℂ) (phase : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1)) (i : Fin (n + 1))
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (atom : Measure ℂ))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(atom : Measure ℂ) ≤ 1) :
    Integrable (fun rows => ∫ a,
      (profile.paperIndicatorOpenPressure center z q rows -
        profile.paperIndicatorOpenPressure center z q
          (Function.update rows i a)) ^ 2
        ∂paperIndicatorRowMeasure m (atom : Measure ℂ))
      (paperIndicatorOpenRowSampleMeasure
        (n + 1) m (atom : Measure ℂ)) := by
  let μ := paperIndicatorRowMeasure m (atom : Measure ℂ)
  letI : IsProbabilityMeasure μ :=
    iidMeasure_isProbability (atom : Measure ℂ) (m + 2)
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
      profile.directional_paperIndicatorOpenPressure_fiber_absLog_L2_all_scales
        atom phase hdir hL hc₀ hsqrt center z q rows₀ i
          hsecondInt hsecond
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
      profile.directional_paperIndicatorOpenPressure_fiber_absLog_L2_all_scales
        atom phase hdir hL hc₀ hsqrt center z q rows₀ i
          hsecondInt hsecond
    simpa only [f, fiberCenter, rows₀, Fin.update_insertNth, sq_abs,
      directionalPaperPressureFiberL2Bound] using hfiber.2

/-- Directional raw one-row resampling energy with its outer-integrability
premise discharged automatically. -/
theorem directional_paperIndicatorOpenPressure_rawResamplingEnergy_le_auto
    {L : ℝ} (atom : ProbabilityMeasure ℂ) (phase : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1)) (i : Fin (n + 1))
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (atom : Measure ℂ))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(atom : Measure ℂ) ≤ 1) :
    iidRawResamplingEnergy (paperIndicatorRowMeasure m (atom : Measure ℂ))
        (profile.paperIndicatorOpenPressure center z q) i ≤
      4 * directionalPaperPressureFiberL2Bound m c₀ L z := by
  apply profile.directional_paperIndicatorOpenPressure_rawResamplingEnergy_le
    atom phase hdir hL hc₀ hsqrt center z q i hsecondInt hsecond
  exact profile.directional_paperIndicatorOpenPressure_rawOuter_integrable
    atom phase hdir hL hc₀ hsqrt center z q i hsecondInt hsecond

/-- The actual directional paper pressure is globally square-integrable on
the complete IID row sample. -/
theorem directional_paperIndicatorOpenPressure_memLp_two
    {L : ℝ} (atom : ProbabilityMeasure ℂ) (phase : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (atom : Measure ℂ))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(atom : Measure ℂ) ≤ 1) :
    MemLp (profile.paperIndicatorOpenPressure center z q) 2
      (paperIndicatorOpenRowSampleMeasure
        (n + 1) m (atom : Measure ℂ)) := by
  let μ := paperIndicatorRowMeasure m (atom : Measure ℂ)
  letI : IsProbabilityMeasure μ :=
    iidMeasure_isProbability (atom : Measure ℂ) (m + 2)
  let f : (Fin (n + 1) → PaperIndicatorAtomRow m) → ℝ :=
    profile.paperIndicatorOpenPressure center z q
  have hf : Measurable f :=
    profile.measurable_paperIndicatorOpenPressure center z q (n + 1)
  apply memLp_two_of_iid_raw_replacement_integrable μ f hf
  · intro i rows
    simpa only [f, μ] using
      profile.directional_paperIndicatorOpenPressure_replacement_sq_integrable
        atom phase hdir hL hc₀ hsqrt center z q rows i
          hsecondInt hsecond
  · intro i
    simpa only [f, μ, paperIndicatorOpenRowSampleMeasure] using
      profile.directional_paperIndicatorOpenPressure_rawOuter_integrable
        atom phase hdir hL hc₀ hsqrt center z q i
          hsecondInt hsecond

/-- Directional pressure variance with all technical Efron--Stein premises
derived from the manuscript hypotheses. -/
theorem variance_directional_paperIndicatorOpenPressure_le_auto
    {L : ℝ} (atom : ProbabilityMeasure ℂ) (phase : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (atom : Measure ℂ))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(atom : Measure ℂ) ≤ 1) :
    variance (profile.paperIndicatorOpenPressure center z q)
        (paperIndicatorOpenRowSampleMeasure
          (n + 1) m (atom : Measure ℂ)) ≤
      2 * (n + 1 : ℝ) * directionalPaperPressureFiberL2Bound m c₀ L z := by
  apply profile.variance_directional_paperIndicatorOpenPressure_le
    atom phase hdir hL hc₀ hsqrt center z q hsecondInt hsecond
  · exact profile.directional_paperIndicatorOpenPressure_memLp_two
      atom phase hdir hL hc₀ hsqrt center z q hsecondInt hsecond
  · intro i
    exact profile.directional_paperIndicatorOpenPressure_rawOuter_integrable
      atom phase hdir hL hc₀ hsqrt center z q i hsecondInt hsecond

/-- Expected maximum over all exterior degrees for the directional branch,
with all row-wise integrability premises supplied automatically. -/
theorem integral_max_directional_paperIndicatorOpenPressure_le_auto
    {L : ℝ} (atom : ProbabilityMeasure ℂ) (phase : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (atom : Measure ℂ))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(atom : Measure ℂ) ≤ 1) :
    let Y : ExteriorDegree (m + 1) →
        (Fin (n + 1) → PaperIndicatorAtomRow m) → ℝ := fun q =>
      profile.paperIndicatorOpenPressure center z q
    (∫ rows, maxCenteredAbs
        (paperIndicatorOpenRowSampleMeasure
          (n + 1) m (atom : Measure ℂ)) Y rows
      ∂paperIndicatorOpenRowSampleMeasure
        (n + 1) m (atom : Measure ℂ)) ≤
      Real.sqrt ((m + 2 : ℝ) *
        (2 * (n + 1 : ℝ) *
          directionalPaperPressureFiberL2Bound m c₀ L z)) := by
  apply profile.integral_max_directional_paperIndicatorOpenPressure_le
    atom phase hdir hL hc₀ hsqrt center z hsecondInt hsecond
  · intro q
    exact profile.directional_paperIndicatorOpenPressure_memLp_two
      atom phase hdir hL hc₀ hsqrt center z q hsecondInt hsecond
  · intro q i
    exact profile.directional_paperIndicatorOpenPressure_rawOuter_integrable
      atom phase hdir hL hc₀ hsqrt center z q i hsecondInt hsecond

/-- Per-degree variance on the literal flat atom sample defining the
directional random matrix. -/
theorem variance_directional_paperIndicatorFlatOpenPressure_le_auto
    {L : ℝ} (atom : ProbabilityMeasure ℂ) (phase : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (atom : Measure ℂ))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(atom : Measure ℂ) ≤ 1) :
    variance (profile.paperIndicatorFlatOpenPressure center z q)
        (paperIndicatorSampleMeasure (n + 1) m (atom : Measure ℂ)) ≤
      2 * (n + 1 : ℝ) * directionalPaperPressureFiberL2Bound m c₀ L z := by
  let e := paperIndicatorFlatRowsEquiv (n + 1) m
  let μflat := paperIndicatorSampleMeasure (n + 1) m (atom : Measure ℂ)
  let μrows := paperIndicatorOpenRowSampleMeasure
    (n + 1) m (atom : Measure ℂ)
  have hpres : MeasurePreserving e μflat μrows := by
    simpa only [e, μflat, μrows] using
      (paperIndicatorFlatRows_measurePreserving
        (n + 1) m (atom : Measure ℂ))
  calc
    variance (profile.paperIndicatorFlatOpenPressure center z q) μflat =
        variance (profile.paperIndicatorOpenPressure center z q) μrows := by
      change variance (fun ω => profile.paperIndicatorOpenPressure center z q
        (e ω)) μflat =
          variance (profile.paperIndicatorOpenPressure center z q) μrows
      exact hpres.variance_fun_comp
        (profile.measurable_paperIndicatorOpenPressure
          center z q (n + 1)).aemeasurable
    _ ≤ 2 * (n + 1 : ℝ) * directionalPaperPressureFiberL2Bound m c₀ L z :=
      profile.variance_directional_paperIndicatorOpenPressure_le_auto
        atom phase hdir hL hc₀ hsqrt center z q hsecondInt hsecond

/-- Expected maximal centered directional pressure on the literal flat
atom sample defining the paper's random matrix. -/
theorem integral_max_directional_paperIndicatorFlatOpenPressure_le_auto
    {L : ℝ} (atom : ProbabilityMeasure ℂ) (phase : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (atom : Measure ℂ))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(atom : Measure ℂ) ≤ 1) :
    (∫ ω, maxCenteredAbs
        (paperIndicatorSampleMeasure (n + 1) m (atom : Measure ℂ))
        (fun q => profile.paperIndicatorFlatOpenPressure center z q) ω
      ∂paperIndicatorSampleMeasure (n + 1) m (atom : Measure ℂ)) ≤
      Real.sqrt ((m + 2 : ℝ) *
        (2 * (n + 1 : ℝ) *
          directionalPaperPressureFiberL2Bound m c₀ L z)) := by
  let e := paperIndicatorFlatRowsEquiv (n + 1) m
  let μflat := paperIndicatorSampleMeasure (n + 1) m (atom : Measure ℂ)
  let μrows := paperIndicatorOpenRowSampleMeasure
    (n + 1) m (atom : Measure ℂ)
  let Y : ExteriorDegree (m + 1) →
      (Fin (n + 1) → PaperIndicatorAtomRow m) → ℝ := fun q =>
    profile.paperIndicatorOpenPressure center z q
  have hpres : MeasurePreserving e μflat μrows := by
    simpa only [e, μflat, μrows] using
      (paperIndicatorFlatRows_measurePreserving
        (n + 1) m (atom : Measure ℂ))
  have htransport := integral_maxCenteredAbs_comp_measurePreserving e hpres Y
  calc
    (∫ ω, maxCenteredAbs μflat
        (fun q => profile.paperIndicatorFlatOpenPressure center z q) ω ∂μflat) =
        ∫ rows, maxCenteredAbs μrows Y rows ∂μrows := by
      change (∫ ω, maxCenteredAbs μflat
        (fun q ω => Y q (e ω)) ω ∂μflat) =
          ∫ rows, maxCenteredAbs μrows Y rows ∂μrows
      exact htransport
    _ ≤ Real.sqrt ((m + 2 : ℝ) *
          (2 * (n + 1 : ℝ) *
            directionalPaperPressureFiberL2Bound m c₀ L z)) := by
      simpa only [Y, μrows] using
        profile.integral_max_directional_paperIndicatorOpenPressure_le_auto
          atom phase hdir hL hc₀ hsqrt center z hsecondInt hsecond

end PaperIndicatorWeights

end CircularLawSection4
