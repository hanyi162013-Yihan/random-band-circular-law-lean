import CircularLawSection4.PaperPressureDirectionalL2
import CircularLawSection4.PaperPressureComplexConcentration

/-!
# Directional concentration for the paper's actual random open pressure

The full directional row-fiber `L²` estimate is fed into the same literal
row replacement, unbounded continuous Efron--Stein, variance, and finite
exterior-degree maximal-deviation chain used by the other atom branches.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace PaperIndicatorWeights

variable {m n : ℕ} {c₀ C₀ : ℝ}

/-- Explicit one-row `L²` constant for the directional-density branch. -/
def directionalPaperPressureFiberL2Bound
    (m : ℕ) (c₀ L : ℝ) (z : ℂ) : ℝ :=
  2 * oneSidedLogSecondMomentBound
      ((4 * L) /
        ((1 / 2 : ℝ) * Real.sqrt (c₀ / (m + 2 : ℝ)))) 1 +
    2 * (3 * (Real.log (m + 2 : ℝ)) ^ 2 + 3 + 3 * ‖z‖ ^ 2)

/-- For every fixed outside sample, replacing one literal matrix row has a
square-integrable pressure difference in the directional branch. -/
theorem directional_paperIndicatorOpenPressure_replacement_sq_integrable
    {L : ℝ} (atom : ProbabilityMeasure ℂ) (phase : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin (n + 1) → PaperIndicatorAtomRow m) (i : Fin (n + 1))
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (atom : Measure ℂ))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(atom : Measure ℂ) ≤ 1) :
    Integrable (fun a : PaperIndicatorAtomRow m =>
      (profile.paperIndicatorOpenPressure center z q rows -
        profile.paperIndicatorOpenPressure center z q
          (Function.update rows i a)) ^ 2)
      (paperIndicatorRowMeasure m (atom : Measure ℂ)) := by
  let μ := paperIndicatorRowMeasure m (atom : Measure ℂ)
  letI : IsProbabilityMeasure μ :=
    iidMeasure_isProbability (atom : Measure ℂ) (m + 2)
  let scale := profile.paperPressureRowScale center q
    (profile.paperPressureLeftHistory center z q rows i)
    (profile.paperPressureRightHistory center z q rows i)
  let g : PaperIndicatorAtomRow m → ℝ := fun a =>
    profile.paperIndicatorOpenPressure center z q (Function.update rows i a)
  have hfiber :=
    profile.directional_paperIndicatorOpenPressure_fiber_absLog_L2_all_scales
      atom phase hdir hL hc₀ hsqrt center z q rows i hsecondInt hsecond
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
      (profile.paperIndicatorOpenPressure center z q rows - Real.log scale)).sub
      herr
  have hint := hdiff.integrable_sq
  convert hint using 1
  funext a
  dsimp only [g]
  ring

/-- Raw Efron--Stein energy of replacing any one complete actual complex row
under directional density. -/
theorem directional_paperIndicatorOpenPressure_rawResamplingEnergy_le
    {L : ℝ} (atom : ProbabilityMeasure ℂ) (phase : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1)) (i : Fin (n + 1))
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (atom : Measure ℂ))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(atom : Measure ℂ) ≤ 1)
    (hrawOuter : Integrable (fun rows => ∫ a,
      (profile.paperIndicatorOpenPressure center z q rows -
        profile.paperIndicatorOpenPressure center z q
          (Function.update rows i a)) ^ 2
        ∂paperIndicatorRowMeasure m (atom : Measure ℂ))
      (paperIndicatorOpenRowSampleMeasure (n + 1) m (atom : Measure ℂ))) :
    iidRawResamplingEnergy (paperIndicatorRowMeasure m (atom : Measure ℂ))
        (profile.paperIndicatorOpenPressure center z q) i ≤
      4 * directionalPaperPressureFiberL2Bound m c₀ L z := by
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
  apply iidRawResamplingEnergy_le_four_mul_of_fiber_memLp
    μ f i fiberCenter
  · simpa only [μ, f, paperIndicatorOpenRowSampleMeasure] using hrawOuter
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

/-- Per-exterior-degree variance bound for the actual random indicator
matrix under directional density. -/
theorem variance_directional_paperIndicatorOpenPressure_le
    {L : ℝ} (atom : ProbabilityMeasure ℂ) (phase : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (atom : Measure ℂ))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(atom : Measure ℂ) ≤ 1)
    (hpressureL2 : MemLp
      (profile.paperIndicatorOpenPressure center z q) 2
      (paperIndicatorOpenRowSampleMeasure
        (n + 1) m (atom : Measure ℂ)))
    (hrawOuter : ∀ i : Fin (n + 1), Integrable (fun rows => ∫ a,
      (profile.paperIndicatorOpenPressure center z q rows -
        profile.paperIndicatorOpenPressure center z q
          (Function.update rows i a)) ^ 2
        ∂paperIndicatorRowMeasure m (atom : Measure ℂ))
      (paperIndicatorOpenRowSampleMeasure
        (n + 1) m (atom : Measure ℂ))) :
    variance (profile.paperIndicatorOpenPressure center z q)
        (paperIndicatorOpenRowSampleMeasure
          (n + 1) m (atom : Measure ℂ)) ≤
      2 * (n + 1 : ℝ) * directionalPaperPressureFiberL2Bound m c₀ L z := by
  let μ := paperIndicatorRowMeasure m (atom : Measure ℂ)
  letI : IsProbabilityMeasure μ :=
    iidMeasure_isProbability (atom : Measure ℂ) (m + 2)
  let f : (Fin (n + 1) → PaperIndicatorAtomRow m) → ℝ :=
    profile.paperIndicatorOpenPressure center z q
  have hmeas : Measurable f :=
    profile.measurable_paperIndicatorOpenPressure center z q (n + 1)
  have hES := variance_iidMeasure_le_half_sum_raw_memLp μ f hmeas
    (by simpa only [f, μ, paperIndicatorOpenRowSampleMeasure] using hpressureL2)
    (fun i rows => by
      simpa only [f, μ] using
        profile.directional_paperIndicatorOpenPressure_replacement_sq_integrable
          atom phase hdir hL hc₀ hsqrt center z q rows i
            hsecondInt hsecond)
    (fun i => by
      simpa only [f, μ, paperIndicatorOpenRowSampleMeasure] using hrawOuter i)
  calc
    variance (profile.paperIndicatorOpenPressure center z q)
        (paperIndicatorOpenRowSampleMeasure
          (n + 1) m (atom : Measure ℂ)) ≤
        (1 / 2 : ℝ) * ∑ i : Fin (n + 1),
          iidRawResamplingEnergy μ f i := by
      simpa only [f, μ, paperIndicatorOpenRowSampleMeasure] using hES
    _ ≤ (1 / 2 : ℝ) * ∑ _i : Fin (n + 1),
          (4 * directionalPaperPressureFiberL2Bound m c₀ L z) := by
      gcongr with i
      exact profile.directional_paperIndicatorOpenPressure_rawResamplingEnergy_le
        atom phase hdir hL hc₀ hsqrt center z q i hsecondInt hsecond
          (hrawOuter i)
    _ = 2 * (n + 1 : ℝ) *
          directionalPaperPressureFiberL2Bound m c₀ L z := by
      simp
      ring

/-- Expected maximum of the centered pressure over every exterior degree
for the actual directional random matrix. -/
theorem integral_max_directional_paperIndicatorOpenPressure_le
    {L : ℝ} (atom : ProbabilityMeasure ℂ) (phase : ℝ)
    (hdir : HasDirectionalConditionalDensity atom phase L) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) (atom : Measure ℂ))
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂(atom : Measure ℂ) ≤ 1)
    (hpressureL2 : ∀ q : ExteriorDegree (m + 1), MemLp
      (profile.paperIndicatorOpenPressure center z q) 2
      (paperIndicatorOpenRowSampleMeasure
        (n + 1) m (atom : Measure ℂ)))
    (hrawOuter : ∀ (q : ExteriorDegree (m + 1)) (i : Fin (n + 1)),
      Integrable (fun rows => ∫ a,
        (profile.paperIndicatorOpenPressure center z q rows -
          profile.paperIndicatorOpenPressure center z q
            (Function.update rows i a)) ^ 2
          ∂paperIndicatorRowMeasure m (atom : Measure ℂ))
        (paperIndicatorOpenRowSampleMeasure
          (n + 1) m (atom : Measure ℂ))) :
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
  dsimp only
  let μrow := paperIndicatorRowMeasure m (atom : Measure ℂ)
  letI : IsProbabilityMeasure μrow :=
    iidMeasure_isProbability (atom : Measure ℂ) (m + 2)
  let μrows := iidMeasure μrow (n + 1)
  letI : IsProbabilityMeasure μrows := iidMeasure_isProbability μrow (n + 1)
  let Y : ExteriorDegree (m + 1) →
      (Fin (n + 1) → PaperIndicatorAtomRow m) → ℝ := fun q =>
    profile.paperIndicatorOpenPressure center z q
  have hmax := integral_maxCenteredAbs_le_sqrt_card_mul
    (μ := μrows) (Y := Y)
    (fun q => by
      simpa only [Y, μrows, μrow, paperIndicatorOpenRowSampleMeasure] using
        hpressureL2 q)
    (fun q => by
      simpa only [Y, μrows, μrow, paperIndicatorOpenRowSampleMeasure] using
        profile.variance_directional_paperIndicatorOpenPressure_le
          atom phase hdir hL hc₀ hsqrt center z q hsecondInt hsecond
            (hpressureL2 q) (hrawOuter q))
  convert hmax using 1 <;>
    simp only [Y, μrows, μrow, paperIndicatorOpenRowSampleMeasure,
      Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] <;> ring

end PaperIndicatorWeights

end CircularLawSection4
