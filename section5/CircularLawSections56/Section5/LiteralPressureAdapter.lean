import CircularLawSection4.PressureProbability
import CircularLawSection4.PaperPressureAssumptionFree
import CircularLawSections56.Section5.PressureLifting
import CircularLawSections56.Section5.NearEndToEnd

/-!
# Literal finite-pressure adapter from Section 4 to Section 5

This file connects the finite-family probability API in
`CircularLawSection4.PressureProbability` to Section 5's signed finite maximum and `L¹`
receiver structures, and directly invokes the assumption-free paper-indicator bounds from
`CircularLawSection4.PaperPressureAssumptionFree`.  It proves the finite-maximum and
integration transport:

* Section 5's signed maximum of the absolute coordinates over `Finset.univ` is Section 4's
  `finiteMaxAbs`;
* the random maximum differs from the maximum of the coordinate means by at most Section
  4's `maxCenteredAbs`;
* coordinatewise `MemLp 2` makes this difference integrable, so any Section 4 integral
  bound becomes the fluctuation half of an `L1ApproximationTri` or
  `TwoStepL1ApproximationTri` certificate;
* the literal flat complex and real paper-indicator pressures inherit `MemLp 2` through
  the proved flat-to-row equivalence, allowing the Section 4 `_auto` bounds to be called
  without an extra integrability premise;
* positivity of every exterior-degree norm identifies the logarithm of Section 4's
  maximal exterior norm with Section 5's finite signed maximum of the logarithmic norms.

The flat `MemLp` and `_auto` fluctuation declarations below are literal Section 4 pressure
results.  This file still does not identify the manuscript determinant/outside observable
with an exterior-family product, nor prove the actual iid-cell adapted increment estimates.
The optional cell telescope at the end assumes both per-cell lower and upper estimates; a
projective lower estimate alone is not presented as a two-sided cell bound.
-/

open scoped BigOperators Matrix.Norms.L2Operator
open Filter MeasureTheory ProbabilityTheory Topology

namespace CircularLawSections56.Section5

universe u v

section FixedFiniteFamily

variable {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]

/-- On a nonempty finite type, the Section 5 signed maximum of absolute coordinates over
`Finset.univ` is definitionally Section 4's `finiteMaxAbs`. -/
theorem finiteSignedMax_univ_abs_eq_section4_finiteMaxAbs
    [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    finiteSignedMax Finset.univ Finset.univ_nonempty (fun i => |x i|) =
      CircularLawSection4.finiteMaxAbs x := by
  rfl

/-- Pointwise finite-max transport: the maximum of the random coordinates differs from
the maximum of their coordinate means by at most Section 4's centered absolute maximum. -/
theorem abs_randomFiniteSignedMax_sub_mean_le_maxCenteredAbs
    [Fintype ι] [Nonempty ι] (μ : Measure Ω) (Y : ι → Ω → ℝ) (ω : Ω) :
    |finiteSignedMax Finset.univ Finset.univ_nonempty (fun i => Y i ω) -
        finiteSignedMax Finset.univ Finset.univ_nonempty
          (fun i => ∫ x, Y i x ∂μ)| ≤
      CircularLawSection4.maxCenteredAbs μ Y ω := by
  calc
    |finiteSignedMax Finset.univ Finset.univ_nonempty (fun i => Y i ω) -
        finiteSignedMax Finset.univ Finset.univ_nonempty
          (fun i => ∫ x, Y i x ∂μ)| ≤
        finiteSignedMax Finset.univ Finset.univ_nonempty
          (fun i => |Y i ω - ∫ x, Y i x ∂μ|) :=
      abs_finiteSignedMax_sub_le_finiteSignedMax_abs_sub
        Finset.univ_nonempty (fun i => Y i ω) (fun i => ∫ x, Y i x ∂μ)
    _ = CircularLawSection4.maxCenteredAbs μ Y ω := by
      rfl

/-- Coordinatewise `L²` control makes the absolute difference between the random finite
maximum and the finite maximum of coordinate means integrable. -/
theorem integrable_abs_randomFiniteSignedMax_sub_mean
    [Fintype ι] [Nonempty ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ι → Ω → ℝ) (hY : ∀ i, MemLp (Y i) 2 μ) :
    Integrable
      (fun ω =>
        |finiteSignedMax Finset.univ Finset.univ_nonempty (fun i => Y i ω) -
          finiteSignedMax Finset.univ Finset.univ_nonempty
            (fun i => ∫ x, Y i x ∂μ)|) μ := by
  have hRandomMax : MemLp
      (fun ω => finiteSignedMax Finset.univ Finset.univ_nonempty (fun i => Y i ω))
      2 μ := by
    simpa only [finiteSignedMax] using
      (CircularLawSection4.memLp_finsetSup'
        (μ := μ) Finset.univ_nonempty (fun i _ => hY i))
  exact ((hRandomMax.integrable (by simp)).sub (integrable_const _)).abs

/-- The pointwise comparison integrates: any Section 4 bound for `maxCenteredAbs` is an
`L¹` fluctuation bound for the random maximum around the maximum of coordinate means. -/
theorem integral_abs_randomFiniteSignedMax_sub_mean_le_maxCenteredAbs
    [Fintype ι] [Nonempty ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ι → Ω → ℝ) (hY : ∀ i, MemLp (Y i) 2 μ) :
    (∫ ω,
      |finiteSignedMax Finset.univ Finset.univ_nonempty (fun i => Y i ω) -
        finiteSignedMax Finset.univ Finset.univ_nonempty
          (fun i => ∫ x, Y i x ∂μ)| ∂μ) ≤
      ∫ ω, CircularLawSection4.maxCenteredAbs μ Y ω ∂μ := by
  apply integral_mono
    (integrable_abs_randomFiniteSignedMax_sub_mean μ Y hY)
    ((CircularLawSection4.memLp_maxCenteredAbs hY).integrable (by simp))
  intro ω
  exact abs_randomFiniteSignedMax_sub_mean_le_maxCenteredAbs μ Y ω

/-- Direct transport of Section 4's generic variance-sum estimate to the Section 5 finite
maximum centered at the maximum of coordinate expectations. -/
theorem integral_abs_randomFiniteSignedMax_sub_mean_le_sqrt_sum_variance
    [Fintype ι] [Nonempty ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : ι → Ω → ℝ) (hY : ∀ i, MemLp (Y i) 2 μ) :
    (∫ ω,
      |finiteSignedMax Finset.univ Finset.univ_nonempty (fun i => Y i ω) -
        finiteSignedMax Finset.univ Finset.univ_nonempty
          (fun i => ∫ x, Y i x ∂μ)| ∂μ) ≤
      Real.sqrt (∑ i, variance (Y i) μ) :=
  (integral_abs_randomFiniteSignedMax_sub_mean_le_maxCenteredAbs μ Y hY).trans
    (CircularLawSection4.integral_maxCenteredAbs_le_sqrt_sum_variance hY)

end FixedFiniteFamily

section LiteralPaperIndicatorPressure

open CircularLawSection4

/-- Literal scale-to-random-pressure identification for an exterior family.

Section 4 defines the scale as the largest Euclidean operator norm over the exterior
degrees, while Section 5 writes the random pressure as the largest logarithmic norm.  If
every degree has positive norm, monotonicity of `Real.log` identifies the two expressions
exactly.  Positivity is deliberately an explicit premise: this adapter does not prove
cofactor or exterior-power nonvanishing. -/
theorem log_exteriorFamilyMaxL2OpNorm_eq_finiteSignedMax_log_norm
    {d : ℕ}
    (B : (q : ExteriorDegree d) →
      Matrix (ExteriorIndex d q) (ExteriorIndex d q) ℂ)
    (hB : ∀ q, 0 < ‖B q‖) :
    Real.log (exteriorFamilyMaxL2OpNorm B) =
      finiteSignedMax Finset.univ Finset.univ_nonempty
        (fun q : ExteriorDegree d => Real.log ‖B q‖) := by
  unfold exteriorFamilyMaxL2OpNorm finiteSignedMax
  apply le_antisymm
  · obtain ⟨q, hq, hmax⟩ := Finset.exists_mem_eq_sup'
      Finset.univ_nonempty (fun q : ExteriorDegree d => ‖B q‖)
    rw [hmax]
    exact Finset.le_sup' (fun q : ExteriorDegree d => Real.log ‖B q‖) hq
  · obtain ⟨q, hq, hmax⟩ := Finset.exists_mem_eq_sup'
      Finset.univ_nonempty (fun q : ExteriorDegree d => Real.log ‖B q‖)
    rw [hmax]
    exact Real.log_le_log (hB q)
      (Finset.le_sup' (fun q : ExteriorDegree d => ‖B q‖) hq)

/-- The literal flat complex pressure is in `L²` on the flat atom space.

Section 4 states the automatic `MemLp` result on the IID-row presentation.  This lemma
transports it through Section 4's proved flat-to-row measure-preserving equivalence, so no
new analytic premise is introduced. -/
theorem complex_paperIndicatorFlatOpenPressure_memLp_two_auto
    {m n : ℕ} {c₀ C₀ L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ) (q : ExteriorDegree (m + 1))
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    MemLp (profile.paperIndicatorFlatOpenPressure center z q) 2
      (paperIndicatorSampleMeasure (n + 1) m ν) := by
  have hRow := profile.complex_paperIndicatorOpenPressure_memLp_two
    (n := n) ν hν hL hc₀ hsqrt center z q hνInt hνSecond
  have hPres := paperIndicatorFlatRows_measurePreserving (n + 1) m ν
  have hComp := hRow.comp_measurePreserving hPres
  change MemLp
    (profile.paperIndicatorOpenPressure center z q ∘
      ⇑(paperIndicatorFlatRowsEquiv (n + 1) m)) 2
    (paperIndicatorSampleMeasure (n + 1) m ν)
  exact hComp

/-- Real-input counterpart of
`complex_paperIndicatorFlatOpenPressure_memLp_two_auto`. -/
theorem real_paperIndicatorFlatOpenPressure_memLp_two_auto
    {m n : ℕ} {c₀ C₀ L : ℝ}
    (ν : Measure ℝ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ) (q : ExteriorDegree (m + 1))
    (hνInt : Integrable (fun u : ℝ => u ^ 2) ν)
    (hνSecond : ∫ u : ℝ, u ^ 2 ∂ν = 1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    MemLp (profile.paperIndicatorRealFlatOpenPressure center z q) 2
      (paperIndicatorRealSampleMeasure (n + 1) m ν) := by
  have hRow := profile.real_paperIndicatorOpenPressure_memLp_two
    (n := n) ν hν hL hc₀ hsqrt center z q hνInt hνSecond
      theta htheta0 htheta1
  have hPres := paperIndicatorRealFlatRows_measurePreserving (n + 1) m ν
  have hComp := hRow.comp_measurePreserving hPres
  change MemLp
    (profile.paperIndicatorOpenPressureOfReal center z q ∘
      ⇑(paperIndicatorRealFlatRowsEquiv (n + 1) m)) 2
    (paperIndicatorRealSampleMeasure (n + 1) m ν)
  exact hComp

/-- Literal complex-pressure fluctuation bound on the flat atom space.

The center is the Section 5 signed maximum of the per-degree expectations, not the
expectation of the random maximum.  The proof automatically supplies every flat-coordinate
`MemLp 2` fact above and then invokes Section 4's assumption-free maximal bound. -/
theorem integral_abs_randomMax_complex_paperIndicatorFlatOpenPressure_sub_mean_le_auto
    {m n : ℕ} {c₀ C₀ L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    (∫ ω,
      |finiteSignedMax Finset.univ Finset.univ_nonempty
          (fun q : ExteriorDegree (m + 1) =>
            profile.paperIndicatorFlatOpenPressure center z q ω) -
        finiteSignedMax Finset.univ Finset.univ_nonempty
          (fun q : ExteriorDegree (m + 1) =>
            ∫ x, profile.paperIndicatorFlatOpenPressure center z q x
              ∂paperIndicatorSampleMeasure (n + 1) m ν)|
      ∂paperIndicatorSampleMeasure (n + 1) m ν) ≤
      Real.sqrt ((m + 2 : ℝ) *
        (2 * (n + 1 : ℝ) *
          PaperIndicatorWeights.complexPaperPressureFiberL2Bound m c₀ L z)) := by
  let μ := paperIndicatorSampleMeasure (n + 1) m ν
  let _ : IsProbabilityMeasure μ := by
    simpa only [μ, paperIndicatorSampleMeasure] using
      iidMeasure_isProbability ν ((n + 1) * (m + 2))
  let Y : ExteriorDegree (m + 1) →
      (Fin ((n + 1) * (m + 2)) → ℂ) → ℝ := fun q =>
    profile.paperIndicatorFlatOpenPressure center z q
  have hY : ∀ q, MemLp (Y q) 2 μ := by
    intro q
    exact complex_paperIndicatorFlatOpenPressure_memLp_two_auto
      (n := n) ν hν hL profile hc₀ hsqrt center z q hνInt hνSecond
  have hSection4 :=
    profile.integral_max_complex_paperIndicatorFlatOpenPressure_le_auto
      (n := n) ν hν hL hc₀ hsqrt center z hνInt hνSecond
  simpa only [μ, Y] using
    (integral_abs_randomFiniteSignedMax_sub_mean_le_maxCenteredAbs μ Y hY).trans
      hSection4

/-- Literal real-pressure counterpart of
`integral_abs_randomMax_complex_paperIndicatorFlatOpenPressure_sub_mean_le_auto`. -/
theorem integral_abs_randomMax_real_paperIndicatorFlatOpenPressure_sub_mean_le_auto
    {m n : ℕ} {c₀ C₀ L : ℝ}
    (ν : Measure ℝ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (hνInt : Integrable (fun u : ℝ => u ^ 2) ν)
    (hνSecond : ∫ u : ℝ, u ^ 2 ∂ν = 1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (∫ ω,
      |finiteSignedMax Finset.univ Finset.univ_nonempty
          (fun q : ExteriorDegree (m + 1) =>
            profile.paperIndicatorRealFlatOpenPressure center z q ω) -
        finiteSignedMax Finset.univ Finset.univ_nonempty
          (fun q : ExteriorDegree (m + 1) =>
            ∫ x, profile.paperIndicatorRealFlatOpenPressure center z q x
              ∂paperIndicatorRealSampleMeasure (n + 1) m ν)|
      ∂paperIndicatorRealSampleMeasure (n + 1) m ν) ≤
      Real.sqrt ((m + 2 : ℝ) *
        (2 * (n + 1 : ℝ) *
          PaperIndicatorWeights.realPaperPressureFiberL2Bound m c₀ L z theta)) := by
  let μ := paperIndicatorRealSampleMeasure (n + 1) m ν
  let _ : IsProbabilityMeasure μ := by
    simpa only [μ, paperIndicatorRealSampleMeasure] using
      iidMeasure_isProbability ν ((n + 1) * (m + 2))
  let Y : ExteriorDegree (m + 1) →
      (Fin ((n + 1) * (m + 2)) → ℝ) → ℝ := fun q =>
    profile.paperIndicatorRealFlatOpenPressure center z q
  have hY : ∀ q, MemLp (Y q) 2 μ := by
    intro q
    exact real_paperIndicatorFlatOpenPressure_memLp_two_auto
      (n := n) ν hν hL profile hc₀ hsqrt center z q hνInt hνSecond
        theta htheta0 htheta1
  have hSection4 :=
    profile.integral_max_real_paperIndicatorFlatOpenPressure_le_auto
      (n := n) ν hν hL hc₀ hsqrt center z hνInt hνSecond
        theta htheta0 htheta1
  simpa only [μ, Y] using
    (integral_abs_randomFiniteSignedMax_sub_mean_le_maxCenteredAbs μ Y hY).trans
      hSection4

end LiteralPaperIndicatorPressure

section TriangularFiniteFamilies

variable {Ω : ℕ → Type u} {ι : ℕ → Type v}
  [∀ n, MeasurableSpace (Ω n)] [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]

/-- Random finite signed maximum for a triangular family of coordinate pressures. -/
noncomputable def randomFiniteSignedMaxTri
    (Y : ∀ n, ι n → Ω n → ℝ) : ∀ n, Ω n → ℝ :=
  fun n ω => finiteSignedMax Finset.univ Finset.univ_nonempty (fun i => Y n i ω)

/-- Finite signed maximum of the coordinate expectations at each triangular index. -/
noncomputable def coordinateMeanFiniteSignedMaxTri
    (μ : ∀ n, Measure (Ω n)) (Y : ∀ n, ι n → Ω n → ℝ) : ℕ → ℝ :=
  fun n => finiteSignedMax Finset.univ Finset.univ_nonempty
    (fun i => ∫ ω, Y n i ω ∂μ n)

/-- A supplied Section 4 integral bound for `maxCenteredAbs` becomes a one-step triangular
`L¹` certificate for the random finite maximum. -/
theorem l1ApproximationTri_of_section4_maxCenteredAbs_bound
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (Y : ∀ n, ι n → Ω n → ℝ) (fluctuationError : ℕ → ℝ)
    (hY : ∀ n i, MemLp (Y n i) 2 (μ n))
    (hSection4Bound : ∀ n,
      (∫ ω, CircularLawSection4.maxCenteredAbs (μ n) (Y n) ω ∂μ n) ≤
        fluctuationError n)
    (hFluctuationErrorZero : Tendsto fluctuationError atTop (𝓝 0)) :
    L1ApproximationTri μ (randomFiniteSignedMaxTri Y)
      (coordinateMeanFiniteSignedMaxTri μ Y) fluctuationError := by
  refine
    { integrable := ?_
      integral_le := ?_
      rate_tendsto_zero := hFluctuationErrorZero }
  · intro n
    exact integrable_abs_randomFiniteSignedMax_sub_mean (μ n) (Y n) (hY n)
  · intro n
    exact (integral_abs_randomFiniteSignedMax_sub_mean_le_maxCenteredAbs
      (μ n) (Y n) (hY n)).trans (hSection4Bound n)

/-- Combine an explicit seam with the transported Section 4 finite-pressure fluctuation
bound to produce the exact two-step receiver used by Section 5.

The seam hypotheses still contain the literal determinant/pressure identification; this
constructor only fills the intermediate and fluctuation fields. -/
noncomputable def twoStepL1ApproximationTri_of_section4_pressure_bound
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (observable : ∀ n, Ω n → ℝ) (Y : ∀ n, ι n → Ω n → ℝ)
    (seamError fluctuationError : ℕ → ℝ)
    (hSeamIntegrable : ∀ n,
      Integrable (fun ω => |observable n ω - randomFiniteSignedMaxTri Y n ω|) (μ n))
    (hSeamIntegral : ∀ n,
      ∫ ω, |observable n ω - randomFiniteSignedMaxTri Y n ω| ∂μ n ≤ seamError n)
    (hY : ∀ n i, MemLp (Y n i) 2 (μ n))
    (hSection4Bound : ∀ n,
      (∫ ω, CircularLawSection4.maxCenteredAbs (μ n) (Y n) ω ∂μ n) ≤
        fluctuationError n)
    (hSeamErrorZero : Tendsto seamError atTop (𝓝 0))
    (hFluctuationErrorZero : Tendsto fluctuationError atTop (𝓝 0)) :
    TwoStepL1ApproximationTri μ observable (coordinateMeanFiniteSignedMaxTri μ Y) := by
  refine
    { intermediate := randomFiniteSignedMaxTri Y
      seamError := seamError
      fluctuationError := fluctuationError
      seamIntegrable := hSeamIntegrable
      seamIntegral_le := hSeamIntegral
      fluctuationIntegrable := ?_
      fluctuationIntegral_le := ?_
      seamError_tendsto_zero := hSeamErrorZero
      fluctuationError_tendsto_zero := hFluctuationErrorZero }
  · intro n
    exact integrable_abs_randomFiniteSignedMax_sub_mean (μ n) (Y n) (hY n)
  · intro n
    exact (integral_abs_randomFiniteSignedMax_sub_mean_le_maxCenteredAbs
      (μ n) (Y n) (hY n)).trans (hSection4Bound n)

end TriangularFiniteFamilies

section ActiveCellTelescope

variable {ι : Type v}

/-- Active-index cell increment bounds imply the eventual degreewise lifting estimate.

Both the lower and upper per-cell bounds are explicit hypotheses.  Conditional
independence, projective lower estimates, and a genuine one-cell upper estimate must be
proved before applying this deterministic telescope. -/
theorem lifting_eventually_of_active_cell_increment_bounds
    (active : ℕ → Bool) (degrees : ℕ → Finset ι)
    (base lifted : ℕ → ι → ℝ) (cellPressure : ℕ → ι → ℕ → ℝ)
    (q m : ℕ → ℕ) (cellError : ℕ → ℝ)
    (hScale : ∀ᶠ n in atTop, active n = true → 0 < q n ∧ 0 < m n)
    (hZero : ∀ n, active n = true → ∀ r, r ∈ degrees n →
      cellPressure n r 0 = 0)
    (hLifted : ∀ n, active n = true → ∀ r, r ∈ degrees n →
      lifted n r = cellPressure n r (q n))
    (hCell : ∀ n, active n = true → ∀ r, r ∈ degrees n → ∀ j < q n,
      base n r - cellError n ≤
          cellPressure n r (j + 1) - cellPressure n r j ∧
        cellPressure n r (j + 1) - cellPressure n r j ≤
          base n r + cellError n) :
    ∀ᶠ n in atTop, active n = true →
      0 < q n ∧ 0 < m n ∧ ∀ r, r ∈ degrees n →
        (q n : ℝ) * (base n r - cellError n) ≤ lifted n r ∧
          lifted n r ≤ (q n : ℝ) * (base n r + cellError n) := by
  filter_upwards [hScale] with n hn
  intro hActive
  refine ⟨(hn hActive).1, (hn hActive).2, ?_⟩
  intro r hr
  rw [hLifted n hActive r hr]
  exact pressure_lift_degree (cellPressure n r) (base n r) (cellError n) (q n)
    (hZero n hActive r hr) (hCell n hActive r hr)

end ActiveCellTelescope

end CircularLawSections56.Section5
