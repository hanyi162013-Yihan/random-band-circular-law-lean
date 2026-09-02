import CircularLawSection4.FlatIIDRows
import CircularLawSection4.PaperIndicatorRandomMatrix
import CircularLawSection4.PaperPressureComplexConcentration
import CircularLawSection4.PaperPressureRealConcentration

/-!
# Concentration on the flat random-matrix sample space

The literal matrix `paperIndicatorX` is defined on a flat vector of
`N * (m + 2)` scalar atoms, whereas the row-resampling argument is most
naturally stated on `N` complete IID rows.  This file proves that the two
sample spaces are related by a measure-preserving measurable equivalence,
identifies its coordinates with `paperIndicatorXi` (and its real analogue),
and transports the final pressure variance and maximal-deviation bounds back
to the flat sample space of the actual random matrix.
-/

open scoped ENNReal MeasureTheory
open MeasureTheory ProbabilityTheory

noncomputable section

namespace CircularLawSection4

/-- Split the flat complex atom vector into complete rows. -/
def paperIndicatorFlatRowsEquiv (N m : ℕ) :
    (Fin (N * (m + 2)) → ℂ) ≃ᵐ
      (Fin N → PaperIndicatorWeights.PaperIndicatorAtomRow m) :=
  flatIIDRowsMeasurableEquiv N (m + 2)

/-- Split the flat real atom vector into complete rows. -/
def paperIndicatorRealFlatRowsEquiv (N m : ℕ) :
    (Fin (N * (m + 2)) → ℝ) ≃ᵐ
      (Fin N → PaperIndicatorWeights.PaperIndicatorRealAtomRow m) :=
  flatIIDRowsMeasurableEquiv N (m + 2)

@[simp] theorem paperIndicatorFlatIndex_finEquiv
    (N m : ℕ) [NeZero N] (i : Fin N) (k : Fin (m + 2)) :
    paperIndicatorFlatIndex N m (ZMod.finEquiv N i) k =
      finProdFinEquiv (i, k) := by
  change ((finProdFinEquiv.symm.trans
      (Equiv.prodCongr (ZMod.finEquiv N).toEquiv (Equiv.refl _))).symm
        (ZMod.finEquiv N i, k)) = finProdFinEquiv (i, k)
  simp

/-- The row splitting uses exactly the same scalar coordinate as the flat
random-matrix definition. -/
@[simp] theorem paperIndicatorFlatRowsEquiv_apply_eq_Xi
    (N m : ℕ) [NeZero N]
    (ω : Fin (N * (m + 2)) → ℂ) (i : Fin N) (k : Fin (m + 2)) :
    paperIndicatorFlatRowsEquiv N m ω i k =
      paperIndicatorXi N m ω (ZMod.finEquiv N i) k := by
  simp [paperIndicatorFlatRowsEquiv, paperIndicatorXi]

/-- Real counterpart of `paperIndicatorFlatRowsEquiv_apply_eq_Xi`. -/
@[simp] theorem paperIndicatorRealFlatRowsEquiv_apply_eq_XiOfReal
    (N m : ℕ) [NeZero N]
    (ω : Fin (N * (m + 2)) → ℝ) (i : Fin N) (k : Fin (m + 2)) :
    ((paperIndicatorRealFlatRowsEquiv N m ω i k : ℝ) : ℂ) =
      paperIndicatorXiOfReal N m ω (ZMod.finEquiv N i) k := by
  simp [paperIndicatorRealFlatRowsEquiv, paperIndicatorXiOfReal]

/-- The flat complex atom law is carried exactly to the IID complete-row
law used by the leave-one-row argument. -/
theorem paperIndicatorFlatRows_measurePreserving
    (N m : ℕ) [NeZero N]
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν] :
    MeasurePreserving (paperIndicatorFlatRowsEquiv N m)
      (paperIndicatorSampleMeasure N m ν)
      (PaperIndicatorWeights.paperIndicatorOpenRowSampleMeasure N m ν) := by
  simpa only [paperIndicatorFlatRowsEquiv, paperIndicatorSampleMeasure,
    PaperIndicatorWeights.paperIndicatorOpenRowSampleMeasure,
    PaperIndicatorWeights.paperIndicatorRowMeasure] using
      (flatIIDRows_measurePreserving N (m + 2) ν)

/-- The same flat-to-row statement for real atoms. -/
theorem paperIndicatorRealFlatRows_measurePreserving
    (N m : ℕ) [NeZero N]
    (ν : Measure ℝ) [SigmaFinite ν] [IsProbabilityMeasure ν] :
    MeasurePreserving (paperIndicatorRealFlatRowsEquiv N m)
      (paperIndicatorRealSampleMeasure N m ν)
      (PaperIndicatorWeights.paperIndicatorRealOpenRowSampleMeasure N m ν) := by
  simpa only [paperIndicatorRealFlatRowsEquiv, paperIndicatorRealSampleMeasure,
    PaperIndicatorWeights.paperIndicatorRealOpenRowSampleMeasure,
    PaperIndicatorWeights.paperIndicatorRealRowMeasure] using
      (flatIIDRows_measurePreserving N (m + 2) ν)

/-- A measure-preserving measurable equivalence transports the expected
maximum of a finite centered family, including the centering expectations
themselves. -/
theorem integral_maxCenteredAbs_comp_measurePreserving
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [Fintype ι] [Nonempty ι]
    {μ : Measure Ω} {ν : Measure Ω'}
    (e : Ω ≃ᵐ Ω') (h : MeasurePreserving e μ ν)
    (Y : ι → Ω' → ℝ) :
    (∫ ω, maxCenteredAbs μ (fun i ω => Y i (e ω)) ω ∂μ) =
      ∫ x, maxCenteredAbs ν Y x ∂ν := by
  have hpoint (ω : Ω) :
      maxCenteredAbs μ (fun i ω => Y i (e ω)) ω =
        maxCenteredAbs ν Y (e ω) := by
    unfold maxCenteredAbs
    apply congrArg finiteMaxAbs
    funext i
    unfold centered
    rw [h.integral_comp' (Y i)]
  calc
    (∫ ω, maxCenteredAbs μ (fun i ω => Y i (e ω)) ω ∂μ) =
        ∫ ω, maxCenteredAbs ν Y (e ω) ∂μ := by
      exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ x, maxCenteredAbs ν Y x ∂ν := h.integral_comp' _

namespace PaperIndicatorWeights

variable {m n : ℕ} {c₀ C₀ : ℝ}

/-- The open exterior pressure, now viewed directly as a function of the
flat complex atom vector defining `paperIndicatorX`. -/
def paperIndicatorFlatOpenPressure
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (ω : Fin (n * (m + 2)) → ℂ) : ℝ :=
  profile.paperIndicatorOpenPressure center z q
    (paperIndicatorFlatRowsEquiv n m ω)

/-- Real-atom version of the flat open pressure. -/
def paperIndicatorRealFlatOpenPressure
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (ω : Fin (n * (m + 2)) → ℝ) : ℝ :=
  profile.paperIndicatorOpenPressureOfReal center z q
    (paperIndicatorRealFlatRowsEquiv n m ω)

/-- Per-degree pressure variance for the literal flat complex random-matrix
sample.  The analytic premises are exactly those of the row-wise theorem;
only the sample-space presentation has changed. -/
theorem variance_complex_paperIndicatorFlatOpenPressure_le
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
    variance (profile.paperIndicatorFlatOpenPressure center z q)
        (paperIndicatorSampleMeasure (n + 1) m ν) ≤
      2 * (n + 1 : ℝ) * complexPaperPressureFiberL2Bound m c₀ L z := by
  let e := paperIndicatorFlatRowsEquiv (n + 1) m
  let μflat := paperIndicatorSampleMeasure (n + 1) m ν
  let μrows := paperIndicatorOpenRowSampleMeasure (n + 1) m ν
  have hpres : MeasurePreserving e μflat μrows := by
    simpa only [e, μflat, μrows] using
      (paperIndicatorFlatRows_measurePreserving (n + 1) m ν)
  calc
    variance (profile.paperIndicatorFlatOpenPressure center z q) μflat =
        variance (profile.paperIndicatorOpenPressure center z q) μrows := by
      change variance (fun ω => profile.paperIndicatorOpenPressure center z q
        (e ω)) μflat =
          variance (profile.paperIndicatorOpenPressure center z q) μrows
      exact hpres.variance_fun_comp
        (profile.measurable_paperIndicatorOpenPressure
          center z q (n + 1)).aemeasurable
    _ ≤ 2 * (n + 1 : ℝ) * complexPaperPressureFiberL2Bound m c₀ L z :=
      profile.variance_complex_paperIndicatorOpenPressure_le
        ν hν hL hc₀ hsqrt center z q hνInt hνSecond
          hpressureL2 hrawOuter

/-- Per-degree pressure variance for the literal flat real random-matrix
sample. -/
theorem variance_real_paperIndicatorFlatOpenPressure_le
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
    variance (profile.paperIndicatorRealFlatOpenPressure center z q)
        (paperIndicatorRealSampleMeasure (n + 1) m ν) ≤
      2 * (n + 1 : ℝ) *
        realPaperPressureFiberL2Bound m c₀ L z theta := by
  let e := paperIndicatorRealFlatRowsEquiv (n + 1) m
  let μflat := paperIndicatorRealSampleMeasure (n + 1) m ν
  let μrows := paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν
  have hpres : MeasurePreserving e μflat μrows := by
    simpa only [e, μflat, μrows] using
      (paperIndicatorRealFlatRows_measurePreserving (n + 1) m ν)
  calc
    variance (profile.paperIndicatorRealFlatOpenPressure center z q) μflat =
        variance (profile.paperIndicatorOpenPressureOfReal center z q) μrows := by
      change variance (fun ω => profile.paperIndicatorOpenPressureOfReal
        center z q (e ω)) μflat =
          variance (profile.paperIndicatorOpenPressureOfReal center z q) μrows
      exact hpres.variance_fun_comp
        (profile.measurable_paperIndicatorOpenPressureOfReal
          center z q (n + 1)).aemeasurable
    _ ≤ 2 * (n + 1 : ℝ) *
          realPaperPressureFiberL2Bound m c₀ L z theta :=
      profile.variance_real_paperIndicatorOpenPressure_le
        ν hν hL hc₀ hsqrt center z q hνInt hνSecond theta
          htheta0 htheta1 hpressureL2 hrawOuter

/-- Expected maximum over every exterior degree, stated directly on the
flat complex atom sample defining `paperIndicatorX`. -/
theorem integral_max_complex_paperIndicatorFlatOpenPressure_le
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
    (∫ ω, maxCenteredAbs
        (paperIndicatorSampleMeasure (n + 1) m ν)
        (fun q => profile.paperIndicatorFlatOpenPressure center z q) ω
      ∂paperIndicatorSampleMeasure (n + 1) m ν) ≤
      Real.sqrt ((m + 2 : ℝ) *
        (2 * (n + 1 : ℝ) * complexPaperPressureFiberL2Bound m c₀ L z)) := by
  let e := paperIndicatorFlatRowsEquiv (n + 1) m
  let μflat := paperIndicatorSampleMeasure (n + 1) m ν
  let μrows := paperIndicatorOpenRowSampleMeasure (n + 1) m ν
  let Y : ExteriorDegree (m + 1) →
      (Fin (n + 1) → PaperIndicatorAtomRow m) → ℝ := fun q =>
    profile.paperIndicatorOpenPressure center z q
  have hpres : MeasurePreserving e μflat μrows := by
    simpa only [e, μflat, μrows] using
      (paperIndicatorFlatRows_measurePreserving (n + 1) m ν)
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
          (2 * (n + 1 : ℝ) * complexPaperPressureFiberL2Bound m c₀ L z)) := by
      simpa only [Y, μrows] using
        profile.integral_max_complex_paperIndicatorOpenPressure_le
          ν hν hL hc₀ hsqrt center z hνInt hνSecond hpressureL2 hrawOuter

/-- Real-atom counterpart of
`integral_max_complex_paperIndicatorFlatOpenPressure_le`. -/
theorem integral_max_real_paperIndicatorFlatOpenPressure_le
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
    (∫ ω, maxCenteredAbs
        (paperIndicatorRealSampleMeasure (n + 1) m ν)
        (fun q => profile.paperIndicatorRealFlatOpenPressure center z q) ω
      ∂paperIndicatorRealSampleMeasure (n + 1) m ν) ≤
      Real.sqrt ((m + 2 : ℝ) *
        (2 * (n + 1 : ℝ) *
          realPaperPressureFiberL2Bound m c₀ L z theta)) := by
  let e := paperIndicatorRealFlatRowsEquiv (n + 1) m
  let μflat := paperIndicatorRealSampleMeasure (n + 1) m ν
  let μrows := paperIndicatorRealOpenRowSampleMeasure (n + 1) m ν
  let Y : ExteriorDegree (m + 1) →
      (Fin (n + 1) → PaperIndicatorRealAtomRow m) → ℝ := fun q =>
    profile.paperIndicatorOpenPressureOfReal center z q
  have hpres : MeasurePreserving e μflat μrows := by
    simpa only [e, μflat, μrows] using
      (paperIndicatorRealFlatRows_measurePreserving (n + 1) m ν)
  have htransport := integral_maxCenteredAbs_comp_measurePreserving e hpres Y
  calc
    (∫ ω, maxCenteredAbs μflat
        (fun q => profile.paperIndicatorRealFlatOpenPressure center z q) ω ∂μflat) =
        ∫ rows, maxCenteredAbs μrows Y rows ∂μrows := by
      change (∫ ω, maxCenteredAbs μflat
        (fun q ω => Y q (e ω)) ω ∂μflat) =
          ∫ rows, maxCenteredAbs μrows Y rows ∂μrows
      exact htransport
    _ ≤ Real.sqrt ((m + 2 : ℝ) *
          (2 * (n + 1 : ℝ) *
            realPaperPressureFiberL2Bound m c₀ L z theta)) := by
      simpa only [Y, μrows] using
        profile.integral_max_real_paperIndicatorOpenPressure_le
          ν hν hL hc₀ hsqrt center z hνInt hνSecond theta
            htheta0 htheta1 hpressureL2 hrawOuter

end PaperIndicatorWeights

end CircularLawSection4
