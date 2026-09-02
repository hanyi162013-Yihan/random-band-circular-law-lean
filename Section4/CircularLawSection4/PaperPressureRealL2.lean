import CircularLawSection4.PaperOperatorAffineRealL2
import CircularLawSection4.PaperPressureLeaveOneOut

/-!
# Real row-fiber `L²` bound for the paper pressure

The paper pressure is complex-valued at the transfer-matrix level even when
the underlying atom law is real.  We therefore complexify a real row
coordinatewise, update the complexified outer-row sample, and identify the
resulting complete open product with the frozen operator-affine expression.

This module inserts the frozen left and right histories into
`paper_real_iid_operatorAffine_absLog_L2`.  The result is stated on the
literal real IID row fiber needed by leave-one-row-out resampling.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace PaperIndicatorWeights

variable {m n : ℕ} {c₀ C₀ : ℝ}

/-- One paper row whose `m + 2` scalar atoms are real. -/
abbrev PaperIndicatorRealAtomRow (m : ℕ) := Fin (m + 2) → ℝ

/-- Coordinatewise complexification of a real paper row. -/
def paperIndicatorComplexifyRealRow
    (row : PaperIndicatorRealAtomRow m) : PaperIndicatorAtomRow m :=
  fun j => (row j : ℂ)

/-- Coordinatewise complexification of a complete real row sample. -/
def paperIndicatorComplexifyRealRows
    (rows : Fin n → PaperIndicatorRealAtomRow m) :
    Fin n → PaperIndicatorAtomRow m :=
  fun i => paperIndicatorComplexifyRealRow (rows i)

/-- Complexification commutes exactly with replacing one row. -/
@[simp] theorem paperIndicatorComplexifyRealRows_update
    (rows : Fin n → PaperIndicatorRealAtomRow m) (i : Fin n)
    (newRow : PaperIndicatorRealAtomRow m) :
    paperIndicatorComplexifyRealRows (Function.update rows i newRow) =
      Function.update (paperIndicatorComplexifyRealRows rows) i
        (paperIndicatorComplexifyRealRow newRow) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [paperIndicatorComplexifyRealRows]
  · simp [paperIndicatorComplexifyRealRows, Function.update_of_ne hji]

/-- The real IID law on one complete paper row. -/
def paperIndicatorRealRowMeasure (m : ℕ) (ν : Measure ℝ) [SFinite ν] :
    Measure (PaperIndicatorRealAtomRow m) :=
  iidMeasure ν (m + 2)

/-- The paper's open pressure evaluated after complexifying every real atom. -/
def paperIndicatorOpenPressureOfReal
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorRealAtomRow m) : ℝ :=
  profile.paperIndicatorOpenPressure center z q
    (paperIndicatorComplexifyRealRows rows)

/-- The common leave-one-row reference scale for a frozen real outer-row
sample.  It is computed from the histories of its complexification. -/
def paperPressureRowScaleOfReal
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorRealAtomRow m) (i : Fin n) : ℝ :=
  let complexRows := paperIndicatorComplexifyRealRows rows
  profile.paperPressureRowScale center q
    (profile.paperPressureLeftHistory center z q complexRows i)
    (profile.paperPressureRightHistory center z q complexRows i)

/-- The reset-label atoms of a complexified real row agree with the
canonical finite enumeration used by the real operator-affine theorem. -/
theorem paperIndicatorOpenRowAtoms_complexifyReal_eq_paperOperatorAffineAtoms
    (row : PaperIndicatorRealAtomRow m) :
    paperIndicatorOpenRowAtoms (paperIndicatorComplexifyRealRow row) =
      paperOperatorAffineAtoms m (fun j => (row j : ℂ)) := by
  funext ell
  cases ell with
  | none =>
      simp [paperIndicatorOpenRowAtoms, paperIndicatorComplexifyRealRow,
        paperOperatorAffineAtoms, paperOperatorAffineLabelEquiv]
  | some j =>
      simp [paperIndicatorOpenRowAtoms, paperIndicatorComplexifyRealRow,
        paperOperatorAffineAtoms, paperOperatorAffineLabelEquiv]

/-- With all outside real rows frozen, a fresh real IID row has an explicit
`L²` logarithmic-deviation bound for the complete updated open pressure.

The bound is the real-atom/complex-operator indicator-profile bound.  Its
reference scale depends only on the complexified frozen histories and is
therefore common to every row in the fiber. -/
theorem real_paperIndicatorOpenPressure_fiber_memLp_two_and_integral_sq
    {L : ℝ}
    (ν : Measure ℝ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorRealAtomRow m) (i : Fin n)
    (hscale : 0 < profile.paperPressureRowScaleOfReal center z q rows i)
    (hνInt : Integrable (fun u : ℝ => u ^ 2) ν)
    (hνSecond : ∫ u : ℝ, u ^ 2 ∂ν = 1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    MemLp (fun a : PaperIndicatorRealAtomRow m =>
        |profile.paperIndicatorOpenPressureOfReal center z q
            (Function.update rows i a) -
          Real.log (profile.paperPressureRowScaleOfReal center z q rows i)|)
        2 (paperIndicatorRealRowMeasure m ν) ∧
      ∫ a : PaperIndicatorRealAtomRow m,
          |profile.paperIndicatorOpenPressureOfReal center z q
              (Function.update rows i a) -
            Real.log
              (profile.paperPressureRowScaleOfReal center z q rows i)| ^ 2
          ∂paperIndicatorRealRowMeasure m ν ≤
        2 * oneSidedLogSecondMomentBound
            ((4 * L) /
              (theta * Real.sqrt (c₀ / (m + 2 : ℝ)))) 1 +
          2 * (3 * (Real.log (m + 2 : ℝ)) ^ 2 + 3 +
            3 * ‖z‖ ^ 2) := by
  let complexRows := paperIndicatorComplexifyRealRows rows
  let Lhist := profile.paperPressureLeftHistory center z q complexRows i
  let Rhist := profile.paperPressureRightHistory center z q complexRows i
  let M := paperPressureFrozenCoefficientCLM q Lhist Rhist
  let scale := profile.paperPressureRowScale center q Lhist Rhist
  let operatorDeviation : PaperIndicatorRealAtomRow m → ℝ := fun a =>
    |Real.log (paperRealOperatorAffineRadius profile center M z a) -
      Real.log scale|
  let pressureDeviation : PaperIndicatorRealAtomRow m → ℝ := fun a =>
    |profile.paperIndicatorOpenPressure center z q
        (Function.update complexRows i
          (paperIndicatorComplexifyRealRow a)) - Real.log scale|
  have hscale' : 0 < operatorAffineScale (some center)
      profile.orderedResetWeight M := by
    simpa only [paperPressureRowScaleOfReal, complexRows, scale, M,
      paperPressureRowScale, Lhist, Rhist] using hscale
  have hop :=
    paper_real_iid_operatorAffine_absLog_L2
      profile hc₀ hsqrt center M z hscale' ν hL hν hνInt hνSecond
        theta htheta0 htheta1
  have hoperator (a : PaperIndicatorRealAtomRow m) :
      Matrix.toEuclideanCLM
          (n := ExteriorIndex (m + 1) q) (𝕜 := ℂ)
          (profile.paperIndicatorOpenExteriorProduct center z q
            (Function.update complexRows i
              (paperIndicatorComplexifyRealRow a))) =
        operatorAffine profile.orderedResetWeight
          (paperOperatorAffineAtoms m (fun j => (a j : ℂ))) M z
          (M (some center)) := by
    have h :=
      (profile.old_new_openExteriorProduct_eq_same_operatorAffine
        center z q complexRows i (paperIndicatorComplexifyRealRow a)).2
    rw [paperIndicatorOpenRowAtoms_complexifyReal_eq_paperOperatorAffineAtoms]
      at h
    simpa only [Lhist, Rhist, M] using h
  have hdeviation : operatorDeviation = pressureDeviation := by
    funext a
    dsimp only [operatorDeviation, pressureDeviation,
      paperRealOperatorAffineRadius, paperIndicatorOpenPressure]
    rw [← hoperator a, Matrix.l2_opNorm_toEuclideanCLM]
  have hpressureDeviation :
      (fun a : PaperIndicatorRealAtomRow m =>
        |profile.paperIndicatorOpenPressureOfReal center z q
            (Function.update rows i a) -
          Real.log (profile.paperPressureRowScaleOfReal center z q rows i)|) =
        pressureDeviation := by
    funext a
    simp only [paperIndicatorOpenPressureOfReal,
      paperIndicatorComplexifyRealRows_update,
      paperPressureRowScaleOfReal, pressureDeviation, complexRows,
      Lhist, Rhist, scale]
  have hfullDeviation :
      (fun a : PaperIndicatorRealAtomRow m =>
        |profile.paperIndicatorOpenPressureOfReal center z q
            (Function.update rows i a) -
          Real.log (profile.paperPressureRowScaleOfReal center z q rows i)|) =
        operatorDeviation :=
    hpressureDeviation.trans hdeviation.symm
  constructor
  · rw [hfullDeviation]
    simpa only [operatorDeviation, scale, M, Lhist, Rhist,
      paperPressureRowScale, paperIndicatorRealRowMeasure] using hop.2.1
  · simp_rw [congrFun hfullDeviation]
    simpa only [operatorDeviation, scale, M, Lhist, Rhist,
      paperPressureRowScale, paperIndicatorRealRowMeasure] using hop.2.2

/-- Scale-free wrapper for the real fresh-row fiber.  When the frozen
operator-affine scale is positive this is the preceding theorem.  When it is
zero, the deterministic operator norm bound and the exact leave-one-out
identity force every updated open product to have norm zero, so the pressure
deviation from `log 0` vanishes identically. -/
theorem real_paperIndicatorOpenPressure_fiber_memLp_two_and_integral_sq_all_scales
    {L : ℝ}
    (ν : Measure ℝ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorRealAtomRow m) (i : Fin n)
    (hνInt : Integrable (fun u : ℝ => u ^ 2) ν)
    (hνSecond : ∫ u : ℝ, u ^ 2 ∂ν = 1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    MemLp (fun a : PaperIndicatorRealAtomRow m =>
        |profile.paperIndicatorOpenPressureOfReal center z q
            (Function.update rows i a) -
          Real.log (profile.paperPressureRowScaleOfReal center z q rows i)|)
        2 (paperIndicatorRealRowMeasure m ν) ∧
      ∫ a : PaperIndicatorRealAtomRow m,
          |profile.paperIndicatorOpenPressureOfReal center z q
              (Function.update rows i a) -
            Real.log
              (profile.paperPressureRowScaleOfReal center z q rows i)| ^ 2
          ∂paperIndicatorRealRowMeasure m ν ≤
        2 * oneSidedLogSecondMomentBound
            ((4 * L) /
              (theta * Real.sqrt (c₀ / (m + 2 : ℝ)))) 1 +
          2 * (3 * (Real.log (m + 2 : ℝ)) ^ 2 + 3 +
            3 * ‖z‖ ^ 2) := by
  let complexRows := paperIndicatorComplexifyRealRows rows
  let Lhist := profile.paperPressureLeftHistory center z q complexRows i
  let Rhist := profile.paperPressureRightHistory center z q complexRows i
  let M := paperPressureFrozenCoefficientCLM q Lhist Rhist
  let scale := profile.paperPressureRowScale center q Lhist Rhist
  have hscaleEq : scale =
      profile.paperPressureRowScaleOfReal center z q rows i := by
    rfl
  by_cases hscalePos : 0 < scale
  · apply real_paperIndicatorOpenPressure_fiber_memLp_two_and_integral_sq
      ν hν hL profile hc₀ hsqrt center z q rows i
        (hscaleEq ▸ hscalePos) hνInt hνSecond theta htheta0 htheta1
  · have hscaleNonneg : 0 ≤ scale := by
      dsimp only [scale, paperPressureRowScale, M]
      exact (norm_nonneg (M (some center))).trans
        (distinguished_operator_norm_le_scale (some center)
          profile.orderedResetWeight M)
    have hscaleZero : scale = 0 :=
      le_antisymm (le_of_not_gt hscalePos) hscaleNonneg
    have hoperatorScaleZero :
        operatorAffineScale (some center) profile.orderedResetWeight M = 0 := by
      simpa only [scale, paperPressureRowScale] using hscaleZero
    have hoperator (a : PaperIndicatorRealAtomRow m) :
        Matrix.toEuclideanCLM
            (n := ExteriorIndex (m + 1) q) (𝕜 := ℂ)
            (profile.paperIndicatorOpenExteriorProduct center z q
              (Function.update complexRows i
                (paperIndicatorComplexifyRealRow a))) =
          operatorAffine profile.orderedResetWeight
            (paperOperatorAffineAtoms m (fun j => (a j : ℂ))) M z
            (M (some center)) := by
      have h :=
        (profile.old_new_openExteriorProduct_eq_same_operatorAffine
          center z q complexRows i (paperIndicatorComplexifyRealRow a)).2
      rw [paperIndicatorOpenRowAtoms_complexifyReal_eq_paperOperatorAffineAtoms]
        at h
      simpa only [Lhist, Rhist, M] using h
    have hoperatorNormZero (a : PaperIndicatorRealAtomRow m) :
        ‖operatorAffine profile.orderedResetWeight
          (paperOperatorAffineAtoms m (fun j => (a j : ℂ))) M z
          (M (some center))‖ = 0 := by
      have hle := operatorAffine_norm_le_scale_mul_sum
        (some center) profile.orderedResetWeight
        (paperOperatorAffineAtoms m (fun j => (a j : ℂ))) M z
      rw [hoperatorScaleZero, zero_mul] at hle
      exact le_antisymm hle (norm_nonneg _)
    have hproductNormZero (a : PaperIndicatorRealAtomRow m) :
        ‖profile.paperIndicatorOpenExteriorProduct center z q
          (Function.update complexRows i
            (paperIndicatorComplexifyRealRow a))‖ = 0 := by
      calc
        ‖profile.paperIndicatorOpenExteriorProduct center z q
            (Function.update complexRows i
              (paperIndicatorComplexifyRealRow a))‖ =
            ‖Matrix.toEuclideanCLM
              (n := ExteriorIndex (m + 1) q) (𝕜 := ℂ)
              (profile.paperIndicatorOpenExteriorProduct center z q
                (Function.update complexRows i
                  (paperIndicatorComplexifyRealRow a)))‖ := by
              rw [Matrix.l2_opNorm_toEuclideanCLM]
        _ = ‖operatorAffine profile.orderedResetWeight
              (paperOperatorAffineAtoms m (fun j => (a j : ℂ))) M z
              (M (some center))‖ := congrArg norm (hoperator a)
        _ = 0 := hoperatorNormZero a
    have hdeviationZero (a : PaperIndicatorRealAtomRow m) :
        |profile.paperIndicatorOpenPressureOfReal center z q
            (Function.update rows i a) -
          Real.log (profile.paperPressureRowScaleOfReal center z q rows i)| =
            0 := by
      rw [← hscaleEq, hscaleZero]
      simp only [paperIndicatorOpenPressureOfReal,
        paperIndicatorComplexifyRealRows_update,
        paperIndicatorOpenPressure, complexRows,
        hproductNormZero, Real.log_zero, sub_zero, abs_zero]
    constructor
    · simpa only [hdeviationZero] using
        (MemLp.zero' : MemLp
          (fun _ : PaperIndicatorRealAtomRow m => (0 : ℝ)) 2
          (paperIndicatorRealRowMeasure m ν))
    · have hbound0 : 0 ≤
          2 * oneSidedLogSecondMomentBound
              ((4 * L) /
                (theta * Real.sqrt (c₀ / (m + 2 : ℝ)))) 1 +
            2 * (3 * (Real.log (m + 2 : ℝ)) ^ 2 + 3 +
              3 * ‖z‖ ^ 2) := by
        unfold oneSidedLogSecondMomentBound
        positivity
      have hintegralZero :
          (∫ a : PaperIndicatorRealAtomRow m,
            |profile.paperIndicatorOpenPressureOfReal center z q
                (Function.update rows i a) -
              Real.log
                (profile.paperPressureRowScaleOfReal center z q rows i)| ^ 2
            ∂paperIndicatorRealRowMeasure m ν) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards with a
        rw [hdeviationZero a]
        norm_num
      rw [hintegralZero]
      exact hbound0

end PaperIndicatorWeights

end CircularLawSection4
