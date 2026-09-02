import CircularLawSection4.PaperOperatorAffineL2
import CircularLawSection4.PaperPressureLeaveOneOut

/-!
# Complex row-fiber `L²` bound for the paper pressure

After every row except one is frozen, the complete updated open pressure is
exactly the norm logarithm of the paper-profile operator-affine expression.
This module inserts the frozen left and right histories into
`complex_paperIndicator_operatorAffine_memLp_two_and_integral_sq` and states
the result on the literal IID row fiber used by leave-one-out resampling.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSection4

open Matrix Set Set.powersetCard

namespace PaperIndicatorWeights

variable {m n : ℕ} {c₀ C₀ : ℝ}

/-- The row-slot enumeration used by the pressure observable is the same
canonical reset-label enumeration used by the operator-affine IID theorem. -/
theorem paperIndicatorOpenRowAtoms_eq_paperOperatorAffineAtoms
    (row : PaperIndicatorAtomRow m) :
    paperIndicatorOpenRowAtoms row = paperOperatorAffineAtoms m row := by
  funext ell
  cases ell with
  | none =>
      simp [paperIndicatorOpenRowAtoms, paperOperatorAffineAtoms,
        paperOperatorAffineLabelEquiv]
  | some j =>
      simp [paperIndicatorOpenRowAtoms, paperOperatorAffineAtoms,
        paperOperatorAffineLabelEquiv]

/-- With the outside rows frozen, a fresh complex IID row has an explicit
`L²` logarithmic deviation bound for the *complete* updated open pressure.

The reference scale depends only on the frozen histories, hence is common
to every row in this fiber.  The bound is exactly the indicator-profile
operator-affine bound: the negative term records the bounded-density and
profile loss, while the positive term records the normalized row second
moment. -/
theorem complex_paperIndicatorOpenPressure_fiber_memLp_two_and_integral_sq
    {L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorAtomRow m) (i : Fin n)
    (hscale : 0 < profile.paperPressureRowScale center q
      (profile.paperPressureLeftHistory center z q rows i)
      (profile.paperPressureRightHistory center z q rows i))
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    MemLp (fun a : PaperIndicatorAtomRow m =>
        |profile.paperIndicatorOpenPressure center z q
            (Function.update rows i a) -
          Real.log (profile.paperPressureRowScale center q
            (profile.paperPressureLeftHistory center z q rows i)
            (profile.paperPressureRightHistory center z q rows i))|)
        2 (paperIndicatorRowMeasure m ν) ∧
      ∫ a : PaperIndicatorAtomRow m,
          |profile.paperIndicatorOpenPressure center z q
              (Function.update rows i a) -
            Real.log (profile.paperPressureRowScale center q
              (profile.paperPressureLeftHistory center z q rows i)
              (profile.paperPressureRightHistory center z q rows i))| ^ 2
          ∂paperIndicatorRowMeasure m ν ≤
        2 * oneSidedLogSecondMomentBound
            ((max 1 (Real.pi * L)) /
              ((1 / 2 : ℝ) * Real.sqrt (c₀ / (m + 2 : ℝ)))) 1 +
          2 * (3 * (Real.log (m + 2 : ℝ)) ^ 2 + 3 * 1 +
            3 * ‖z‖ ^ 2) := by
  let Lhist := profile.paperPressureLeftHistory center z q rows i
  let Rhist := profile.paperPressureRightHistory center z q rows i
  let M := paperPressureFrozenCoefficientCLM q Lhist Rhist
  let scale := profile.paperPressureRowScale center q Lhist Rhist
  let operatorDeviation : PaperIndicatorAtomRow m → ℝ := fun a =>
    |Real.log ‖operatorAffine profile.orderedResetWeight
        (paperOperatorAffineAtoms m a) M z (M (some center))‖ -
      Real.log scale|
  let pressureDeviation : PaperIndicatorAtomRow m → ℝ := fun a =>
    |profile.paperIndicatorOpenPressure center z q
        (Function.update rows i a) - Real.log scale|
  have hscale' : 0 < operatorAffineScale (some center)
      profile.orderedResetWeight M := by
    simpa only [scale, M, paperPressureRowScale, Lhist, Rhist] using hscale
  have hop :=
    complex_paperIndicator_operatorAffine_memLp_two_and_integral_sq
      ν hν hL profile hc₀ hsqrt center M z hscale' hνInt hνSecond
  have hoperator (a : PaperIndicatorAtomRow m) :
      Matrix.toEuclideanCLM
          (n := ExteriorIndex (m + 1) q) (𝕜 := ℂ)
          (profile.paperIndicatorOpenExteriorProduct center z q
            (Function.update rows i a)) =
        operatorAffine profile.orderedResetWeight
          (paperOperatorAffineAtoms m a) M z (M (some center)) := by
    have h :=
      (profile.old_new_openExteriorProduct_eq_same_operatorAffine
        center z q rows i a).2
    rw [paperIndicatorOpenRowAtoms_eq_paperOperatorAffineAtoms] at h
    simpa only [Lhist, Rhist, M] using h
  have hdeviation : operatorDeviation = pressureDeviation := by
    funext a
    dsimp only [operatorDeviation, pressureDeviation,
      paperIndicatorOpenPressure]
    rw [← hoperator a, Matrix.l2_opNorm_toEuclideanCLM]
  change MemLp pressureDeviation 2 (paperIndicatorRowMeasure m ν) ∧
    (∫ a : PaperIndicatorAtomRow m, pressureDeviation a ^ 2
      ∂paperIndicatorRowMeasure m ν) ≤ _
  rw [← hdeviation]
  simpa only [paperIndicatorRowMeasure, operatorDeviation, scale, M,
    Lhist, Rhist, paperPressureRowScale] using hop

/-- Scale-free complex fresh-row fiber bound.  At positive frozen scale this
is the preceding theorem.  At scale zero, the deterministic operator-affine
norm bound forces every fresh evaluation to vanish; the leave-one-out
identity then forces the complete updated open-product norm to vanish as
well, so its deviation from `log 0` is identically zero. -/
theorem complex_paperIndicatorOpenPressure_fiber_memLp_two_and_integral_sq_all_scales
    {L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (m + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (hsqrt : Real.sqrt (c₀ / (m + 2 : ℝ)) ≤ 1)
    (center : Fin (m + 1)) (z : ℂ)
    (q : ExteriorDegree (m + 1))
    (rows : Fin n → PaperIndicatorAtomRow m) (i : Fin n)
    (hνInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hνSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    MemLp (fun a : PaperIndicatorAtomRow m =>
        |profile.paperIndicatorOpenPressure center z q
            (Function.update rows i a) -
          Real.log (profile.paperPressureRowScale center q
            (profile.paperPressureLeftHistory center z q rows i)
            (profile.paperPressureRightHistory center z q rows i))|)
        2 (paperIndicatorRowMeasure m ν) ∧
      ∫ a : PaperIndicatorAtomRow m,
          |profile.paperIndicatorOpenPressure center z q
              (Function.update rows i a) -
            Real.log (profile.paperPressureRowScale center q
              (profile.paperPressureLeftHistory center z q rows i)
              (profile.paperPressureRightHistory center z q rows i))| ^ 2
          ∂paperIndicatorRowMeasure m ν ≤
        2 * oneSidedLogSecondMomentBound
            ((max 1 (Real.pi * L)) /
              ((1 / 2 : ℝ) * Real.sqrt (c₀ / (m + 2 : ℝ)))) 1 +
          2 * (3 * (Real.log (m + 2 : ℝ)) ^ 2 + 3 * 1 +
            3 * ‖z‖ ^ 2) := by
  let Lhist := profile.paperPressureLeftHistory center z q rows i
  let Rhist := profile.paperPressureRightHistory center z q rows i
  let M := paperPressureFrozenCoefficientCLM q Lhist Rhist
  let scale := profile.paperPressureRowScale center q Lhist Rhist
  letI : IsProbabilityMeasure (paperIndicatorRowMeasure m ν) :=
    iidMeasure_isProbability ν (m + 2)
  have hscaleEq : scale =
      profile.paperPressureRowScale center q
        (profile.paperPressureLeftHistory center z q rows i)
        (profile.paperPressureRightHistory center z q rows i) := by
    rfl
  by_cases hscalePos : 0 < scale
  · apply complex_paperIndicatorOpenPressure_fiber_memLp_two_and_integral_sq
      ν hν hL profile hc₀ hsqrt center z q rows i
        (hscaleEq ▸ hscalePos) hνInt hνSecond
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
    have hoperator (a : PaperIndicatorAtomRow m) :
        Matrix.toEuclideanCLM
            (n := ExteriorIndex (m + 1) q) (𝕜 := ℂ)
            (profile.paperIndicatorOpenExteriorProduct center z q
              (Function.update rows i a)) =
          operatorAffine profile.orderedResetWeight
            (paperOperatorAffineAtoms m a) M z (M (some center)) := by
      have h :=
        (profile.old_new_openExteriorProduct_eq_same_operatorAffine
          center z q rows i a).2
      rw [paperIndicatorOpenRowAtoms_eq_paperOperatorAffineAtoms] at h
      simpa only [Lhist, Rhist, M] using h
    have hoperatorNormZero (a : PaperIndicatorAtomRow m) :
        ‖operatorAffine profile.orderedResetWeight
          (paperOperatorAffineAtoms m a) M z (M (some center))‖ = 0 := by
      have hle := operatorAffine_norm_le_scale_mul_sum
        (some center) profile.orderedResetWeight
        (paperOperatorAffineAtoms m a) M z
      rw [hoperatorScaleZero, zero_mul] at hle
      exact le_antisymm hle (norm_nonneg _)
    have hproductNormZero (a : PaperIndicatorAtomRow m) :
        ‖profile.paperIndicatorOpenExteriorProduct center z q
          (Function.update rows i a)‖ = 0 := by
      calc
        ‖profile.paperIndicatorOpenExteriorProduct center z q
            (Function.update rows i a)‖ =
            ‖Matrix.toEuclideanCLM
              (n := ExteriorIndex (m + 1) q) (𝕜 := ℂ)
              (profile.paperIndicatorOpenExteriorProduct center z q
                (Function.update rows i a))‖ := by
              rw [Matrix.l2_opNorm_toEuclideanCLM]
        _ = ‖operatorAffine profile.orderedResetWeight
              (paperOperatorAffineAtoms m a) M z (M (some center))‖ :=
          congrArg norm (hoperator a)
        _ = 0 := hoperatorNormZero a
    have hdeviationZero (a : PaperIndicatorAtomRow m) :
        |profile.paperIndicatorOpenPressure center z q
            (Function.update rows i a) -
          Real.log (profile.paperPressureRowScale center q
            (profile.paperPressureLeftHistory center z q rows i)
            (profile.paperPressureRightHistory center z q rows i))| = 0 := by
      rw [← hscaleEq, hscaleZero]
      simp only [paperIndicatorOpenPressure, hproductNormZero,
        Real.log_zero, sub_zero, abs_zero]
    constructor
    · simpa only [hdeviationZero] using
        (memLp_const (0 : ℝ) : MemLp
          (fun _ : PaperIndicatorAtomRow m => (0 : ℝ)) 2
          (paperIndicatorRowMeasure m ν))
    · have hintegrand :
          (fun a : PaperIndicatorAtomRow m =>
            |profile.paperIndicatorOpenPressure center z q
                (Function.update rows i a) -
              Real.log (profile.paperPressureRowScale center q
                (profile.paperPressureLeftHistory center z q rows i)
                (profile.paperPressureRightHistory center z q rows i))| ^ 2) =
            (fun _ : PaperIndicatorAtomRow m => (0 : ℝ)) := by
          funext a
          rw [hdeviationZero a]
          norm_num
      rw [hintegrand, integral_zero]
      unfold oneSidedLogSecondMomentBound
      positivity

end PaperIndicatorWeights

end CircularLawSection4
