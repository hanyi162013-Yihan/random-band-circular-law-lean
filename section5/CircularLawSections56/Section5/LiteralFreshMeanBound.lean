import CircularLawSections56.Section5.LiteralRowLogMoments

/-!
# The missing fresh-cell mean bound

The fresh mean in the centered physical telescope is bounded here, not supplied
as an input.  Only the already proved Section 4 integrability theorem is used.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

/-- Integral transport along a restriction, including noninjective restrictions. -/
theorem integral_comp_measurePreserving_eq
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} {f : Ω → Ξ}
    (hf : MeasurePreserving f μ ν) (g : Ξ → ℝ) (hg : Integrable g ν) :
    (∫ ω, g (f ω) ∂μ) = ∫ x, g x ∂ν := by
  have hm : AEStronglyMeasurable g (Measure.map f μ) := by
    rw [hf.map_eq]
    exact hg.aestronglyMeasurable
  rw [← integral_map hf.measurable.aemeasurable hm, hf.map_eq]

theorem log_norm_chronologicalProduct_le_sum_positiveLog
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (xs : List (Matrix ι ι ℂ)) :
    Real.log ‖chronologicalProduct xs‖ ≤ (xs.map (fun A => positiveLog ‖A‖)).sum := by
  have h : positiveLog ‖chronologicalProduct xs‖ ≤
      (xs.map (fun A => positiveLog ‖A‖)).sum := by
    induction xs with
    | nil => simp [chronologicalProduct, positiveLog]
    | cons A xs ih =>
      rw [chronologicalProduct_cons, List.map_cons, List.sum_cons]
      have hm : positiveLog ‖chronologicalProduct xs * A‖ ≤
          positiveLog (‖chronologicalProduct xs‖ * ‖A‖) :=
        Real.monotoneOn_posLog (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (norm_mul_le _ _)
      have hp := Real.posLog_mul (x := ‖chronologicalProduct xs‖) (y := ‖A‖)
      change positiveLog (_ * _) ≤ positiveLog _ + positiveLog _ at hp
      linarith
  exact (le_max_right _ _).trans h

theorem literalPaperExteriorCell_mean_le_uniform
    (d : ℕ) (ν : Measure ℂ) [IsProbabilityMeasure ν]
    {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (hL : 0 ≤ L) (hν : ComplexBallBound ν (ENNReal.ofReal L))
    (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1))
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    (∫ ω, Real.log ‖literalPaperExteriorCell profile center z q ω‖
      ∂literalPaperExteriorCellMeasure d ν) ≤
      (d + 1 : ℝ) * ((3 * ‖z‖ + 3) * dimensionLogScale d) := by
  classical
  let μ := literalPaperExteriorCellMeasure d ν
  let : IsProbabilityMeasure μ := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ : FreshAtomIndex (d + 1) => ν)))
  let : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty_bridge _ _
  let cost := fun (t : Fin (d + 1)) (ω : LiteralPaperCellAtoms d) =>
    positiveLog ‖profile.paperIndicatorOpenExteriorRow center z q (literalPaperCellRows ω t)‖
  have hcost : ∀ t, Integrable (cost t) μ ∧ ∫ ω, cost t ω ∂μ ≤
      (3 * ‖z‖ + 3) * dimensionLogScale d := by
    intro t
    apply positiveLog_paperIndicatorOpenExteriorRow_integrable_and_bound
      μ d profile hc₀ center z q (fun ω => literalPaperCellRows ω t)
    · exact measurable_pi_lambda _ (fun k => measurable_pi_apply _)
    · intro ell
      simp only [paperIndicatorOpenRowAtoms_literalPaperCellRows]
      have hmp := measurePreserving_eval (fun _ : FreshAtomIndex (d + 1) => ν) (t, ell)
      exact ⟨hmp.integrable_comp_of_integrable hInt,
        (integral_comp_measurePreserving_eq hmp _ hInt).trans_le hSecond⟩
  have hsum : Integrable (fun ω => ∑ t, cost t ω) μ :=
    integrable_finsetSum _ (fun t _ => (hcost t).1)
  have hcell := complex_literalPaperExteriorCell_logOpNorm_integrable
    ν hν hL profile hc₀ hsqrt center z q hInt hSecond
  have hdom : ∀ ω, Real.log ‖literalPaperExteriorCell profile center z q ω‖ ≤ ∑ t, cost t ω := by
    intro ω
    have h := log_norm_chronologicalProduct_le_sum_positiveLog
      (List.ofFn (fun t : Fin (d + 1) =>
        profile.paperIndicatorOpenExteriorRow center z q (literalPaperCellRows ω t)))
    simpa only [literalPaperExteriorCell, paperIndicatorOpenExteriorProduct,
      List.map_ofFn, List.sum_ofFn, Function.comp_apply, cost] using h
  calc
    _ ≤ ∫ ω, ∑ t, cost t ω ∂μ := integral_mono_ae hcell hsum (ae_of_all _ hdom)
    _ = ∑ t, ∫ ω, cost t ω ∂μ := integral_finsetSum _ (fun t _ => (hcost t).1)
    _ ≤ ∑ _t : Fin (d + 1), (3 * ‖z‖ + 3) * dimensionLogScale d :=
      Finset.sum_le_sum (fun t _ => (hcost t).2)
    _ = _ := by simp

/-- The exact maximum defining the physical cell error has one fixed constant,
uniform over every exterior degree. -/
theorem literalPhysicalCellError_le_uniform_logEW
    (d W : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (hL : 0 ≤ L) (hν : ComplexBallBound ν (ENNReal.ofReal L))
    (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1))
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    max (complexLiteralProjectiveCellLoss d c₀ L q)
      (∫ ω, Real.log ‖literalPaperExteriorCell profile center z q ω‖
        ∂literalPaperExteriorCellMeasure d ν) ≤
      uniformLiteralConstant c₀ L z * ((W : ℝ) * Real.log (Real.exp 1 * (W : ℝ))) := by
  have hH := le_trans zero_le_one (one_le_dimensionLogScale d)
  have hB := Real.log_nonneg (le_max_left 1 (Real.pi * L))
  have hC := uniformRawSeamConstant_nonneg c₀ L z
  have hD : (0 : ℝ) ≤ d + 1 := by positivity
  have hraw : max (complexLiteralProjectiveCellLoss d c₀ L q)
      (∫ ω, Real.log ‖literalPaperExteriorCell profile center z q ω‖
        ∂literalPaperExteriorCellMeasure d ν) ≤
      uniformRawSeamConstant c₀ L z * (d + 1 : ℝ) * dimensionLogScale d := by
    apply max_le
    · apply (complexLiteralProjectiveCellLoss_le_uniform d c₀ L hc₀ q).trans
      apply mul_le_mul_of_nonneg_right _ hH
      apply mul_le_mul_of_nonneg_right _ hD
      unfold uniformRawSeamConstant uniformFreshPositiveConstant
      linarith [norm_nonneg z]
    · apply (literalPaperExteriorCell_mean_le_uniform d ν profile hc₀ hsqrt hL hν
        center z q hInt hSecond).trans
      have hc : 3 * ‖z‖ + 3 ≤ uniformRawSeamConstant c₀ L z := by
        unfold uniformRawSeamConstant uniformCoefficientConstant uniformFreshNegativeConstant
          uniformFreshPositiveConstant
        linarith [abs_nonneg (Real.log c₀), norm_nonneg z]
      nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hD) hH]
  have hlog := dimensionLogScale_le_logEW d W hW hd
  have hd' : (d : ℝ) + 1 = 2 * (W : ℝ) := by exact_mod_cast hd
  have hlog0 : 0 ≤ Real.log (Real.exp 1 * (W : ℝ)) := by linarith
  have hconst : 6 * uniformRawSeamConstant c₀ L z ≤ uniformLiteralConstant c₀ L z := by
    unfold uniformLiteralConstant uniformFiberSquareConstant
    nlinarith [sq_nonneg (uniformFiberNegativeConstant c₀ L + 1), sq_nonneg (3 * ‖z‖ + 3)]
  apply hraw.trans
  calc
    _ ≤ 6 * uniformRawSeamConstant c₀ L z *
        ((W : ℝ) * Real.log (Real.exp 1 * (W : ℝ))) := by
      have h := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC hD)
      rw [hd'] at h ⊢
      nlinarith only [h]
    _ ≤ _ := mul_le_mul_of_nonneg_right hconst (mul_nonneg (Nat.cast_nonneg _) hlog0)

end CircularLawSections56.Section5
