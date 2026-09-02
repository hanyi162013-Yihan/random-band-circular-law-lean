import CircularLawSections56.Section5.LiteralPhysicalMesoscopicCellAdapter
import CircularLawSections56.Section5.LiteralPressureAdapter

/-!
# Physical pressure fluctuations under a sample restriction

A restriction to outside rows is generally not injective.  This module transports
both coordinate means and the maximum centered fluctuation along any measure-preserving
restriction, including almost-everywhere identifications of the pressure observables.
The literal complex-row corollary derives the `MemLp` and maximal-bound fields used by
the final assembly directly from Section 4.
-/

open scoped ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

private theorem pressureFluctuation_integral_comp
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B}
    (hf : MeasurePreserving f μ ν) (g : B → ℝ) (hg : Integrable g ν) :
    (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  have hgMap : AEStronglyMeasurable g (Measure.map f μ) := by
    rw [hf.map_eq]
    exact hg.aestronglyMeasurable
  calc
    _ = ∫ y, g y ∂Measure.map f μ :=
      (integral_map hf.measurable.aemeasurable hgMap).symm
    _ = _ := by rw [hf.map_eq]

/-- A noninjective measure-preserving restriction preserves the centered maximal
fluctuation.  Coordinate expectations and `L²` membership are derived, not assumed. -/
theorem pressure_memLp_and_maxCenteredAbs_of_restriction
    {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Fintype ι] [Nonempty ι]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (restriction : A → B) (hRestriction : MeasurePreserving restriction μ ν)
    (Y : ι → B → ℝ) (Z : ι → A → ℝ)
    (hY : ∀ i, MemLp (Y i) 2 ν)
    (hZ : ∀ i, Z i =ᵐ[μ] (Y i ∘ restriction)) :
    (∀ i, MemLp (Z i) 2 μ) ∧
      (∫ x, maxCenteredAbs μ Z x ∂μ) = ∫ y, maxCenteredAbs ν Y y ∂ν := by
  have hMean (i : ι) : (∫ x, Z i x ∂μ) = ∫ y, Y i y ∂ν := by
    calc
      _ = ∫ x, Y i (restriction x) ∂μ := integral_congr_ae (hZ i)
      _ = _ := pressureFluctuation_integral_comp hRestriction (Y i)
        ((hY i).integrable (by norm_num))
  have hMax : maxCenteredAbs μ Z =ᵐ[μ] (maxCenteredAbs ν Y ∘ restriction) := by
    filter_upwards [ae_all_iff.mpr hZ] with x hx
    unfold maxCenteredAbs
    apply congrArg finiteMaxAbs
    funext i
    simp only [centered, Function.comp_apply, hx i, hMean i]
  refine ⟨fun i => (memLp_congr_ae (hZ i)).2
    ((hY i).comp_measurePreserving hRestriction), ?_⟩
  calc
    _ = ∫ x, maxCenteredAbs ν Y (restriction x) ∂μ := integral_congr_ae hMax
    _ = _ := pressureFluctuation_integral_comp hRestriction (maxCenteredAbs ν Y)
      ((memLp_maxCenteredAbs hY).integrable (by norm_num))

/-- Section 4 supplies both finite pressure inputs on the actual outside-row
restriction.  The source can be the full matrix sample space or any common triangular
sample space.  The only observable input is its almost-everywhere identification.
All outside lengths are allowed: the empty block has constant pressure and exactly
zero centered fluctuation. -/
theorem complex_literalPhysicalPressure_restriction_inputs
    {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (d ell : ℕ) {c₀ C₀ L : ℝ}
    (ν : Measure ℂ) [SigmaFinite ν] [IsProbabilityMeasure ν]
    (hν : ComplexBallBound ν (ENNReal.ofReal L)) (hL : 0 ≤ L)
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hsqrt : Real.sqrt (c₀ / (d + 2 : ℝ)) ≤ 1)
    (center : Fin (d + 1)) (z : ℂ)
    (restriction : A → LiteralPhysicalOutsideRows ell d)
    (hRestriction : MeasurePreserving restriction μ
      (paperIndicatorOpenRowSampleMeasure ell d ν))
    (Z : ExteriorDegree (d + 1) → A → ℝ)
    (hZ : ∀ i, Z i =ᵐ[μ]
      (profile.paperIndicatorOpenPressure center z i ∘ restriction))
    (hsecondInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hsecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1) :
    (∀ i, MemLp (Z i) 2 μ) ∧
      (∫ x, maxCenteredAbs μ Z x ∂μ) ≤
        Real.sqrt ((d + 2 : ℝ) *
          (2 * (ell : ℝ) * complexPaperPressureFiberL2Bound d c₀ L z)) := by
  let νRows := paperIndicatorOpenRowSampleMeasure ell d ν
  let : IsProbabilityMeasure νRows := by
    dsimp only [νRows, paperIndicatorOpenRowSampleMeasure, paperIndicatorRowMeasure]
    let : IsProbabilityMeasure (iidMeasure ν (d + 2)) := iidMeasure_isProbability ν (d + 2)
    exact iidMeasure_isProbability (iidMeasure ν (d + 2)) ell
  have hY : ∀ i, MemLp
      (profile.paperIndicatorOpenPressure center z i) 2 νRows := by
    intro i
    cases ell with
    | zero =>
        change MemLp (fun _ : Fin 0 → PaperIndicatorAtomRow d =>
          Real.log ‖(1 : Matrix (ExteriorIndex (d + 1) i)
            (ExteriorIndex (d + 1) i) ℂ)‖) 2 νRows
        exact memLp_const _
    | succ n =>
        exact profile.complex_paperIndicatorOpenPressure_memLp_two
          (n := n) ν hν hL hc₀ hsqrt center z i hsecondInt hsecond
  have hTransport := pressure_memLp_and_maxCenteredAbs_of_restriction μ νRows
    restriction hRestriction (fun i => profile.paperIndicatorOpenPressure center z i)
    Z hY hZ
  refine ⟨hTransport.1, ?_⟩
  rw [hTransport.2]
  cases ell with
  | zero =>
      have hmax : maxCenteredAbs νRows
          (fun i => profile.paperIndicatorOpenPressure center z i) =
          (fun _ : Fin 0 → PaperIndicatorAtomRow d => 0) := by
        funext rows
        simp [maxCenteredAbs, centered, paperIndicatorOpenPressure,
          paperIndicatorOpenExteriorProduct, finiteMaxAbs]
      rw [hmax]
      simp
  | succ n =>
      simpa only [νRows, Nat.cast_add, Nat.cast_one] using
        profile.integral_max_complex_paperIndicatorOpenPressure_le_auto
          (n := n) ν hν hL hc₀ hsqrt center z hsecondInt hsecond

end CircularLawSections56.Section5
