import CircularLawSections56.Section5.LiteralFreshMeanBound
import CircularLawSections56.Section5.BalancedPhysicalScaleAdapter

/-!
# Section 4 as an explicit completed input: the inverse-row boundary

Only the finite complementary-inverse norm inequality is a new Section 4
input.  Its logarithmic moments, pressure increment, telescope, finite maximum,
and balanced normalization are consequences, not additional assumptions.
-/

open scoped BigOperators ENNReal MeasureTheory Matrix Matrix.Norms.L2Operator
open MeasureTheory

noncomputable section

namespace CircularLawSections56.Section5

open CircularLawSection4 CircularLawSection4.PaperIndicatorWeights

def uniformInverseRowConstant (c₀ L : ℝ) (z : ℂ) : ℝ :=
  6 * ((3 * ‖z‖ + 3) + uniformFiberNegativeConstant c₀ L)

theorem uniformInverseRowConstant_nonneg (c₀ L : ℝ) (z : ℂ) :
    0 ≤ uniformInverseRowConstant c₀ L z := by
  have h := Real.log_nonneg (le_max_left 1 (Real.pi * L))
  unfold uniformInverseRowConstant uniformFiberNegativeConstant
  positivity

/-- Exact finite-dimensional input being granted when Section 4 is completed.
The denominator contains the two weighted edge atoms.  This predicate asserts
neither an expected row cost nor any asymptotic conclusion. -/
def Section4ComplementaryInverseInput
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : ℕ) {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1))
    (rows : Ω → PaperIndicatorAtomRow d) : Prop :=
  ∀ᵐ ω ∂μ,
    ‖(profile.paperIndicatorOpenExteriorRow center z q (rows ω))⁻¹‖ ≤
      profile.freshRowNormMajorant z (paperIndicatorOpenRowAtoms (rows ω)) /
        (‖profile.b 0 * rows ω 0‖ *
          ‖profile.b (Fin.last (d + 1)) * rows ω (Fin.last (d + 1))‖)

/-- IID is stronger than needed here: the individual row marginals suffice.
All four elementary logarithmic moments are discharged internally. -/
theorem literal_row_pressure_increment_of_section4_inverse
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d W : ℕ) (hW : 0 < W) (hd : d + 1 = 2 * W)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    {c₀ C₀ L : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀) (hL : 0 ≤ L) (hν : ComplexBallBound ν (ENNReal.ofReal L))
    (center : Fin (d + 1)) (z : ℂ) (q : ExteriorDegree (d + 1))
    (rows : Ω → PaperIndicatorAtomRow d) (hRows : Measurable rows)
    (hMarginal : ∀ s, MeasurePreserving (fun ω => rows ω s) μ ν)
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν ≤ 1)
    (P : Ω → Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hUnit : ∀ᵐ ω ∂μ, IsUnit (profile.paperIndicatorOpenExteriorRow center z q (rows ω)))
    (hBase : ∀ᵐ ω ∂μ, P ω ≠ 0)
    (hInverse : Section4ComplementaryInverseInput μ d profile center z q rows)
    (hExtendedInt : Integrable (fun ω =>
      Real.log ‖profile.paperIndicatorOpenExteriorRow center z q (rows ω) * P ω‖) μ)
    (hBaseInt : Integrable (fun ω => Real.log ‖P ω‖) μ) :
    |(∫ ω, Real.log ‖profile.paperIndicatorOpenExteriorRow center z q (rows ω) * P ω‖ ∂μ) -
      (∫ ω, Real.log ‖P ω‖ ∂μ)| ≤
      uniformInverseRowConstant c₀ L z * Real.log (Real.exp 1 * (W : ℝ)) := by
  let : Nonempty (ExteriorIndex (d + 1) q) := exteriorIndex_nonempty_bridge _ _
  have hcoord : ∀ ell,
      Integrable (fun ω => ‖paperIndicatorOpenRowAtoms (rows ω) ell‖ ^ 2) μ ∧
      ∫ ω, ‖paperIndicatorOpenRowAtoms (rows ω) ell‖ ^ 2 ∂μ ≤ 1 := by
    have hs : ∀ s, Integrable (fun ω => ‖rows ω s‖ ^ 2) μ ∧
        ∫ ω, ‖rows ω s‖ ^ 2 ∂μ ≤ 1 := fun s =>
      ⟨(hMarginal s).integrable_comp_of_integrable hInt,
        (integral_comp_measurePreserving_eq (hMarginal s) _ hInt).trans_le hSecond⟩
    intro ell
    cases ell with
    | none => exact hs _
    | some s => exact hs _
  have hmeas : ∀ ell, Measurable (fun ω => paperIndicatorOpenRowAtoms (rows ω) ell) := by
    intro ell
    cases ell with
    | none => exact (measurable_pi_apply _).comp hRows
    | some s => exact (measurable_pi_apply _).comp hRows
  have hf := positiveLog_paperIndicatorOpenExteriorRow_integrable_and_bound μ d profile hc₀
    center z q rows hRows hcoord
  have hg := positiveLog_freshRowMajorant_integrable_and_bound μ d profile hc₀ z
    (fun ω => paperIndicatorOpenRowAtoms (rows ω)) hmeas hcoord
  have he : ∀ s, Integrable (fun ω => negativeLog ‖profile.b s * rows ω s‖) μ ∧
      ∫ ω, negativeLog ‖profile.b s * rows ω s‖ ∂μ ≤
        uniformFiberNegativeConstant c₀ L * dimensionLogScale d := by
    intro s
    have h := negativeLog_weighted_atom_integrable_and_bound ν L hL hν d profile hc₀ s
    exact ⟨(hMarginal s).integrable_comp_of_integrable h.1,
      (integral_comp_measurePreserving_eq (hMarginal s) _ h.1).trans_le h.2⟩
  have hzero : ∀ᵐ u : ℂ ∂ν, u ≠ 0 := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using
      measure_singleton_zero_eq_zero_of_complexBallBound hν
  have hp : ∀ s, ∀ᵐ ω ∂μ, 0 < ‖profile.b s * rows ω s‖ := by
    intro s
    filter_upwards [(hMarginal s).quasiMeasurePreserving.ae hzero] with ω hω
    exact norm_pos_iff.2 (mul_ne_zero (profile.b_ne_zero hc₀ s) hω)
  have h := (expected_matrix_row_increment_le_complementary μ
    (fun ω => profile.paperIndicatorOpenExteriorRow center z q (rows ω)) P
    (fun ω => profile.freshRowNormMajorant z (paperIndicatorOpenRowAtoms (rows ω)))
    (fun ω => ‖profile.b 0 * rows ω 0‖)
    (fun ω => ‖profile.b (Fin.last (d + 1)) * rows ω (Fin.last (d + 1))‖)
    hUnit hBase (hp 0) (hp _) hInverse hExtendedInt hBaseInt
    hf.1 hg.1 (he 0).1 (he _).1 _ _ _ _ hf.2 hg.2 (he 0).2 (he _).2).2
  apply h.trans
  have hH := dimensionLogScale_le_logEW d W hW hd
  have hB := Real.log_nonneg (le_max_left 1 (Real.pi * L))
  have hC : 0 ≤ 2 * ((3 * ‖z‖ + 3) + uniformFiberNegativeConstant c₀ L) := by
    unfold uniformFiberNegativeConstant
    positivity
  have hmul := mul_le_mul_of_nonneg_left hH hC
  dsimp only [uniformInverseRowConstant]
  nlinarith only [hmul]

/-- Taking the maximum after the degreewise telescope does not introduce the
number of exterior degrees into the constant. -/
theorem finite_pressure_terminal_remainder
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (pressure : ι → ℕ → ℝ) (steps : ℕ) (cost : ℝ)
    (hStep : ∀ r, ∀ j < steps, |pressure r (j + 1) - pressure r j| ≤ cost) :
    |finiteSignedMax Finset.univ Finset.univ_nonempty (fun r => pressure r steps) -
      finiteSignedMax Finset.univ Finset.univ_nonempty (fun r => pressure r 0)| ≤
      (steps : ℝ) * cost := by
  apply abs_finiteSignedMax_sub_le Finset.univ_nonempty
  intro r _
  exact uniform_step_cost_telescope (pressure r) steps cost (hStep r)

/-- Final normalized receiver form, now derived from single-row increments. -/
theorem balanced_pressure_remainder_of_row_increments
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (δ : ℝ) (W N : ℕ → ℕ) (n : ℕ)
    (hW : 0 < W n) (hm0 : 0 < paperMesoscopicCellLength δ W n)
    (hReserve : 2 * W n ≤ N n)
    (hFit : 2 * paperMesoscopicCellLength δ W n ≤ N n - 2 * W n)
    (pressure : ι → ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hStep : ∀ r, ∀ j < balancedCellRemainder (N n - 2 * W n)
        (paperMesoscopicCellLength δ W n),
      |pressure r (j + 1) - pressure r j| ≤ C * paperLogEW W n) :
    |finiteSignedMax Finset.univ Finset.univ_nonempty
        (fun r => pressure r (balancedCellRemainder (N n - 2 * W n)
          (paperMesoscopicCellLength δ W n))) / (N n : ℝ) -
      balancedPhysicalLengthRatio (N n) (W n) (paperMesoscopicCellLength δ W n) *
        (finiteSignedMax Finset.univ Finset.univ_nonempty (fun r => pressure r 0) /
          ((balancedCellCount (N n - 2 * W n) (paperMesoscopicCellLength δ W n) *
            balancedCellLength (N n - 2 * W n) (paperMesoscopicCellLength δ W n) : ℕ) : ℝ))| ≤
      C * paperBalancedRemainderRate δ W n := by
  apply balanced_physical_normalized_remainder_le_paperRate δ W N n hW hm0 hReserve hFit _ _ C hC
  simpa only [mul_assoc] using finite_pressure_terminal_remainder pressure _
    (C * paperLogEW W n) hStep

end CircularLawSections56.Section5
