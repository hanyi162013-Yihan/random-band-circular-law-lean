import BernoulliSection10.FinitePressure
import BernoulliSection10.AsymptoticScales
import BernoulliSection10Complex.RowConcentration

/-!
# Concrete core pressures and their concentration comparison

The pressure in (10.31) is the expectation under the literal independent
physical-row law. Its optimizing degree is the least maximizer, chosen
internally as in (10.36). The comparison of a random degree maximum with
the deterministic maximum of the expectations pays concentration once
for the whole interval, not once per degree or per cell.
-/

open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection10Complex

open BernoulliSection10

section FiniteMax

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

theorem measurable_finitePressureMax {X : Fin (d + 1) → Ω → ℝ}
    (hX : ∀ r, Measurable (X r)) :
    Measurable (fun x => finitePressureMax (fun r => X r x)) := by
  have h := Finset.measurable_sup' (s := Finset.univ) Finset.univ_nonempty
    (fun r _ => hX r)
  have heq : (fun x => finitePressureMax (fun r => X r x)) =
      Finset.univ.sup' Finset.univ_nonempty X := by
    funext x
    exact (Finset.sup'_apply Finset.univ_nonempty X x).symm
  rw [heq]
  exact h

theorem integrable_finitePressureMax {ν : Measure Ω}
    {X : Fin (d + 1) → Ω → ℝ}
    (hX : ∀ r, Measurable (X r)) (hXi : ∀ r, Integrable (X r) ν) :
    Integrable (fun x => finitePressureMax (fun r => X r x)) ν := by
  have hi := integrable_finsetSum Finset.univ (fun r _ => (hXi r).abs)
  apply hi.mono' (measurable_finitePressureMax hX).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  obtain ⟨r, hr⟩ := finitePressureMax_attained (fun r => X r x)
  rw [Real.norm_eq_abs, ← hr]
  exact Finset.single_le_sum (fun s _ => abs_nonneg (X s x)) (Finset.mem_univ r)

theorem finitePressureMax_sub_meanMax_le
    (ν : Measure Ω) (X : Fin (d + 1) → Ω → ℝ) (x : Ω) :
    |finitePressureMax (fun r => X r x) -
      finitePressureMax (fun r => ∫ y, X r y ∂ν)| ≤
        maxCenteredDeviation X ν x := by
  apply abs_finitePressureMax_sub_le
  intro r
  exact le_finitePressureMax (fun s => |X s x - ∫ y, X s y ∂ν|) r

end FiniteMax

def intervalPressure (μ : Measure ℂ) (W s : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) : ℝ :=
  ∫ x, intervalDegreeLog W s z r x ∂intervalRowsLaw W s μ

def intervalMaxDegreeLog (W s : ℕ) (z : ℂ) (x : IntervalRows W s) : ℝ :=
  finitePressureMax (fun r => intervalDegreeLog W s z r x)

def intervalMaxPressure (μ : Measure ℂ) (W s : ℕ) (z : ℂ) : ℝ :=
  finitePressureMax (intervalPressure μ W s z)

def densityCorePressure (μ : Measure ℂ) (W : ℕ) (z : ℂ)
    (r : Fin (2 * W + 1)) : ℝ :=
  intervalPressure μ W (densityCoreSites W) z r

def densityMaxCorePressure (μ : Measure ℂ) (W : ℕ) (z : ℂ) : ℝ :=
  finitePressureMax (densityCorePressure μ W z)

def densityOptimizingDegree (μ : Measure ℂ) (W : ℕ) (z : ℂ) : Fin (2 * W + 1) :=
  pressureOptimizingDegree (densityCorePressure μ W z)

theorem densityOptimizingDegree_maximizes (μ : Measure ℂ) (W : ℕ) (z : ℂ) :
    densityCorePressure μ W z (densityOptimizingDegree μ W z) =
      densityMaxCorePressure μ W z :=
  pressureOptimizingDegree_maximizes (densityCorePressure μ W z)

theorem densityOptimizingDegree_minimal (μ : Measure ℂ) (W : ℕ) (z : ℂ)
    {r : Fin (2 * W + 1)}
    (hr : densityCorePressure μ W z r = densityMaxCorePressure μ W z) :
    densityOptimizingDegree μ W z ≤ r :=
  pressureOptimizingDegree_le _ hr

theorem intervalDegreeLog_integrable
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) (r : Fin (2 * W + 1)) :
    Integrable (intervalDegreeLog W s z r) (intervalRowsLaw W s μ) := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W s μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  exact (intervalDegreeLog_memLp_two hμ W s hW z r).integrable one_le_two

theorem intervalMaxDegreeLog_integrable
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    Integrable (intervalMaxDegreeLog W s z) (intervalRowsLaw W s μ) :=
  integrable_finitePressureMax (fun r => measurable_intervalDegreeLog W s z r)
    (fun r => intervalDegreeLog_integrable hμ W s hW z r)

/-- A literal real bound for the simultaneous concentration cost. -/
def intervalPressureConcentrationCost (L : ℝ) (W s : ℕ) : ℝ :=
  Real.sqrt (((2 * W + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) *
    ((s * W : ℕ) : ℝ) * physicalRowResamplingEnergy W L)

/-- The random maximum differs in `L¹` from the maximum of the actual
degree expectations by the single whole-interval concentration cost. -/
theorem intervalMaxDegreeLog_sub_maxPressure_integral_le
    {μ : Measure ℂ} {L : ℝ} (hμ : IsBoundedDensityAtom μ L)
    (W s : ℕ) (hW : 0 < W) (z : ℂ) :
    (∫ x, |intervalMaxDegreeLog W s z x - intervalMaxPressure μ W s z|
      ∂intervalRowsLaw W s μ) ≤ intervalPressureConcentrationCost L W s := by
  letI := hμ.toIsProbabilityMeasure
  letI : IsProbabilityMeasure (intervalRowsLaw W s μ) := by
    unfold intervalRowsLaw physicalRowLaw
    infer_instance
  have hX (r : Fin (2 * W + 1)) :
      Measurable (intervalDegreeLog W s z r) := measurable_intervalDegreeLog W s z r
  have hi (r : Fin (2 * W + 1)) := intervalDegreeLog_integrable hμ W s hW z r
  have hci : Integrable
      (maxCenteredDeviation (intervalDegreeLogs W s z) (intervalRowsLaw W s μ))
      (intervalRowsLaw W s μ) :=
    integrable_finitePressureMax (fun r => by
      simpa only [Real.norm_eq_abs, intervalPressure, intervalDegreeLogs] using
        ((hX r).sub_const (intervalPressure μ W s z r)).norm)
      (fun r => ((hi r).sub (integrable_const _)).abs)
  calc
    _ ≤ ∫ x, maxCenteredDeviation (intervalDegreeLogs W s z)
        (intervalRowsLaw W s μ) x ∂intervalRowsLaw W s μ := by
      apply integral_mono
        (((intervalMaxDegreeLog_integrable hμ W s hW z).sub (integrable_const _)).abs)
        hci
      exact finitePressureMax_sub_meanMax_le _ _
    _ ≤ _ := by
      have h := lemma_10_5 hμ W s hW z
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, intervalPressureConcentrationCost, mul_assoc] using h

end BernoulliSection10Complex
