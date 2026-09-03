/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/ScalarConcentration.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.ProbabilityEvent
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Real

/-!
# From real McDiarmid tails to the complex scalar event in v3 Proposition 3.4

McDiarmid is a real-valued inequality, whereas the normalized resolvent trace is complex.
This file proves the elementary but logically necessary bridge: four one-sided real tail bounds
(the two signs of the real and imaginary parts) imply the paper's complex-norm good event, with
the factor `4` displayed in v3 proof step (3).  No concentration conclusion is postulated here.
-/

namespace Arxiv2410V3

open MeasureTheory Set

/-- The fixed-parameter good event in v3 Proposition 3.4, proof step (3). -/
def ComplexConcentrationGood {Omega : Type*}
    (trace : Omega → ℂ) (expectedTrace : ℂ) (bound : ℝ) : Set Omega :=
  {omega | ‖trace omega - expectedTrace‖ ≤ bound}

/-- A one-sided upper-tail event for a centered real observable. -/
def centeredUpperTail {Omega : Type*}
    (observable : Omega → ℝ) (mean threshold : ℝ) : Set Omega :=
  {omega | threshold ≤ observable omega - mean}

/-- A one-sided lower-tail event, written as the upper tail of the negative deviation. -/
def centeredLowerTail {Omega : Type*}
    (observable : Omega → ℝ) (mean threshold : ℝ) : Set Omega :=
  {omega | threshold ≤ -(observable omega - mean)}

/-- Membership in the complex good event is exactly the pointwise scalar estimate. -/
theorem scalarConcentrationHypothesis_complexConcentrationGood
    {Omega : Type*} {trace : Omega → ℂ} {expectedTrace : ℂ} {bound : ℝ} :
    ∀ omega ∈ ComplexConcentrationGood trace expectedTrace bound,
      ‖trace omega - expectedTrace‖ ≤ bound := by
  exact fun _omega homega => homega

/-- Measurability of the fixed-parameter complex concentration event. -/
theorem measurableSet_complexConcentrationGood
    {Omega : Type*} [MeasurableSpace Omega]
    {trace : Omega → ℂ} (htrace : Measurable trace)
    (expectedTrace : ℂ) (bound : ℝ) :
    MeasurableSet (ComplexConcentrationGood trace expectedTrace bound) := by
  exact (htrace.sub measurable_const).norm measurableSet_Iic

/-- Deterministic real/imaginary reduction behind the factor `4` in the v3 McDiarmid tail.
If the complex deviation has norm greater than `bound`, then one of its two coordinates, with
one of its two signs, is at least `bound / 2`. -/
theorem compl_complexConcentrationGood_subset_four_tails
    {Omega : Type*} {trace : Omega → ℂ} {expectedTrace : ℂ} {bound : ℝ}
    (_hbound : 0 ≤ bound) :
    (ComplexConcentrationGood trace expectedTrace bound)ᶜ ⊆
      centeredUpperTail (fun omega => (trace omega).re) expectedTrace.re (bound / 2) ∪
      centeredLowerTail (fun omega => (trace omega).re) expectedTrace.re (bound / 2) ∪
      centeredUpperTail (fun omega => (trace omega).im) expectedTrace.im (bound / 2) ∪
      centeredLowerTail (fun omega => (trace omega).im) expectedTrace.im (bound / 2) := by
  intro omega homega
  simp only [ComplexConcentrationGood, mem_compl_iff, mem_ofPred_eq, not_le] at homega
  simp only [mem_union, centeredUpperTail, centeredLowerTail, mem_ofPred_eq]
  by_contra hnone
  simp only [not_or, not_le] at hnone
  rcases hnone with ⟨⟨⟨hreUpper, hreLower⟩, himUpper⟩, himLower⟩
  have hre : |(trace omega - expectedTrace).re| < bound / 2 := by
    rw [abs_lt]
    constructor <;> simp only [Complex.sub_re] <;> linarith
  have him : |(trace omega - expectedTrace).im| < bound / 2 := by
    rw [abs_lt]
    constructor <;> simp only [Complex.sub_im] <;> linarith
  have hnorm := Complex.norm_le_abs_re_add_abs_im (trace omega - expectedTrace)
  linarith

/-- Four one-sided real tail estimates imply the complex scalar concentration event.

This is the exact union-bound bookkeeping behind v3's
`P(|m-E m| ≥ t) ≤ 4 exp(-c n v² t²)`: if every one-sided coordinate tail has probability at
most `q`, the complex good event has probability at least `1 - 4q`. -/
theorem probabilityAtLeast_complexConcentrationGood_of_four_tails
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {trace : Omega → ℂ} (htrace : Measurable trace)
    {expectedTrace : ℂ} {bound q : ℝ} (hbound : 0 ≤ bound)
    (hreUpper : mu.real
      (centeredUpperTail (fun omega => (trace omega).re) expectedTrace.re (bound / 2)) ≤ q)
    (hreLower : mu.real
      (centeredLowerTail (fun omega => (trace omega).re) expectedTrace.re (bound / 2)) ≤ q)
    (himUpper : mu.real
      (centeredUpperTail (fun omega => (trace omega).im) expectedTrace.im (bound / 2)) ≤ q)
    (himLower : mu.real
      (centeredLowerTail (fun omega => (trace omega).im) expectedTrace.im (bound / 2)) ≤ q) :
    ProbabilityAtLeast mu (ComplexConcentrationGood trace expectedTrace bound) (1 - 4 * q) := by
  let bad : Set Omega :=
    centeredUpperTail (fun omega => (trace omega).re) expectedTrace.re (bound / 2) ∪
    centeredLowerTail (fun omega => (trace omega).re) expectedTrace.re (bound / 2) ∪
    centeredUpperTail (fun omega => (trace omega).im) expectedTrace.im (bound / 2) ∪
    centeredLowerTail (fun omega => (trace omega).im) expectedTrace.im (bound / 2)
  have hbad : mu.real bad ≤ 4 * q := by
    dsimp only [bad]
    calc
      mu.real (_ ∪ _ ∪ _ ∪ _) ≤
          mu.real (centeredUpperTail (fun omega => (trace omega).re)
            expectedTrace.re (bound / 2)) +
          mu.real (centeredLowerTail (fun omega => (trace omega).re)
            expectedTrace.re (bound / 2)) +
          mu.real (centeredUpperTail (fun omega => (trace omega).im)
            expectedTrace.im (bound / 2)) +
          mu.real (centeredLowerTail (fun omega => (trace omega).im)
            expectedTrace.im (bound / 2)) := by
              calc
                mu.real (_ ∪ _ ∪ _ ∪ _) ≤ mu.real (_ ∪ _ ∪ _) + mu.real _ :=
                  measureReal_union_le _ _
                _ ≤ (mu.real (_ ∪ _) + mu.real _) + mu.real _ := by
                  gcongr
                  exact measureReal_union_le _ _
                _ ≤ ((mu.real _ + mu.real _) + mu.real _) + mu.real _ := by
                  gcongr
                  exact measureReal_union_le _ _
      _ ≤ 4 * q := by linarith
  have hcompl : mu.real (ComplexConcentrationGood trace expectedTrace bound)ᶜ ≤ 4 * q :=
    (measureReal_mono
      (compl_complexConcentrationGood_subset_four_tails hbound) (by finiteness)).trans hbad
  have hmeas := measurableSet_complexConcentrationGood htrace expectedTrace bound
  have hreal : 1 - 4 * q ≤ mu.real (ComplexConcentrationGood trace expectedTrace bound) := by
    have heq := probReal_compl_eq_one_sub (μ := mu) hmeas
    linarith
  exact ENNReal.ofReal_le_of_le_toReal hreal

/-- Specialization of the four-tail union bound to the `1 - n⁻¹⁰` probability in v3
Proposition 3.4. -/
theorem probabilityAtLeast_complexConcentrationGood_v3
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {trace : Omega → ℂ} (htrace : Measurable trace)
    {expectedTrace : ℂ} {bound q n : ℝ} (hbound : 0 ≤ bound)
    (hreUpper : mu.real
      (centeredUpperTail (fun omega => (trace omega).re) expectedTrace.re (bound / 2)) ≤ q)
    (hreLower : mu.real
      (centeredLowerTail (fun omega => (trace omega).re) expectedTrace.re (bound / 2)) ≤ q)
    (himUpper : mu.real
      (centeredUpperTail (fun omega => (trace omega).im) expectedTrace.im (bound / 2)) ≤ q)
    (himLower : mu.real
      (centeredLowerTail (fun omega => (trace omega).im) expectedTrace.im (bound / 2)) ≤ q)
    (hq : 4 * q ≤ n ^ (-10 : ℤ)) :
    ProbabilityAtLeast mu (ComplexConcentrationGood trace expectedTrace bound)
      (1 - n ^ (-10 : ℤ)) := by
  have hbase := probabilityAtLeast_complexConcentrationGood_of_four_tails
    htrace hbound hreUpper hreLower himUpper himLower
  exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hbase

end Arxiv2410V3

