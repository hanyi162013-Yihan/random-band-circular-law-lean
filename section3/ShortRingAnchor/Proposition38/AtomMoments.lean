import ShortRingAnchor.Proposition38.Source
import ShortRingAnchor.AtomAssumption21

/-! Proposition 3.8, application of counting and Lemma 3.5: the needed
third moment follows from the stated subgaussian hypothesis. It is not an
additional external input or a bounded-density assumption. -/

open MeasureTheory ProbabilityTheory
noncomputable section
namespace ShortRingAnchor.Proposition38

/-- Proposition 3.8: every finite absolute moment follows from the MGF. -/
theorem Atom.integrable_norm_pow (A : Atom) (p : ℕ) :
    Integrable (fun x : ℝ => ‖x‖ ^ p) A.law := by
  exact (A.subgaussian.memLp p).integrable_norm_pow'

/-- Proposition 3.8, before (3.23)--(3.24): the atom satisfies the precise
moment package consumed by the internally proved v3 comparison machinery. -/
theorem Atom.momentAssumption21 (A : Atom) :
    AtomMomentAssumption21 A.law (fun x : ℝ => (x : ℂ)) where
  stronglyMeasurable := Complex.measurable_ofReal.stronglyMeasurable
  centered := by
    change (∫ x : ℝ, (x : ℂ) ∂A.law) = 0
    rw [integral_complex_ofReal, A.centered]
    rfl
  unitSecondMoment := by simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using A.second_moment
  thirdMomentIntegrable := by simpa [Complex.norm_real] using A.integrable_norm_pow 3

end ShortRingAnchor.Proposition38
