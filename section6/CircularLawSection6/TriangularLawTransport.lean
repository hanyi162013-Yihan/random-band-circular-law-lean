import CircularLawSections56.Section5.TriangularProbability
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! # Transport of triangular-array probability limits

The source sample spaces may be larger than the target spaces. Only a
measure-preserving map is needed, not a measurable equivalence or coupling
between different matrix sizes.
-/

open MeasureTheory Filter Topology
open CircularLawSections56.Section5

namespace CircularLawSection6

theorem tendstoInProbabilityTri_comp_measurePreserving
    {Ω Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)]
    (μ : ∀ n, Measure (Ω n)) (ν : ∀ n, Measure (Ξ n))
    [∀ n, IsFiniteMeasure (μ n)] [∀ n, IsFiniteMeasure (ν n)]
    (T : ∀ n, Ω n → Ξ n) (hT : ∀ n, MeasurePreserving (T n) (μ n) (ν n))
    (X : ∀ n, Ξ n → ℝ) (hX : ∀ n, Measurable (X n)) {a : ℝ}
    (hlim : TendstoInProbabilityTri ν X a) :
    TendstoInProbabilityTri μ (fun n ω => X n (T n ω)) a := by
  intro ε hε
  apply (hlim ε hε).congr'
  apply Filter.Eventually.of_forall
  intro n
  have hm : Measurable (fun ω => |X n ω - a|) := by
    simpa only [Real.norm_eq_abs] using ((hX n).sub_const a).norm
  exact ((hT n).measureReal_preimage
    (measurableSet_le measurable_const hm).nullMeasurableSet).symm

end CircularLawSection6
