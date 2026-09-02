import BernoulliSection10.ProbabilityLimits
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! # Probability limits are invariant under the proved model-law transports -/

open MeasureTheory

namespace BernoulliSection10.ProbabilityLimits

theorem tendstoInProbabilityTri_measurePreserving_iff
    {Ω Λ : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Λ n)]
    (μ : ∀ n, Measure (Ω n)) (ν : ∀ n, Measure (Λ n))
    [∀ n, IsFiniteMeasure (μ n)] [∀ n, IsFiniteMeasure (ν n)]
    (f : ∀ n, Ω n → Λ n) (hf : ∀ n, MeasurePreserving (f n) (μ n) (ν n))
    (X : ∀ n, Λ n → ℝ) (hX : ∀ n, Measurable (X n)) (u : ℝ) :
    TendstoInProbabilityTri μ (fun n ω => X n (f n ω)) u ↔
      TendstoInProbabilityTri ν X u := by
  have he (ε : ℝ) (n : ℕ) :
      (μ n).real {ω | ε ≤ |X n (f n ω) - u|} =
        (ν n).real {ω | ε ≤ |X n ω - u|} :=
    (hf n).measureReal_preimage
      (measurableSet_le measurable_const ((hX n).sub_const u).norm).nullMeasurableSet
  simp only [TendstoInProbabilityTri, he]

end BernoulliSection10.ProbabilityLimits
