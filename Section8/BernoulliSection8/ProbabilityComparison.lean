import BernoulliSection10.ProbabilityLimits

/-! # Elementary probability comparisons on changing sample spaces -/

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace BernoulliSection8

open BernoulliSection10.ProbabilityLimits

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

theorem tendstoInProbabilityTri_eventually_congr
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    {X Y : ∀ n, Ω n → ℝ} {u : ℝ}
    (hX : TendstoInProbabilityTri μ X u)
    (hXY : ∀ᶠ n in atTop, ∀ x, X n x = Y n x) :
    TendstoInProbabilityTri μ Y u := by
  intro ε hε
  apply (hX ε hε).congr'
  filter_upwards [hXY] with n hn
  congr 1
  ext x
  simp only [hn]

/-- A deterministic bound on a scalar multiplier preserves a zero limit. -/
theorem tendstoInProbabilityTri_mul_of_bounded
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    {X : ∀ n, Ω n → ℝ} (hX : TendstoInProbabilityTri μ X 0)
    (a : ℕ → ℝ) {C : ℝ} (hC : 0 < C)
    (ha : ∀ᶠ n in atTop, |a n| ≤ C) :
    TendstoInProbabilityTri μ (fun n x => a n * X n x) 0 := by
  intro ε hε
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) _
    (hX (ε / C) (div_pos hε hC))
  filter_upwards [ha] with n han
  apply measureReal_mono (h₂ := measure_ne_top (μ n) _)
  intro x hx
  simp only [Set.mem_setOf_eq, sub_zero, abs_mul] at hx ⊢
  apply (div_le_iff₀ hC).mpr
  have hh := mul_le_mul_of_nonneg_right han (abs_nonneg (X n x))
  nlinarith

/-- Total logarithms may behave arbitrarily on an exceptional event;
only its probability and the displayed good-event estimate are used. -/
theorem tendstoInProbabilityTri_of_good_event_bound
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (E : ∀ n, Set (Ω n)) (hE : Tendsto (fun n => (μ n).real (E n)) atTop (𝓝 0))
    {X Y : ∀ n, Ω n → ℝ} (hY : TendstoInProbabilityTri μ Y 0)
    (hXY : ∀ᶠ n in atTop, ∀ x ∉ E n, |X n x| ≤ |Y n x|) :
    TendstoInProbabilityTri μ X 0 := by
  intro ε hε
  have hlim := hE.add (hY ε hε)
  simp only [zero_add] at hlim
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) _ hlim
  filter_upwards [hXY] with n hn
  apply (measureReal_mono (show {x | ε ≤ |X n x - 0|} ⊆
      E n ∪ {x | ε ≤ |Y n x - 0|} from ?_)).trans (measureReal_union_le _ _)
  intro x hx
  by_cases he : x ∈ E n
  · exact Or.inl he
  · have hx' : ε ≤ |X n x| := by simpa only [Set.mem_setOf_eq, sub_zero] using hx
    exact Or.inr (by simpa only [Set.mem_setOf_eq, sub_zero] using hx'.trans (hn x he))

theorem tendstoInProbabilityTri_abs_zero
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    {X : ∀ n, Ω n → ℝ} (hX : TendstoInProbabilityTri μ X 0) :
    TendstoInProbabilityTri μ (fun n x => |X n x|) 0 := by
  simpa only [TendstoInProbabilityTri, sub_zero, abs_abs] using hX

/-- Arbitrary alternation of branches that each converge to zero. -/
theorem tendstoInProbabilityTri_if_zero
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (P : ℕ → Prop) [DecidablePred P]
    {X : ∀ n, Ω n → ℝ} (hX : TendstoInProbabilityTri μ X 0) :
    TendstoInProbabilityTri μ (fun n x => if P n then X n x else 0) 0 := by
  intro ε hε
  apply squeeze_zero (fun _ => measureReal_nonneg) _ (hX ε hε)
  intro n
  by_cases hn : P n
  · simp only [if_pos hn, le_refl]
  · simp only [if_neg hn, sub_zero, abs_zero, not_le_of_gt hε, Set.setOf_false,
      measureReal_empty]
    exact measureReal_nonneg

end BernoulliSection8
