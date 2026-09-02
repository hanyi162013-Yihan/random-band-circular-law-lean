import CircularLawSections56.Section5.ProbabilityInputs
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Linarith

/-!
# Deterministic centering from a Section 3 probability anchor

The direct high-band half of `prop:compact-gaussian-core` uses two probability facts:
the Section 3 raw-log anchor converges to the circular potential, and Gaussian
concentration says that the same observable minus its deterministic expectation tends to
zero.  This file proves that those deterministic expectations must converge to the same
target.
-/

open Filter MeasureTheory Set Topology

namespace CircularLawSections56.Section6

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A random observable converging in probability to `target`, while its difference from
a deterministic center converges in probability to zero, forces the centers to converge
to `target`.

This is the probability-level bridge needed by the direct compact-core branch.  The
probability-measure assumption is essential: it turns a deterministic deviation event
into an event of mass one. -/
theorem deterministic_center_tendsto_of_anchor_and_concentration
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (observable : ℕ → Ω → ℝ) (center : ℕ → ℝ) (target : ℝ)
    (hAnchor :
      Section5.ConvergesInProbability μ observable target)
    (hConcentration :
      Section5.ConvergesInProbability μ
        (fun n ω => observable n ω - center n) 0) :
    Tendsto center atTop (𝓝 target) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hεHalf : 0 < ε / 2 := half_pos hε
  have hAnchorEvents :=
    (tendstoInMeasure_iff_dist.mp hAnchor) (ε / 2) hεHalf
  have hCenterEvents :=
    (tendstoInMeasure_iff_dist.mp hConcentration) (ε / 2) hεHalf
  have hSum : Tendsto
      (fun n =>
        μ {ω | ε / 2 ≤ dist (observable n ω) target} +
          μ {ω | ε / 2 ≤ dist (observable n ω - center n) 0})
      atTop (𝓝 0) := by
    simpa using hAnchorEvents.add hCenterEvents
  have hEventuallySmall : ∀ᶠ n in atTop,
      μ {ω | ε / 2 ≤ dist (observable n ω) target} +
          μ {ω | ε / 2 ≤ dist (observable n ω - center n) 0} < 1 :=
    hSum.eventually (Iio_mem_nhds (show (0 : ENNReal) < 1 by simp))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hEventuallySmall
  refine ⟨N, ?_⟩
  intro n hn
  have hSmall := hN n hn
  by_contra hNotClose
  have hFar : ε ≤ dist (center n) target := le_of_not_gt hNotClose
  let anchorBad : Set Ω :=
    {ω | ε / 2 ≤ dist (observable n ω) target}
  let centerBad : Set Ω :=
    {ω | ε / 2 ≤ dist (observable n ω - center n) 0}
  have hCover : (Set.univ : Set Ω) ⊆ anchorBad ∪ centerBad := by
    intro ω hω
    by_cases hA : ε / 2 ≤ dist (observable n ω) target
    · exact Or.inl hA
    by_cases hC : ε / 2 ≤ dist (observable n ω - center n) 0
    · exact Or.inr hC
    · have hA' : dist (observable n ω) target < ε / 2 := lt_of_not_ge hA
      have hC' : dist (observable n ω - center n) 0 < ε / 2 := lt_of_not_ge hC
      have hCenterObservable :
          dist (center n) (observable n ω) =
            dist (observable n ω - center n) 0 := by
        simp [Real.dist_eq, abs_sub_comm]
      have hTriangle :
          dist (center n) target ≤
            dist (center n) (observable n ω) +
              dist (observable n ω) target :=
        dist_triangle _ _ _
      rw [hCenterObservable] at hTriangle
      exfalso
      linarith
  have hMassOne : (1 : ENNReal) ≤ μ anchorBad + μ centerBad := by
    calc
      (1 : ENNReal) = μ (Set.univ : Set Ω) := by simp
      _ ≤ μ (anchorBad ∪ centerBad) := measure_mono hCover
      _ ≤ μ anchorBad + μ centerBad := measure_union_le _ _
  have hSmall' : μ anchorBad + μ centerBad < 1 := by
    simpa [anchorBad, centerBad] using hSmall
  exact (not_lt_of_ge hMassOne) hSmall'

/-- Direct compact-core specialization with the Section 3 input named explicitly. -/
theorem deterministic_center_tendsto_of_section3_anchor
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (observable : ℕ → Ω → ℝ) (center : ℕ → ℝ) (target : ℝ)
    (hSection3 :
      Section5.Section3ShortRingAnchorInput μ observable target)
    (hGaussianConcentration :
      Section5.ConvergesInProbability μ
        (fun n ω => observable n ω - center n) 0) :
    Tendsto center atTop (𝓝 target) :=
  deterministic_center_tendsto_of_anchor_and_concentration
    μ observable center target hSection3 hGaussianConcentration

end CircularLawSections56.Section6
