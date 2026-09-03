import CircularLawSection6.ProbabilityFinitePrefix

/-! # Fill gaps in a convergent subsequence with a comparison sequence

This preserves the original matrix dimension at every index. It lets the
already proved replacement theorem act on a subsequence without assuming
a second arbitrary-dimension version of replacement.
-/

open MeasureTheory Filter Topology
open CircularLawSections56.Section5

noncomputable section

namespace CircularLawSection6

theorem tendsto_subsequence_filler (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (x y : ℕ → ℝ) {a : ℝ} (hx : Tendsto (fun n => x (φ n)) atTop (𝓝 a))
    (hy : Tendsto y atTop (𝓝 a)) :
    Tendsto (fun n => if n ∈ Set.range φ then x n else y n) atTop (𝓝 a) := by
  classical
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨Kx, hKx⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hx) ε hε)
  obtain ⟨Ky, hKy⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hy) ε hε)
  refine eventually_atTop.2 ⟨max (φ Kx) Ky, fun n hn => ?_⟩
  by_cases hrange : n ∈ Set.range φ
  · obtain ⟨i, rfl⟩ := hrange
    have hi : Kx ≤ i := hφ.le_iff_le.mp ((le_max_left _ _).trans hn)
    simpa only [if_pos (Set.mem_range_self i)] using hKx i hi
  · simpa only [if_neg hrange] using hKy n ((le_max_right _ _).trans hn)

theorem tendstoInProbabilityTri_subsequence_filler
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (X Y : ∀ n, Ω n → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ) {a : ℝ}
    (hX : TendstoInProbabilityTri (fun n => μ (φ n)) (fun n => X (φ n)) a)
    (hY : TendstoInProbabilityTri μ Y a) :
    TendstoInProbabilityTri μ
      (fun n ω => if n ∈ Set.range φ then X n ω else Y n ω) a := by
  classical
  intro ε hε
  have h := tendsto_subsequence_filler φ hφ
    (fun n => (μ n).real {ω | ε ≤ |X n ω - a|})
    (fun n => (μ n).real {ω | ε ≤ |Y n ω - a|}) (hX ε hε) (hY ε hε)
  apply h.congr'
  apply Eventually.of_forall
  intro n
  by_cases hn : n ∈ Set.range φ <;> simp [hn]

end CircularLawSection6
