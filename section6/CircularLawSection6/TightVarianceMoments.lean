import CircularLawSection6.NegativeMomentCutoff
import CircularLawSection6.GinibreReference

/-! # Tightness and concentration bound the logarithmic second moments

This passage does not assume convergence of the logarithmic center.
In particular it can be used before proving a Ginibre log-potential limit.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open CircularLawSections56.Section5
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem eventually_abs_center_le_of_tight_and_close
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (c : ℕ → ℝ)
    (htight : BoundedInProbabilityTri μ X)
    (hclose : TendstoInProbabilityTri μ (fun n ω => X n ω - c n) 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, |c n| ≤ C := by
  obtain ⟨D, hD, htail⟩ := htight (1 / 4) (by norm_num)
  refine ⟨D + 1, by linarith, ?_⟩
  have hsmall := (hclose 1 zero_lt_one).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [htail, hsmall] with n hn hc
  by_contra hnot
  have hcover : univ ⊆ {ω | D < |X n ω|} ∪
      {ω | 1 ≤ |(X n ω - c n) - 0|} := by
    intro ω _
    by_contra hbad
    have hx : |X n ω| ≤ D := le_of_not_gt (fun h => hbad (Or.inl h))
    have he : |X n ω - c n| < 1 := by
      apply lt_of_not_ge
      intro h
      apply hbad
      exact Or.inr (by simpa only [sub_zero] using h)
    have htri : |c n| ≤ |X n ω| + |X n ω - c n| := by
      have h := abs_sub_le (c n) (X n ω) 0
      simpa only [sub_zero, abs_sub_comm, add_comm] using h
    linarith
  have hmono := measureReal_mono (μ := μ n) hcover
  have hunion := measureReal_union_le (μ := μ n) {ω | D < |X n ω|}
    {ω | 1 ≤ |(X n ω - c n) - 0|}
  rw [probReal_univ] at hmono
  linarith

theorem exists_uniform_secondMoment_of_tight_and_centered
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ) (hX : ∀ n, MemLp (X n) 2 (μ n))
    (htight : BoundedInProbabilityTri μ X)
    (hclose : TendstoInProbabilityTri μ
      (fun n ω => X n ω - ∫ x, X n x ∂μ n) 0)
    {v : ℝ} (hvar : Tendsto (fun n => variance (X n) (μ n)) atTop (𝓝 v)) :
    ∃ C : ℝ, ∀ n, (∫ ω, X n ω ^ 2 ∂μ n) ≤ C := by
  obtain ⟨D, hD, hmean⟩ := eventually_abs_center_le_of_tight_and_close
    μ X (fun n => ∫ ω, X n ω ∂μ n) htight hclose
  obtain ⟨V, hV⟩ := (Metric.isBounded_range_of_tendsto _ hvar).bddAbove
  obtain ⟨K, hK⟩ := eventually_atTop.1 hmean
  let E (n : ℕ) : ℝ := ∫ ω, X n ω ^ 2 ∂μ n
  let P : ℝ := ∑ n ∈ Finset.range K, |E n|
  have hP : 0 ≤ P := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨max V 0 + D ^ 2 + P, fun n => ?_⟩
  by_cases hn : K ≤ n
  · have hm := hK n hn
    have hsq : (∫ ω, X n ω ∂μ n) ^ 2 ≤ D ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD).2 hm
    have hv : variance (X n) (μ n) ≤ max V 0 :=
      (hV ⟨n, rfl⟩).trans (le_max_left _ _)
    rw [variance_eq_sub (hX n)] at hv
    simp only [Pi.pow_apply] at hv
    linarith
  · have hmem : n ∈ Finset.range K := Finset.mem_range.2 (lt_of_not_ge hn)
    have hsingle : |E n| ≤ P :=
      Finset.single_le_sum (fun i _ => abs_nonneg (E i)) hmem
    have he := (le_abs_self (E n)).trans hsingle
    have hzero : 0 ≤ max V 0 + D ^ 2 :=
      add_nonneg (le_max_right _ _) (sq_nonneg _)
    exact he.trans (by linarith)

end CircularLawSection6
