import CircularLawSection6.SubsequenceFillers
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact

/-! # Sparse/dense extraction and probability subsequence closure

Every nonnegative ratio sequence has a further sequence tending to zero
or bounded below by a positive constant. The convergence-in-measure
subsequence principle is proved through its numerical bad probabilities,
so no unproved measurability of a spectral observable is required.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace CircularLawSection6

theorem exists_sparse_or_dense_subsequence (x : ℕ → ℝ) (hx : ∀ n, 0 ≤ x n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (Tendsto (fun n => x (φ n)) atTop (𝓝 0) ∨ ∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ x (φ n)) := by
  let y (n : ℕ) := min 1 (x n)
  obtain ⟨a, ha, φ, hφ, hlim⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).tendsto_subseq
    (x := y) (fun n => ⟨le_min zero_le_one (hx n), min_le_left _ _⟩)
  by_cases ha0 : a = 0
  · subst a
    refine ⟨φ, hφ, Or.inl ?_⟩
    apply hlim.congr'
    filter_upwards [hlim.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with n hn
    change min 1 (x (φ n)) = x (φ n)
    change min 1 (x (φ n)) < 1 at hn
    apply min_eq_right
    by_contra hnot
    rw [min_eq_left (le_of_not_ge hnot)] at hn
    exact (lt_irrefl (1 : ℝ)) hn
  · have haPos : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hlim.eventually (lt_mem_nhds (half_lt_self haPos)))
    refine ⟨fun n => φ (n + K), hφ.comp (fun i j hij => Nat.add_lt_add_right hij K),
      Or.inr ⟨a / 2, half_pos haPos, fun n => ?_⟩⟩
    exact (hK (n + K) (by omega)).le.trans (min_le_right _ _)

theorem tendsto_of_every_subsequence_has_further
    {E : Type*} [TopologicalSpace E] (u : ℕ → E) (a : E)
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun n => u (φ (ψ n))) atTop (𝓝 a)) : Tendsto u atTop (𝓝 a) := by
  by_contra hnot
  obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hnot
  obtain ⟨φ, hφ, hout⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ψ, _, hlim⟩ := h φ hφ
  obtain ⟨n, hn⟩ := (hlim.eventually hs).exists
  exact hout (ψ n) hn

theorem tendstoInMeasure_of_every_subsequence_has_further
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoInMeasure μ (fun n => X (φ (ψ n))) atTop g) :
    TendstoInMeasure μ X atTop g := by
  intro ε hε
  apply tendsto_of_every_subsequence_has_further _ 0
  intro φ hφ
  obtain ⟨ψ, hψ, hlim⟩ := h φ hφ
  exact ⟨ψ, hψ, hlim ε hε⟩

theorem tendstoInMeasure_of_sparse_dense_subsequences
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (g : Ω → ℝ) (ratio : ℕ → ℝ) (hratio : ∀ n, 0 ≤ ratio n)
    (hsparse : ∀ φ : ℕ → ℕ, StrictMono φ → Tendsto (fun n => ratio (φ n)) atTop (𝓝 0) →
      TendstoInMeasure μ (fun n => X (φ n)) atTop g)
    (hdense : ∀ φ : ℕ → ℕ, StrictMono φ →
      (∃ c : ℝ, 0 < c ∧ ∀ n, c ≤ ratio (φ n)) →
      TendstoInMeasure μ (fun n => X (φ n)) atTop g) :
    TendstoInMeasure μ X atTop g := by
  apply tendstoInMeasure_of_every_subsequence_has_further μ X g
  intro φ hφ
  obtain ⟨ψ, hψ, hbranch⟩ := exists_sparse_or_dense_subsequence (fun n => ratio (φ n)) (fun n => hratio (φ n))
  refine ⟨ψ, hψ, ?_⟩
  rcases hbranch with hs | hd
  · exact hsparse (φ ∘ ψ) (hφ.comp hψ) hs
  · exact hdense (φ ∘ ψ) (hφ.comp hψ) hd

end CircularLawSection6
