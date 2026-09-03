import CircularLawSection6.NegativeMomentCutoff

/-! # Probability limits through uniformly tight approximations

The approximation parameter is chosen first; the matrix dimension then
tends to infinity. No expectation bound for the tight variable is used.
This is the double-limit passage needed for removal of regularization.
-/

open MeasureTheory Filter Topology Set
open CircularLawSections56.Section5
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem tendstoInProbabilityTri_of_tight_approximations
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (Y Z : ∀ n, Ω n → ℝ) (X : ℕ → ∀ n, Ω n → ℝ)
    (c a b : ℕ → ℝ) (target : ℝ)
    (hZ : BoundedInProbabilityTri μ Z)
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hc : Tendsto c atTop (𝓝 target))
    (hX : ∀ k, TendstoInProbabilityTri μ (X k) (c k))
    (herror : ∀ k n, ∀ᵐ ω ∂μ n,
      |Y n ω - X k n ω| ≤ |a k| * |Z n ω| + |b k|) :
    TendstoInProbabilityTri μ Y target := by
  intro ε hε
  apply Metric.tendsto_nhds.2
  intro δ hδ
  obtain ⟨C, _hC, htail⟩ := hZ (δ / 2) (half_pos hδ)
  have hrate : Tendsto
      (fun k => |a k| * C + |b k| + |c k - target|) atTop (𝓝 0) := by
    simpa only [abs_zero, zero_mul, zero_add, sub_self] using
      ((ha.abs.mul_const C).add hb.abs).add (hc.sub tendsto_const_nhds).abs
  obtain ⟨k, hk⟩ := (hrate.eventually (gt_mem_nhds (half_pos hε))).exists
  have hprob := (hX k (ε / 2) (half_pos hε)).eventually
    (gt_mem_nhds (half_pos hδ))
  filter_upwards [htail, hprob] with n hn hnprob
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  have hsubset : {ω | ε ≤ |Y n ω - target|} ≤ᵐ[μ n]
      {ω | C < |Z n ω|} ∪ {ω | ε / 2 ≤ |X k n ω - c k|} := by
    filter_upwards [herror k n] with ω hω
    intro hy
    by_contra hnot
    have hz : |Z n ω| ≤ C := le_of_not_gt (fun hz => hnot (Or.inl hz))
    have hx : |X k n ω - c k| < ε / 2 :=
      lt_of_not_ge (fun hx => hnot (Or.inr hx))
    have hsmall : |Y n ω - X k n ω| ≤ |a k| * C + |b k| :=
      hω.trans (add_le_add_right
        (mul_le_mul_of_nonneg_left hz (abs_nonneg (a k))) _)
    have htri := abs_sub_le (Y n ω) (X k n ω) target
    have htri2 := abs_sub_le (X k n ω) (c k) target
    change ε ≤ |Y n ω - target| at hy
    linarith
  have hmono : (μ n).real {ω | ε ≤ |Y n ω - target|} ≤
      (μ n).real ({ω | C < |Z n ω|} ∪ {ω | ε / 2 ≤ |X k n ω - c k|}) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsubset)
  have hunion := measureReal_union_le (μ := μ n)
    {ω | C < |Z n ω|} {ω | ε / 2 ≤ |X k n ω - c k|}
  linarith

end CircularLawSection6
