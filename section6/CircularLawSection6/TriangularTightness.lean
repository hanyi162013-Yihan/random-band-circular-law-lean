import CircularLawSection6.NegativeMomentCutoff

/-! # Elementary tightness tools on varying probability spaces -/

open MeasureTheory Filter Topology Set
open CircularLawSections56.Section5
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem boundedInProbabilityTri_of_integral_abs_bound
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → ℝ)
    (hint : ∀ n, Integrable (fun ω => |X n ω|) (μ n))
    (C : ℝ) (hC : ∀ n, (∫ ω, |X n ω| ∂μ n) ≤ C) :
    BoundedInProbabilityTri μ X := by
  intro δ hδ
  let K : ℝ := (max C 0 + 1) / δ
  have hK : 0 < K := div_pos (by positivity) hδ
  refine ⟨K, hK, Eventually.of_forall (fun n => ?_)⟩
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := μ n) (f := fun ω => |X n ω|)
    (ae_of_all _ fun ω => abs_nonneg _) (hint n) K
  have hmono : (μ n).real {ω | K < |X n ω|} ≤
      (μ n).real {ω | K ≤ |X n ω|} := by
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω h
    change K < |X n ω| at h
    change K ≤ |X n ω|
    exact h.le
  have hprod : K * (μ n).real {ω | K < |X n ω|} ≤ C :=
    (mul_le_mul_of_nonneg_left hmono hK.le).trans (hm.trans (hC n))
  have hden : K * δ = max C 0 + 1 := div_mul_cancel₀ _ hδ.ne'
  have hClt : C < K * δ := by rw [hden]; linarith [le_max_left C 0]
  exact (mul_lt_mul_iff_right₀ hK).1 (hprod.trans_lt hClt)

theorem BoundedInProbabilityTri.of_ae_abs_le
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {X Y : ∀ n, Ω n → ℝ} (hY : BoundedInProbabilityTri μ Y)
    (hXY : ∀ n, ∀ᵐ ω ∂μ n, |X n ω| ≤ |Y n ω|) :
    BoundedInProbabilityTri μ X := by
  intro δ hδ
  obtain ⟨C, hC, htail⟩ := hY δ hδ
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail] with n hn
  refine lt_of_le_of_lt ?_ hn
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hXY n] with ω hω
  exact fun h => h.trans_le hω

theorem BoundedInProbabilityTri.add
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    {X Y : ∀ n, Ω n → ℝ}
    (hX : BoundedInProbabilityTri μ X) (hY : BoundedInProbabilityTri μ Y) :
    BoundedInProbabilityTri μ (fun n ω => X n ω + Y n ω) := by
  intro δ hδ
  obtain ⟨C, hC, htailC⟩ := hX (δ / 2) (half_pos hδ)
  obtain ⟨D, hD, htailD⟩ := hY (δ / 2) (half_pos hδ)
  refine ⟨C + D, add_pos hC hD, ?_⟩
  filter_upwards [htailC, htailD] with n hnC hnD
  have hsub : {ω | C + D < |X n ω + Y n ω|} ⊆
      {ω | C < |X n ω|} ∪ {ω | D < |Y n ω|} := by
    intro ω hω
    by_contra hnot
    change ¬ (C < |X n ω| ∨ D < |Y n ω|) at hnot
    have hx : |X n ω| ≤ C := le_of_not_gt (fun h => hnot (Or.inl h))
    have hy : |Y n ω| ≤ D := le_of_not_gt (fun h => hnot (Or.inr h))
    have h := abs_add_le (X n ω) (Y n ω)
    change C + D < |X n ω + Y n ω| at hω
    linarith
  have hm := measureReal_mono (μ := μ n) hsub
  have hu := measureReal_union_le (μ := μ n)
    {ω | C < |X n ω|} {ω | D < |Y n ω|}
  linarith

theorem BoundedInProbabilityTri.const_mul
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {X : ∀ n, Ω n → ℝ} (hX : BoundedInProbabilityTri μ X) (a : ℝ) :
    BoundedInProbabilityTri μ (fun n ω => a * X n ω) := by
  intro δ hδ
  obtain ⟨C, hC, htail⟩ := hX δ hδ
  refine ⟨(|a| + 1) * C, mul_pos (by positivity) hC, ?_⟩
  filter_upwards [htail] with n hn
  refine lt_of_le_of_lt ?_ hn
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  change C < |X n ω|
  by_contra hnot
  have hle := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) (abs_nonneg a)
  change (|a| + 1) * C < |a * X n ω| at hω
  rw [abs_mul] at hω
  nlinarith

end CircularLawSection6
