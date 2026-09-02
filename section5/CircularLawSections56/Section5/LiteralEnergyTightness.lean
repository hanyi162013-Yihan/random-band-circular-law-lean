import CircularLawSections56.Section6.LiteralIndicatorModel
import CircularLawSections56.Section5.RealSampleTransport

/-! # Energy tightness of the unfilled literal matrices

The normalized Hilbert--Schmidt bound is a conclusion, including on the original
real sample space. Finite prefix fillers used in replacement are removed here.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 1200000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open Section6 TaoVuReplacement CircularLawSection4

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]

theorem boundedInProbability_of_eventually_eq
    (P : Measure Ω) {X Y : ℕ → Ω → ℝ}
    (hX : BoundedInProbability P X) (hXY : X =ᶠ[atTop] Y) :
    BoundedInProbability P Y := by
  intro ε hε
  obtain ⟨C, hC, htail⟩ := hX ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail, hXY] with n hn he
  simpa only [← he] using hn

theorem boundedInProbability_pullback_measurePreserving
    (P : Measure Ω) (Q : Measure Λ) (F : Ω → Λ)
    (hF : MeasurePreserving F P Q) (X : ℕ → Λ → ℝ)
    (hX : BoundedInProbability Q X) :
    BoundedInProbability P (fun n ω => X n (F ω)) := by
  intro ε hε
  obtain ⟨C, hC, htail⟩ := hX ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [htail] with n hn
  exact (hF.measure_preimage_le {ω | C < ‖X n ω‖}).trans_lt hn

theorem literal_indicator_energy_bounded_in_probability
    (d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (hc₀ : ∀ n, 0 < c₀ n)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (hInt : ∀ n, Integrable (fun u : ℂ => ‖u‖ ^ 2) (ν n))
    (hSecond : ∀ n, ∫ u : ℂ, ‖u‖ ^ 2 ∂ν n ≤ 1)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1) :
    BoundedInProbability
      (Measure.infinitePi (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))))
      (fun n ω => physicalEnergy
        (literalIndicatorMatrix n (d n) (center n) (profile n).b (ω n))) := by
  let μ := fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))
  let : ∀ n, IsProbabilityMeasure (μ n) := fun n => iidMeasure_isProbability _ _
  let Y : ℕ → (∀ n, Fin ((n + 1) * (d n + 2)) → ℂ) → ℝ := fun n ω => physicalEnergy
    (filledLiteralIndicatorMatrix n (d n) (center n) (profile n).b (ω n))
  have hE := fun n => filledLiteralIndicatorMatrix_energy_integrable_and_le_one
    n (d n) (center n) (profile n) (hc₀ n) (ν n) (hInt n) (hSecond n)
  have hY : BoundedInProbability (Measure.infinitePi μ) Y := by
    apply boundedInProbability_of_uniform_integral (Measure.infinitePi μ) Y 1 zero_le_one
    · intro n ω
      exact div_nonneg (hilbertSchmidtSq_nonneg _) (by positivity)
    · intro n
      exact (measurePreserving_eval_infinitePi μ n).integrable_comp_of_integrable (hE n).1
    · intro n
      rw [canonical_integral_eq μ n _ (hE n).1]
      exact (hE n).2
  apply boundedInProbability_of_eventually_eq (Measure.infinitePi μ) hY
  filter_upwards [hfit] with n hn
  funext ω
  simp only [Y, filledLiteralIndicatorMatrix, if_pos hn]

theorem real_literal_indicator_energy_bounded_in_probability
    (d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (hc₀ : ∀ n, 0 < c₀ n)
    (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)]
    (hInt : ∀ n, Integrable (fun u : ℝ => u ^ 2) (ρ n))
    (hSecond : ∀ n, ∫ u : ℝ, u ^ 2 ∂ρ n ≤ 1)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1) :
    BoundedInProbability
      (Measure.infinitePi (fun n => iidMeasure (ρ n) ((n + 1) * (d n + 2))))
      (fun n ω => physicalEnergy
        (literalIndicatorMatrix n (d n) (center n) (profile n).b
          (realSampleComplexify _ (ω n)))) := by
  have hE := literal_indicator_energy_bounded_in_probability d center profile hc₀
    (fun n => realComplexAtomLaw (ρ n))
    (fun n => (realComplexAtomLaw_secondMoment (ρ n) (hInt n)).1)
    (fun n => (realComplexAtomLaw_secondMoment (ρ n) (hInt n)).2.trans_le (hSecond n)) hfit
  exact boundedInProbability_pullback_measurePreserving _ _ _
    (realSamplesComplexify_measurePreserving (fun n => (n + 1) * (d n + 2)) ρ)
    (fun n ω => physicalEnergy
      (literalIndicatorMatrix n (d n) (center n) (profile n).b (ω n))) hE

end CircularLawSections56.Section5
