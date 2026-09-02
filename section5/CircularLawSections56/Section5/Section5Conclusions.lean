import CircularLawSections56.Section5.WeakCircularLaw
import CircularLawSections56.Section5.LiteralEnergyIdentity
import CircularLawSections56.Section5.LiteralNonvanishing

/-! # All three manuscript conclusions and nonvanishing in one output

This structure is an output certificate only. Its constructors below combine
proved Section 5 results; it is never an additional hypothesis of a final
Section 3/4-to-circular-law theorem.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 1600000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open Section6 TaoVuReplacement ShortRingAnchor CircularLawSection4

universe u
variable {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]

structure Section5Conclusions
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Prop where
  logPotential : ∀ᵐ z ∂(volume : Measure ℂ),
    TendstoInProbabilityTri μ (fun n ω => physicalLogPotential (X n ω) z) (circularLogPotential z)
  spectral : ∀ g : BoundedContinuousFunction ℂ ℝ,
    TendstoInMeasure (Measure.infinitePi μ) (fun n ω => realEsdTest (X n (ω n)) g) atTop
      (fun _ => ∫ z, g z ∂circularMeasure)
  hilbertSchmidt_tight : BoundedInProbability (Measure.infinitePi μ)
    (fun n ω => normalizedHilbertSchmidtNorm (X n (ω n)))
  determinant_nonzero : ∀ᵐ z ∂(volume : Measure ℂ), ∀ n,
    ∀ᵐ ω ∂μ n, (X n ω - z • 1).det ≠ 0

def LiteralSection5Conclusions
    (d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) (b : ∀ n, Fin (d n + 2) → ℂ)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)] : Prop :=
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
    fun _n => iidMeasure_isProbability _ _
  Section5Conclusions (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
    (fun n ω => literalIndicatorMatrix n (d n) (center n) (b n) ω)

def RealLiteralSection5Conclusions
    (d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) (b : ∀ n, Fin (d n + 2) → ℂ)
    (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)] : Prop :=
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ρ n) ((n + 1) * (d n + 2))) :=
    fun _n => iidMeasure_isProbability _ _
  Section5Conclusions (fun n => iidMeasure (ρ n) ((n + 1) * (d n + 2)))
    (fun n ω => literalIndicatorMatrix n (d n) (center n) (b n) (realSampleComplexify _ ω))

theorem literalSection5Conclusions_of_limits
    (d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (hc₀ : ∀ n, 0 < c₀ n)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (hInt : ∀ n, Integrable (fun u : ℂ => ‖u‖ ^ 2) (ν n))
    (hSecond : ∀ n, ∫ u : ℂ, ‖u‖ ^ 2 ∂ν n ≤ 1)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hLog : let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
      fun _n => iidMeasure_isProbability _ _
      ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
        (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
        (fun n ω => physicalLogPotential (literalIndicatorMatrix n (d n) (center n) (profile n).b ω) z)
        (circularLogPotential z))
    (hEsd : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure (Measure.infinitePi (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))))
        (fun n ω => realEsdTest (literalIndicatorMatrix n (d n) (center n) (profile n).b (ω n)) g)
        atTop (fun _ => ∫ z, g z ∂circularMeasure)) :
    LiteralSection5Conclusions d center (fun n => (profile n).b) ν := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
    fun _n => iidMeasure_isProbability _ _
  refine ⟨hLog, ?_, literal_indicator_normalized_hilbertSchmidt_tight
    d center profile hc₀ ν hInt hSecond hfit, literal_indicator_determinant_nonzero
      d center (fun n => (profile n).b) ν⟩
  exact circularLaw_boundedContinuousMap_of_compactSupport _ _ hEsd

theorem realLiteralSection5Conclusions_of_limits
    (d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (hc₀ : ∀ n, 0 < c₀ n)
    (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)]
    (hInt : ∀ n, Integrable (fun u : ℝ => u ^ 2) (ρ n))
    (hSecond : ∀ n, ∫ u : ℝ, u ^ 2 ∂ρ n ≤ 1)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1)
    (hLog : let : ∀ n, IsProbabilityMeasure (iidMeasure (ρ n) ((n + 1) * (d n + 2))) :=
      fun _n => iidMeasure_isProbability _ _
      ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri
        (fun n => iidMeasure (ρ n) ((n + 1) * (d n + 2)))
        (fun n ω => physicalLogPotential (literalIndicatorMatrix n (d n) (center n) (profile n).b
          (realSampleComplexify _ ω)) z) (circularLogPotential z))
    (hEsd : ∀ g : ℂ → ℝ, Continuous g → HasCompactSupport g →
      TendstoInMeasure (Measure.infinitePi (fun n => iidMeasure (ρ n) ((n + 1) * (d n + 2))))
        (fun n ω => realEsdTest (literalIndicatorMatrix n (d n) (center n) (profile n).b
          (realSampleComplexify _ (ω n))) g) atTop (fun _ => ∫ z, g z ∂circularMeasure)) :
    RealLiteralSection5Conclusions d center (fun n => (profile n).b) ρ := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ρ n) ((n + 1) * (d n + 2))) :=
    fun _n => iidMeasure_isProbability _ _
  refine ⟨hLog, ?_, ?_, real_literal_indicator_determinant_nonzero
      d center (fun n => (profile n).b) ρ⟩
  · exact circularLaw_boundedContinuousMap_of_compactSupport _ _ hEsd
  · simp_rw [normalizedHilbertSchmidtNorm_eq_sqrt_energy]
    exact boundedInProbability_sqrt _ _
      (real_literal_indicator_energy_bounded_in_probability d center profile hc₀ ρ hInt hSecond hfit)

end CircularLawSections56.Section5
