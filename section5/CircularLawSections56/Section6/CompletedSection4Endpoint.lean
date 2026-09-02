import CircularLawSections56.Section5.CompletedSection4UniformInputs
import CircularLawSections56.Section6.TriangularReplacement

/-!
# Section 3/4 preinputs to the actual ESD endpoint

The caller supplies finite Section 4 data and the known Section 3 anchors,
not a Section 5 closure certificate or a replacement principle.  Both are
constructed/called inside this theorem.  The reference ensemble's own limit
remains a separate, explicit input.
-/

open Filter MeasureTheory Topology

noncomputable section

namespace CircularLawSections56.Section6

open CircularLawSections56.Section5 TaoVuReplacement

universe u v
variable {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]
variable {ι : ℕ → Type v} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]

/-- Complete conditional replacement endpoint, including the genuine short/long
branch selection.  No caller-supplied final certificate or `hReplacement` is needed. -/
theorem replacement_of_completedSection4
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (X Y : ∀ k, Ω k → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hX : ∀ k i j, Measurable fun ω => X k ω i j)
    (hY : ∀ k i j, Measurable fun ω => Y k ω i j)
    (energyBound : ℝ) (hEnergyBound : 0 ≤ energyBound)
    (hEnergyInt : ∀ k, Integrable
      (fun ω => physicalEnergy (X k ω) + physicalEnergy (Y k ω)) (μ k))
    (hEnergy : ∀ k, ∫ ω, physicalEnergy (X k ω) + physicalEnergy (Y k ω) ∂μ k ≤ energyBound)
    (shortBranch : ℕ → Bool)
    (shortLog calibrationRaw finalRaw : ℂ → ∀ n, Ω n → ℝ)
    (calibrationY finalY : ℂ → ∀ n, ι n → Ω n → ℝ)
    (lifted : ℂ → ∀ n, ι n → ℝ) (q m W : ℕ → ℕ)
    (target C : ℂ → ℝ) (δ γ : ℝ)
    (hδ : 0 < δ) (hδγ : δ < γ) (hγ : γ < 1 / 8)
    (hW : Tendsto W atTop atTop)
    (hLong : ∀ᶠ n in atTop, literalLongActive shortBranch n = true →
      (W n : ℝ) ^ (1 + γ) < (n + 1 : ℝ))
    (h4 : ∀ᵐ z ∂(volume : Measure ℂ), Nonempty
      (CompletedSection4LongBranchData μ (literalLongActive shortBranch)
        (calibrationRaw z) (finalRaw z) (calibrationY z) (finalY z)
        (lifted z) q m (fun n => n + 1) W δ (C z)))
    (h3 : ∀ᵐ z ∂(volume : Measure ℂ), Section3IndicatorAnchorsTri μ (shortLog z)
      (literalActiveNormalizedObservable (literalLongActive shortBranch)
        (calibrationRaw z) m (target z)) (target z))
    (hActual : ∀ᵐ z ∂(volume : Measure ℂ), ∀ n ω,
      physicalLogPotential (X n ω) z = branchSelectedTri shortBranch (shortLog z)
        (literalActiveNormalizedObservable (literalLongActive shortBranch)
          (finalRaw z) (fun n => n + 1) (target z)) n ω)
    (hLogY : ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri μ
      (fun k ω => physicalLogPotential (Y k ω) z) (target z)) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure (Measure.infinitePi μ)
        (fun k ω => esdDifference (X k (ω k)) (Y k (ω k)) f) atTop 0 := by
  apply triangular_physical_replacement μ X Y hX hY energyBound hEnergyBound
    hEnergyInt hEnergy target ?_ hLogY
  filter_upwards [h4, h3, hActual] with z hz4 hz3 hzActual
  have hgrowth : ∀ᶠ n in atTop, literalLongActive shortBranch n = true →
      (W n : ℝ) ^ (1 + γ) < ((fun n : ℕ => n + 1) n : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hLong
  let cert := completedSection4_literalCertificate μ shortBranch (shortLog z)
    (calibrationRaw z) (finalRaw z) (calibrationY z) (finalY z) (lifted z)
    q m (fun n => n + 1) W (target z) δ γ (C z) hδ hδγ hγ hW hgrowth hz4.some hz3
  exact indicator_actualLogPotential_of_literal_certificate μ shortBranch (shortLog z)
    (literalActiveNormalizedObservable (literalLongActive shortBranch) (calibrationRaw z) m (target z))
    (literalActiveNormalizedObservable (literalLongActive shortBranch) (finalRaw z)
      (fun n => n + 1) (target z))
    (fun n ω => physicalLogPotential (X n ω) z)
    (literalActiveNormalizedMeanPressure μ (literalLongActive shortBranch) (finalY z)
      (fun n => n + 1) (target z)) (target z) hz3 cert hzActual

end CircularLawSections56.Section6
