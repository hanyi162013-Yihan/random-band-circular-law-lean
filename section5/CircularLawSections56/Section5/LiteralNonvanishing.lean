import CircularLawSections56.Section5.RealSampleTransport

/-! # Nonvanishing and the literal logarithmic-potential identity

One planar full-measure set works for every size. This explicitly removes the
ambiguity caused by Lean's totalized value `Real.log 0 = 0`: on this set the
actual determinant is almost surely nonzero, and the spectral identity holds.
The argument needs entrywise measurability, not an additional atom assumption.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open Section6 TaoVuReplacement CircularLawSection4

theorem triangular_physical_determinant_nonzero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (X : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hX : ∀ n i j, Measurable (fun ω => X n ω i j)) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ n,
      ∀ᵐ ω ∂μ n, (X n ω - z • 1).det ≠ 0 := by
  apply ae_all_iff.2
  intro n
  have h := ae_ae_normalizedShiftDet_ne_zero_of_entrywise (μ n)
    (fun ω => undoPhysicalNormalization (X n ω))
    (fun i j => measurable_const.mul (hX n i j))
  simpa only [normalizedShiftDet, normalizedMatrix_undoPhysicalNormalization] using h

theorem triangular_physical_logPotential_spectral_identity
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (X : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hX : ∀ n i j, Measurable (fun ω => X n ω i j)) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ n,
      ∀ᵐ ω ∂μ n, physicalLogPotential (X n ω) z =
        realEsdTest (X n ω) (fun w => Real.log ‖w - z‖) := by
  filter_upwards [triangular_physical_determinant_nonzero μ X hX] with z hz
  intro n
  filter_upwards [hz n] with ω hω
  simpa only [physicalLogPotential, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    normalized_log_norm_det_sub_scalar_eq_realEsdTest (X n ω) z hω

theorem literal_indicator_determinant_nonzero
    (d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) (b : ∀ n, Fin (d n + 2) → ℂ)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)] :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ n,
      ∀ᵐ ω ∂iidMeasure (ν n) ((n + 1) * (d n + 2)),
        (literalIndicatorMatrix n (d n) (center n) (b n) ω - z • 1).det ≠ 0 := by
  let : ∀ n, IsProbabilityMeasure (iidMeasure (ν n) ((n + 1) * (d n + 2))) :=
    fun n => iidMeasure_isProbability _ _
  exact triangular_physical_determinant_nonzero
    (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2)))
    (fun n ω => literalIndicatorMatrix n (d n) (center n) (b n) ω)
    (fun n => literalIndicatorMatrix_measurable n (d n) (center n) (b n))

theorem real_literal_indicator_determinant_nonzero
    (d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1)) (b : ∀ n, Fin (d n + 2) → ℂ)
    (ρ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ρ n)] :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ n,
      ∀ᵐ ω ∂iidMeasure (ρ n) ((n + 1) * (d n + 2)),
        (literalIndicatorMatrix n (d n) (center n) (b n)
          (realSampleComplexify _ ω) - z • 1).det ≠ 0 := by
  filter_upwards [literal_indicator_determinant_nonzero d center b
    (fun n => realComplexAtomLaw (ρ n))] with z hz
  intro n
  exact (realSampleComplexify_measurePreserving _ (ρ n)).quasiMeasurePreserving.ae (hz n)

end CircularLawSections56.Section5
