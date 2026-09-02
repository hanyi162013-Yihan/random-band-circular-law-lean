import CircularLawSections56.Section5.Section5Conclusions

/-! # The two models have asymptotically the same spectral distribution

All bounded continuous real tests are covered. The conclusion is valid for any
coupling with the prescribed marginal sample laws; independence between the two
models is not needed. The product realization is an immediate special case.
-/

open Filter MeasureTheory Topology
noncomputable section
set_option maxHeartbeats 1400000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open Section6 TaoVuReplacement ShortRingAnchor

universe u v w
variable {Ω : ℕ → Type u} {Ξ : ℕ → Type v} {SampleSpace : Type w}
  [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (Ξ n)] [MeasurableSpace SampleSpace]

theorem section5_spectral_difference_under_coupling
    (μ : ∀ n, Measure (Ω n)) (ν : ∀ n, Measure (Ξ n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (X : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (Y : ∀ n, Ξ n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hX : Section5Conclusions μ X) (hY : Section5Conclusions ν Y)
    (P : Measure SampleSpace) [IsProbabilityMeasure P]
    (F : SampleSpace → ∀ n, Ω n) (G : SampleSpace → ∀ n, Ξ n)
    (hF : MeasurePreserving F P (Measure.infinitePi μ))
    (hG : MeasurePreserving G P (Measure.infinitePi ν))
    (g : BoundedContinuousFunction ℂ ℝ) :
    TendstoInMeasure P
      (fun n ω => realEsdTest (X n (F ω n)) g - realEsdTest (Y n (G ω n)) g)
      atTop 0 := by
  have hx := tendstoInMeasure_pullback_measurePreserving hF (hX.spectral g)
  have hy := tendstoInMeasure_pullback_measurePreserving hG (hY.spectral g)
  exact tendstoInMeasure_sub_same_constant P
    ((tendstoInMeasure_iff_tri P _ _).1 hx) ((tendstoInMeasure_iff_tri P _ _).1 hy)

theorem section5_spectral_difference_on_product
    (μ : ∀ n, Measure (Ω n)) (ν : ∀ n, Measure (Ξ n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (X : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (Y : ∀ n, Ξ n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hX : Section5Conclusions μ X) (hY : Section5Conclusions ν Y)
    (g : BoundedContinuousFunction ℂ ℝ) :
    TendstoInMeasure ((Measure.infinitePi μ).prod (Measure.infinitePi ν))
      (fun n ω => realEsdTest (X n (ω.1 n)) g - realEsdTest (Y n (ω.2 n)) g)
      atTop 0 :=
  section5_spectral_difference_under_coupling μ ν X Y hX hY _ Prod.fst Prod.snd
    measurePreserving_fst measurePreserving_snd g

theorem section5_logPotential_difference_under_triangular_coupling
    {TriSpace : ℕ → Type w} [∀ n, MeasurableSpace (TriSpace n)]
    (μ : ∀ n, Measure (Ω n)) (ν : ∀ n, Measure (Ξ n))
    [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsProbabilityMeasure (ν n)]
    (X : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (Y : ∀ n, Ξ n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hX : Section5Conclusions μ X) (hY : Section5Conclusions ν Y)
    (P : ∀ n, Measure (TriSpace n)) [∀ n, IsProbabilityMeasure (P n)]
    (F : ∀ n, TriSpace n → Ω n) (G : ∀ n, TriSpace n → Ξ n)
    (hF : ∀ n, MeasurePreserving (F n) (P n) (μ n))
    (hG : ∀ n, MeasurePreserving (G n) (P n) (ν n)) :
    ∀ᵐ z ∂(volume : Measure ℂ), TendstoInProbabilityTri P
      (fun n ω => physicalLogPotential (X n (F n ω)) z - physicalLogPotential (Y n (G n ω)) z) 0 := by
  filter_upwards [hX.logPotential, hY.logPotential] with z hx hy
  have hx' := tendstoInProbabilityTri_pullback_measurePreserving P μ F hF _ _ hx
  have hy' := tendstoInProbabilityTri_pullback_measurePreserving P ν G hG _ _ hy
  have hyneg : TendstoInProbabilityTri P
      (fun n ω => -physicalLogPotential (Y n (G n ω)) z) (-circularLogPotential z) := by
    intro ε hε
    simpa only [neg_sub_neg, abs_sub_comm] using hy' ε hε
  simpa only [add_neg_cancel, sub_eq_add_neg] using hx'.add P hyneg

end CircularLawSections56.Section5
