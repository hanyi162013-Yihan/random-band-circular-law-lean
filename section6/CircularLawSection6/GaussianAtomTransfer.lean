import CircularLawSection6.GaussianDensityBounds
import CircularLawSections56.Section5.AtomFreshFinite
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # The full Section 5 finite atom package for the actual Gaussian law

The Radon--Nikodym density is only a representation of the already constructed
circular Gaussian measure. Its density bound follows from the proved measure
domination; no additional Gaussian integrability or projective estimate is
assumed.
-/

open MeasureTheory
open CircularLawSections56.Section5
open scoped ENNReal

noncomputable section

namespace CircularLawSection6

def circularGaussianDensity : ℂ → ℝ≥0∞ :=
  circularComplexGaussian.rnDeriv volume

theorem circularGaussianDensity_withDensity :
    volume.withDensity circularGaussianDensity = circularComplexGaussian :=
  Measure.withDensity_rnDeriv_eq _ _
    (Measure.absolutelyContinuous_of_le_smul circularComplexGaussian_le_two_volume)

instance circularGaussianDensity_isProbability :
    IsProbabilityMeasure (volume.withDensity circularGaussianDensity) := by
  rw [circularGaussianDensity_withDensity]
  infer_instance

theorem circularGaussianDensity_le_two :
    ∀ᵐ z ∂(volume : Measure ℂ), circularGaussianDensity z ≤ 2 := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    (Measure.measurable_rnDeriv circularComplexGaussian volume)
  intro s _ _
  have h := (Measure.setLIntegral_rnDeriv_le (μ := circularComplexGaussian)
    (ν := (volume : Measure ℂ)) s).trans (circularComplexGaussian_le_two_volume s)
  simpa only [circularGaussianDensity, lintegral_const, Measure.restrict_apply_univ,
    Measure.smul_apply, smul_eq_mul] using h

theorem circularComplexGaussian_atomTransferControl :
    AtomTransferControl circularComplexGaussian (uniformFreshNegativeConstant 2)
      ((Real.log (max 1 (Real.pi * 2)) + 1) / 2) := by
  have h := AtomTransferControl.complex circularGaussianDensity 2 (by norm_num)
    (by simpa only [ENNReal.ofReal_ofNat] using circularGaussianDensity_le_two)
    (by rw [circularGaussianDensity_withDensity]; exact circularComplexGaussian_sq_integrable)
    (by rw [circularGaussianDensity_withDensity]; exact circularComplexGaussian_secondMoment.le)
  simpa only [circularGaussianDensity_withDensity] using h

end CircularLawSection6
