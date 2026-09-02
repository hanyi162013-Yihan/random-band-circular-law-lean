import CircularLawSection4.PaperIndicatorFreshRows
import CircularLawSection4.PaperIndicatorFreshComplex
import CircularLawSection4.RealInputComplexMultiaffine

/-!
# Real-atom logarithmic estimate for the paper's fresh-row polynomial

The spectral parameter and all frozen coefficients in the manuscript's
fresh-row polynomial are complex, even when the fresh atoms themselves are
real.  This module combines the deterministic nonvanishing selector from
`PaperIndicatorFreshComplex` with the real-input estimates from
`RealInputComplexMultiaffine`.

Both results below choose the exterior degree and matrix coordinates
internally.  Consequently the selected fresh polynomial has nonzero complex
top coefficient and may be evaluated directly on IID real inputs.
-/

open scoped ENNReal MeasureTheory
open MeasureTheory Set

noncomputable section

namespace CircularLawSection4
namespace PaperIndicatorWeights

variable {d : ℕ} {c₀ C₀ : ℝ}

/-- For a real IID atom satisfying an interval concentration bound, one of
the manuscript's complex fresh polynomials has a null zero set and a finite,
explicitly bounded untruncated negative logarithmic moment.

The frozen atoms and spectral parameter may remain complex; only the
`d + 1` selected fresh coordinates are sampled from `ν`. -/
theorem exists_paperIndicatorFreshPolynomial_realInput_complex_positiveLogLoss_of_intervalBound
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxEntryNorm B)
    (ν : Measure ℝ) [SFinite ν] [IsProbabilityMeasure ν]
    {L : ℝ} (hL : 0 ≤ L)
    (hν : RealIntervalBound ν (ENNReal.ofReal L)) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        let p :=
          profile.paperIndicatorFreshPolynomial center z atoms B r I J
        iidMeasure ν (d + 1) {x | ‖realInputEval p x‖ = 0} = 0 ∧
          (fun x => positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖) =ᵐ[
            iidMeasure ν (d + 1)]
              (fun x => max 0
                (Real.log (‖p.topCoeff‖ / ‖realInputEval p x‖))) ∧
          Integrable
            (fun x => positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖)
            (iidMeasure ν (d + 1)) ∧
          ∫ x, positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖
                ∂iidMeasure ν (d + 1) ≤
            (Real.log
                  (max 1 (((d + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
              (((1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
  obtain ⟨r, I, J, htop⟩ :=
    profile.exists_paperIndicatorFreshPolynomial_topCoeff_pos
      hc₀ center z atoms B hB
  refine ⟨r, I, J, ?_⟩
  exact iid_realInput_complex_positiveLogLoss_of_intervalBound
    ν hL hν
      (profile.paperIndicatorFreshPolynomial center z atoms B r I J) htop

/-- Bounded-density presentation of the real-atom, complex-spectral
fresh-polynomial logarithmic estimate.  The exterior degree and coordinates
with nonzero top coefficient are selected internally from `B`. -/
theorem exists_paperIndicatorFreshPolynomial_realInput_complex_positiveLogLoss_withDensity
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxEntryNorm B)
    (f : ℝ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ x ∂(volume : Measure ℝ), f x ≤ ENNReal.ofReal L) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        let p :=
          profile.paperIndicatorFreshPolynomial center z atoms B r I J
        iidMeasure (volume.withDensity f) (d + 1)
              {x | ‖realInputEval p x‖ = 0} = 0 ∧
          (fun x => positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖) =ᵐ[
            iidMeasure (volume.withDensity f) (d + 1)]
              (fun x => max 0
                (Real.log (‖p.topCoeff‖ / ‖realInputEval p x‖))) ∧
          Integrable
            (fun x => positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖)
            (iidMeasure (volume.withDensity f) (d + 1)) ∧
          ∫ x, positiveLogLoss ‖p.topCoeff‖ ‖realInputEval p x‖
                ∂iidMeasure (volume.withDensity f) (d + 1) ≤
            (Real.log
                  (max 1 (((d + 1 : ℕ) : ℝ) * (4 * L))) + 1) /
              (((1 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
  obtain ⟨r, I, J, htop⟩ :=
    profile.exists_paperIndicatorFreshPolynomial_topCoeff_pos
      hc₀ center z atoms B hB
  refine ⟨r, I, J, ?_⟩
  exact iid_realInput_complex_positiveLogLoss_withDensity
    f hL hf
      (profile.paperIndicatorFreshPolynomial center z atoms B r I J) htop

end PaperIndicatorWeights
end CircularLawSection4
