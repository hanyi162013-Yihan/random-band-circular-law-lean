import CircularLawSection4.PaperIndicatorFreshRows
import CircularLawSection4.MultiaffineUntruncated

/-!
# Complex bounded-density estimate for the paper's fresh-row polynomial

The deterministic bridge in `PaperIndicatorFreshRows` produces the actual
fresh alternating exterior trace as a complex multiaffine polynomial.  This
module substitutes the manuscript's positive indicator profile and an IID
complex atom with bounded planar density into the already proved
multiaffine logarithmic estimate.
-/

open scoped ENNReal MeasureTheory
open MeasureTheory Set

noncomputable section

namespace CircularLawSection4
namespace PaperIndicatorWeights

variable {d : ℕ} {c₀ C₀ : ℝ}

/-- Positivity of the paper profile and of the frozen exterior family gives
an actually nonzero top coefficient for one explicitly selected fresh
polynomial. -/
theorem exists_paperIndicatorFreshPolynomial_topCoeff_pos
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxEntryNorm B) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        0 < ‖MultiAffine.topCoeff
          (profile.paperIndicatorFreshPolynomial center z atoms B r I J)‖ := by
  obtain ⟨r, I, J, hcoefficient⟩ :=
    profile.exists_paperIndicatorFreshPolynomial_topCoeff_maxEntry_lower_bound
      center z atoms B
  refine ⟨r, I, J, ?_⟩
  have hden : 0 < (d + 2 : ℝ) := by positivity
  have hbmin : 0 < Real.sqrt (c₀ / (d + 2 : ℝ)) :=
    Real.sqrt_pos.2 (div_pos hc₀ hden)
  exact (mul_pos (pow_pos hbmin (d + 1)) hB).trans_le hcoefficient

/-- The manuscript's complex fresh polynomial has a null zero set and the
full untruncated negative-log estimate under a bounded planar density.

The selected degree and coordinates are produced internally from the frozen
exterior family `B`; the displayed polynomial evaluates to the genuine
alternating fresh trace by `eval_paperIndicatorFreshPolynomial`. -/
theorem exists_paperIndicatorFreshPolynomial_complex_positiveLogLoss_withDensity
    (profile : PaperIndicatorWeights (d + 1) c₀ C₀)
    (hc₀ : 0 < c₀)
    (center : Fin (d + 1)) (z : ℂ)
    (atoms : Fin (d + 1) → ResetLabel (d + 1) → ℂ)
    (B : (q : ExteriorDegree (d + 1)) →
      Matrix (ExteriorIndex (d + 1) q) (ExteriorIndex (d + 1) q) ℂ)
    (hB : 0 < exteriorFamilyMaxEntryNorm B)
    (f : ℂ → ℝ≥0∞) [IsProbabilityMeasure (volume.withDensity f)]
    {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ᵐ w ∂(volume : Measure ℂ), f w ≤ ENNReal.ofReal L) :
    ∃ r : ExteriorDegree (d + 1),
      ∃ I J : ExteriorIndex (d + 1) r,
        let p :=
          profile.paperIndicatorFreshPolynomial center z atoms B r I J
        iidMeasure (volume.withDensity f) (d + 1)
              {x | ‖p.eval x‖ = 0} = 0 ∧
          (fun x => positiveLogLoss ‖p.topCoeff‖ ‖p.eval x‖) =ᵐ[
            iidMeasure (volume.withDensity f) (d + 1)]
              (fun x => max 0 (Real.log (‖p.topCoeff‖ / ‖p.eval x‖))) ∧
          Integrable
            (fun x => positiveLogLoss ‖p.topCoeff‖ ‖p.eval x‖)
            (iidMeasure (volume.withDensity f) (d + 1)) ∧
          ∫ x, positiveLogLoss ‖p.topCoeff‖ ‖p.eval x‖
                ∂iidMeasure (volume.withDensity f) (d + 1) ≤
            (Real.log
                  (max 1 (((d + 1 : ℕ) : ℝ) * (Real.pi * L))) + 1) /
              (((2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
  obtain ⟨r, I, J, htop⟩ :=
    profile.exists_paperIndicatorFreshPolynomial_topCoeff_pos
      hc₀ center z atoms B hB
  refine ⟨r, I, J, ?_⟩
  exact iid_complex_positiveLogLoss_withDensity f hL hf
    (profile.paperIndicatorFreshPolynomial center z atoms B r I J) htop

end PaperIndicatorWeights
end CircularLawSection4
