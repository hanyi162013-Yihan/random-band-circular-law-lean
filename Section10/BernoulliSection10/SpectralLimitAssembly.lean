import BernoulliSection10.PhysicalReplacement

/-! # Passing a proved replacement comparison to its reference spectral limit -/

open Filter MeasureTheory Topology

namespace BernoulliSection10.DiskReference

open BernoulliSection10.Replacement BernoulliSection10.ProbabilityLimits TaoVuReplacement

theorem esd_limit_of_replacement
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ → ℕ}
    (X Y : ∀ k, Ω → Matrix (Fin (d k + 1)) (Fin (d k + 1)) ℂ)
    (limitTest : (ℂ → ℝ) → ℝ)
    (hReplacement : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure P (fun k ω => esdDifference (X k ω) (Y k ω) f) atTop 0)
    (hComparison : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure P (fun k ω => realEsdTest (Y k ω) f) atTop (fun _ => limitTest f)) :
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      TendstoInMeasure P (fun k ω => realEsdTest (X k ω) f) atTop (fun _ => limitTest f) := by
  intro f hf hc
  have hdiff := (tendstoInMeasure_iff_tri P _ 0).1 (hReplacement f hf hc)
  have hY := (tendstoInMeasure_iff_tri P _ (limitTest f)).1 (hComparison f hf hc)
  apply (tendstoInMeasure_iff_tri P _ (limitTest f)).2
  simpa only [esdDifference, sub_add_cancel, zero_add] using hdiff.add (fun _ => P) hY

end BernoulliSection10.DiskReference
