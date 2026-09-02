import BernoulliSection8.RademacherLogPotential
import BernoulliSection8.RademacherCircularReduction

/-!
# Section 8: caller-facing Bernoulli results

For `s ≥ 1`, the number of block sites is `m=s+3 ≥ 4` and the exact
matrix dimension is `N=(s+3)W`. Each allowed atom is an independent
symmetric sign, with the physical factor `1/sqrt(3W)` built into
`rademacherMatrix`. The bandwidth assumptions below are the paper's
`W → infinity` and `W/log N → infinity`.

The only unproved analytic inputs accepted by these statements are the
explicit Nguyen, Cook, and Section 3 objects. Pressure, reset, terminal,
measurability, energy, and circular-law reduction data are all constructed.
-/

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace BernoulliSection8

open BernoulliSection9 BernoulliSection10
open BernoulliSection10.DiskReference BernoulliSection10.Replacement ShortRingAnchor TaoVuReplacement

theorem section8_bernoulli_log_potential
    (cook : CookDeformedSquareInput.{0, 0}) (nguyen : NguyenBottomSingularInput.{0, 0})
    (hNguyen : 1 ≤ nguyen.subgaussianBound)
    (section3 : Section3SubgaussianHighBandInput rademacherLaw 1)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hs : ∀ n, 0 < s n)
    (hWtop : Tendsto W atTop atTop)
    (hband : Tendsto
      (fun n => (W n : ℝ) / Real.log (((s n + 3) * W n : ℕ) : ℝ)) atTop atTop)
    (z : ℂ) :
    TendstoInMeasure rademacherSequenceLaw
      (fun n ω => normalizedShiftLogDet (rademacherMatrix (W n) (s n) ω) z)
      atTop (fun _ => circularLogPotential z) := by
  have hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, inv_div] using tendsto_inv_atTop_zero.comp hband
  exact rademacher_log_potential cook nguyen hNguyen section3 W s hW hs hWtop hlog z

/-- Weak convergence in probability of the empirical eigenvalue measure
of the actual cyclic band matrix with symmetric Bernoulli entries to the uniform disk. -/
theorem section8_bernoulli_circular_law
    (cook : CookDeformedSquareInput.{0, 0}) (nguyen : NguyenBottomSingularInput.{0, 0})
    (hNguyen : 1 ≤ nguyen.subgaussianBound)
    (section3 : Section3SubgaussianHighBandInput rademacherLaw 1)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hs : ∀ n, 0 < s n)
    (hWtop : Tendsto W atTop atTop)
    (hband : Tendsto
      (fun n => (W n : ℝ) / Real.log (((s n + 3) * W n : ℕ) : ℝ)) atTop atTop)
    (f : BoundedContinuousFunction ℂ ℝ) :
    TendstoInMeasure rademacherSequenceLaw
      (fun n ω => realEsdTest (rademacherMatrix (W n) (s n) ω) f) atTop
      (fun _ => ∫ z, f z ∂circularMeasure) :=
  rademacher_circular_law_of_log_potential W s hW hWtop
    (ae_of_all _ fun z =>
      section8_bernoulli_log_potential cook nguyen hNguyen section3 W s hW hs hWtop hband z) f

end BernoulliSection8
