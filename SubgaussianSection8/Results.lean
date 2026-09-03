import SubgaussianSection8.LogPotential
import SubgaussianSection8.CircularReduction
import SubgaussianSection8.Section3Integration

/-!
# Section 8 for a fixed real subgaussian law

The law has mean zero, variance one, and any fixed finite subgaussian
parameter. The independent entries are scaled by `1 / sqrt(3W)` and the
exact matrix dimension is `N = (s + 3) W`. No support, density, or symmetry
assumption is imposed. Cook and Nguyen remain explicit inputs. Section 3.8
is supplied by its concrete proof, under its named upstream literature inputs.
-/

open Filter MeasureTheory
open scoped Topology

noncomputable section

namespace SubgaussianSection8
open BernoulliSection8

open BernoulliSection9 BernoulliSection10
open BernoulliSection10.DiskReference BernoulliSection10.Replacement ShortRingAnchor TaoVuReplacement

theorem section8_subgaussian_log_potential (Ξ : Atom)
    (cook : CookInput Ξ) (nguyen : NguyenBottomSingularInput.{0, 0})
    (hNguyen : Ξ.parameter ≤ nguyen.subgaussianBound)
    (section3 : Section3UpstreamInputs Ξ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hs : ∀ n, 0 < s n)
    (hWtop : Tendsto W atTop atTop)
    (hband : Tendsto
      (fun n => (W n : ℝ) / Real.log (((s n + 3) * W n : ℕ) : ℝ)) atTop atTop)
    (z : ℂ) :
    TendstoInMeasure (sequenceLaw Ξ)
      (fun n ω => normalizedShiftLogDet (matrix (W n) (s n) ω) z)
      atTop (fun _ => circularLogPotential z) := by
  have hlog : Tendsto (fun n => Real.log (((s n + 3) * W n : ℕ) : ℝ) / (W n : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, inv_div] using tendsto_inv_atTop_zero.comp hband
  exact (subgaussian_log_potential Ξ) cook nguyen hNguyen
    (section3_input Ξ section3) W s hW hs hWtop hlog z

/-- Weak convergence in probability of the empirical eigenvalue measure
of the actual cyclic band matrix with independent subgaussian entries to the uniform disk. -/
theorem section8_subgaussian_circular_law (Ξ : Atom)
    (cook : CookInput Ξ) (nguyen : NguyenBottomSingularInput.{0, 0})
    (hNguyen : Ξ.parameter ≤ nguyen.subgaussianBound)
    (section3 : Section3UpstreamInputs Ξ)
    (W s : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hs : ∀ n, 0 < s n)
    (hWtop : Tendsto W atTop atTop)
    (hband : Tendsto
      (fun n => (W n : ℝ) / Real.log (((s n + 3) * W n : ℕ) : ℝ)) atTop atTop)
    (f : BoundedContinuousFunction ℂ ℝ) :
    TendstoInMeasure (sequenceLaw Ξ)
      (fun n ω => realEsdTest (matrix (W n) (s n) ω) f) atTop
      (fun _ => ∫ z, f z ∂circularMeasure) :=
  circular_law_of_log_potential Ξ W s hW hWtop
    (ae_of_all _ fun z =>
      (section8_subgaussian_log_potential Ξ) cook nguyen hNguyen section3 W s hW hs hWtop hband z) f

end SubgaussianSection8
