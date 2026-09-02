import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Compact support and bounds for the planar Laplacian

These elementary support facts are used when the Green--Girko integral is
restricted to a finite observation ball in Tao--Vu, Theorem 2.1.
-/

open Metric Set
open MeasureTheory
open InnerProductSpace Laplacian
open scoped InnerProductSpace

noncomputable section

namespace TaoVuReplacement

/-- Taking the planar Laplacian cannot enlarge compact support. -/
theorem hasCompactSupport_laplacian {f : ℂ → ℝ}
    (hfc : HasCompactSupport f) : HasCompactSupport (Δ f) := by
  apply hfc.mono'
  intro z hz
  apply support_iteratedFDeriv_subset (𝕜 := ℝ) (f := f) 2
  intro hzero
  apply hz
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp [hzero]

/-- A `C²` function has a continuous planar Laplacian. -/
theorem continuous_laplacian {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Δ f) := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  have hbase : Continuous (fun z ↦ iteratedFDeriv ℝ 2 f z) :=
    hf.continuous_iteratedFDeriv le_rfl
  fun_prop

/-- The Laplacian of a compactly supported `C²` function is globally
bounded. -/
theorem exists_norm_laplacian_le {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) : ∃ C : ℝ, ∀ z, ‖Δ f z‖ ≤ C :=
  (continuous_laplacian hf).bounded_above_of_compact_support
    (hasCompactSupport_laplacian hfc)

/-- The Laplacian vanishes off some closed ball of nonnegative radius. -/
theorem exists_laplacian_zero_outside_closedBall {f : ℂ → ℝ}
    (hfc : HasCompactSupport f) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∉ closedBall (0 : ℂ) R, Δ f z = 0 := by
  obtain ⟨r, hr⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
      (hasCompactSupport_laplacian hfc).isCompact.isBounded
  let R : ℝ := max r 0
  have hsubset : tsupport (Δ f) ⊆ closedBall (0 : ℂ) R :=
    hr.trans (closedBall_subset_closedBall (le_max_left r 0))
  refine ⟨R, le_max_right r 0, fun z hz ↦ ?_⟩
  by_contra hz_ne
  exact hz (hsubset (subset_tsupport (Δ f) hz_ne))

/-- Once the Laplacian vanishes off an observation ball, a Green integral
over the plane is exactly the corresponding set integral over that ball. -/
theorem integral_laplacian_mul_eq_integral_closedBall
    (f g : ℂ → ℝ) (R : ℝ)
    (hout : ∀ z ∉ closedBall (0 : ℂ) R, Δ f z = 0) :
    (∫ z : ℂ, Δ f z * g z) =
      ∫ z in closedBall (0 : ℂ) R, Δ f z * g z := by
  rw [← integral_indicator measurableSet_closedBall]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ closedBall (0 : ℂ) R
  · simp [hz]
  · simp [hz, hout z hz]

end TaoVuReplacement

