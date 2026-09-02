import TaoVuReplacement.TestFunctionApproximation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# From smooth tests to vague convergence

The Green--Girko calculation naturally gives convergence for smooth compactly
supported test functions.  This file uses the uniform approximation and the
mass-one estimate from `TestFunctionApproximation` to obtain the exact vague
convergence conclusion of Tao--Vu, Theorem 2.1.
-/

open Filter MeasureTheory
open scoped ContDiff Topology

noncomputable section

namespace TaoVuReplacement

/-- Difference of the real empirical spectral test functionals. -/
def esdDifference {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (f : ℂ → ℝ) : ℝ :=
  realEsdTest A f - realEsdTest B f

/-- Convergence in probability for every smooth compactly supported test
implies convergence in probability for every continuous compactly supported
test.  This is the last approximation step in Tao--Vu §3.6. -/
theorem vague_inProbability_of_smooth
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : ∀ k : ℕ, Ω → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hsmooth : ∀ g : (ℂ → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      TendstoInMeasure P
        (fun k sample ↦ esdDifference (A k sample) (B k sample) g) atTop 0) :
    ∀ f : (ℂ → ℝ), Continuous f → HasCompactSupport f →
      TendstoInMeasure P
        (fun k sample ↦ esdDifference (A k sample) (B k sample) f) atTop 0 := by
  intro f hf hfc
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  obtain ⟨g, hg_smooth, hg_compact, hgf⟩ :=
    exists_contDiff_hasCompactSupport_dist_lt f hf hfc (show 0 < ε / 8 by positivity)
  have hfg : ∀ z, |f z - g z| ≤ ε / 8 := by
    intro z
    have := (hgf z).le
    simpa only [Real.dist_eq, abs_sub_comm] using this
  have hG := tendstoInMeasure_iff_norm.mp (hsmooth g hg_smooth hg_compact)
    (ε / 2) (half_pos hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hG
    (fun _ ↦ zero_le) ?_
  intro k
  apply measure_mono
  intro sample hsample
  simp only [Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hsample ⊢
  change ε ≤ |esdDifference (A k sample) (B k sample) f| at hsample
  have hclose :
      |esdDifference (A k sample) (B k sample) f -
        esdDifference (A k sample) (B k sample) g| ≤ ε / 4 := by
    have h := abs_esdDifference_sub_le_of_forall
      (A k sample) (B k sample) f g (by positivity) hfg
    calc
      |esdDifference (A k sample) (B k sample) f -
          esdDifference (A k sample) (B k sample) g| ≤
          2 * (ε / 8) := by simpa only [esdDifference] using h
      _ = ε / 4 := by ring
  have htri :
      |esdDifference (A k sample) (B k sample) f| ≤
        |esdDifference (A k sample) (B k sample) f -
          esdDifference (A k sample) (B k sample) g| +
        |esdDifference (A k sample) (B k sample) g| := by
    calc
      |esdDifference (A k sample) (B k sample) f| =
          |(esdDifference (A k sample) (B k sample) f -
            esdDifference (A k sample) (B k sample) g) +
            esdDifference (A k sample) (B k sample) g| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  change ε / 2 ≤ |esdDifference (A k sample) (B k sample) g|
  linarith

/-- Almost-sure convergence on one common event for every smooth compactly
supported test implies the corresponding one-event vague convergence for all
continuous compactly supported tests. -/
theorem vague_almostSurely_of_smooth
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : ∀ k : ℕ, Ω → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hsmooth : ∀ᵐ sample ∂P, ∀ g : (ℂ → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      Tendsto (fun k ↦ esdDifference (A k sample) (B k sample) g) atTop (𝓝 0)) :
    ∀ᵐ sample ∂P, ∀ f : (ℂ → ℝ), Continuous f → HasCompactSupport f →
      Tendsto (fun k ↦ esdDifference (A k sample) (B k sample) f) atTop (𝓝 0) := by
  filter_upwards [hsmooth] with sample hsmooth_sample
  intro f hf hfc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg_smooth, hg_compact, hgf⟩ :=
    exists_contDiff_hasCompactSupport_dist_lt f hf hfc (show 0 < ε / 8 by positivity)
  have hfg : ∀ z, |f z - g z| ≤ ε / 8 := by
    intro z
    have := (hgf z).le
    simpa only [Real.dist_eq, abs_sub_comm] using this
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hsmooth_sample g hg_smooth hg_compact)
    (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk ↦ ?_⟩
  have hclose :
      |esdDifference (A k sample) (B k sample) f -
        esdDifference (A k sample) (B k sample) g| ≤ ε / 4 := by
    have h := abs_esdDifference_sub_le_of_forall
      (A k sample) (B k sample) f g (by positivity) hfg
    calc
      |esdDifference (A k sample) (B k sample) f -
          esdDifference (A k sample) (B k sample) g| ≤
          2 * (ε / 8) := by simpa only [esdDifference] using h
      _ = ε / 4 := by ring
  have hgsmall : |esdDifference (A k sample) (B k sample) g| < ε / 2 := by
    simpa only [dist_zero_right, Real.norm_eq_abs] using hN k hk
  simp only [dist_zero_right, Real.norm_eq_abs]
  calc
    |esdDifference (A k sample) (B k sample) f| =
        |(esdDifference (A k sample) (B k sample) f -
          esdDifference (A k sample) (B k sample) g) +
          esdDifference (A k sample) (B k sample) g| := by ring_nf
    _ ≤ |esdDifference (A k sample) (B k sample) f -
          esdDifference (A k sample) (B k sample) g| +
        |esdDifference (A k sample) (B k sample) g| := abs_add_le _ _
    _ < ε / 4 + ε / 2 := add_lt_add_of_le_of_lt hclose hgsmall
    _ < ε := by linarith

end TaoVuReplacement

