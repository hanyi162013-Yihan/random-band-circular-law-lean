import CircularLawSections56.Section5.TriangularProbability
import CircularLawSections56.Section5.PressureLifting
import Mathlib.Order.Interval.Finset.Nat

/-! # Uniformity over all mesoscopic cell lengths

This is the manuscript's violating-sequence argument in exact finite-supremum
form. The probabilistic input is a Section 3 anchor for every admissible choice
of lengths; the deterministic uniform limit is derived using the two finite
Section 4 L1 comparisons, not supplied as an additional assumption.
-/

open Filter MeasureTheory Topology

noncomputable section
set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace CircularLawSections56.Section5

theorem finite_uniform_limit_of_all_selections
    {ι : ℕ → Type*} (S : ∀ n, Finset (ι n)) (hS : ∀ n, (S n).Nonempty)
    (F : ∀ n, ι n → ℝ) (a : ℝ)
    (hChoice : ∀ j : ∀ n, ι n, (∀ n, j n ∈ S n) →
      Tendsto (fun n => F n (j n)) atTop (𝓝 a)) :
    Tendsto (fun n => finiteSignedMax (S n) (hS n) (fun j => |F n j - a|))
      atTop (𝓝 0) := by
  classical
  choose j hj heq using fun n => exists_eq_finiteSignedMax (hS n) (fun j => |F n j - a|)
  have ht := ((hChoice j hj).sub_const a).abs
  simpa only [heq, sub_self, abs_zero] using ht

theorem uniform_calibration_of_triangular_anchors_and_two_seams
    {ι : ℕ → Type*} (S : ∀ n, Finset (ι n)) (hS : ∀ n, (S n).Nonempty)
    {Ω : ∀ n, ι n → Type*} [∀ n j, MeasurableSpace (Ω n j)]
    (μ : ∀ n j, Measure (Ω n j)) [∀ n j, IsProbabilityMeasure (μ n j)]
    (anchor pressure : ∀ n j, Ω n j → ℝ) (mean : ∀ n, ι n → ℝ)
    (target : ℝ) (seam fluctuation : ℕ → ℝ)
    (hAnchor : ∀ j : ∀ n, ι n, (∀ n, j n ∈ S n) →
      TendstoInProbabilityTri (fun n => μ n (j n)) (fun n => anchor n (j n)) target)
    (hSeamInt : ∀ n j, j ∈ S n →
      Integrable (fun ω => |anchor n j ω - pressure n j ω|) (μ n j))
    (hSeam : ∀ n j, j ∈ S n →
      (∫ ω, |anchor n j ω - pressure n j ω| ∂μ n j) ≤ seam n)
    (hFluctuationInt : ∀ n j, j ∈ S n →
      Integrable (fun ω => |pressure n j ω - mean n j|) (μ n j))
    (hFluctuation : ∀ n j, j ∈ S n →
      (∫ ω, |pressure n j ω - mean n j| ∂μ n j) ≤ fluctuation n)
    (hSeamZero : Tendsto seam atTop (𝓝 0))
    (hFluctuationZero : Tendsto fluctuation atTop (𝓝 0)) :
    Tendsto (fun n => finiteSignedMax (S n) (hS n) (fun j => |mean n j - target|))
      atTop (𝓝 0) := by
  apply finite_uniform_limit_of_all_selections S hS mean target
  intro j hj
  exact deterministic_center_tendsto_of_tri_anchor_and_two_L1_seams
    (fun n => μ n (j n)) (fun n => anchor n (j n)) (fun n => pressure n (j n))
    (fun n => mean n (j n)) seam fluctuation target (hAnchor j hj)
    (fun n => hSeamInt n (j n) (hj n)) (fun n => hSeam n (j n) (hj n))
    (fun n => hFluctuationInt n (j n) (hj n)) (fun n => hFluctuation n (j n) (hj n))
    hSeamZero hFluctuationZero

theorem mesoscopic_interval_nonempty (m₀ : ℕ) :
    (Finset.Icc m₀ (2 * m₀)).Nonempty := by
  exact ⟨m₀, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩

/-- The literal supremum over all integer lengths in `[m₀,2m₀]`, rather than
only the one balanced length selected for the final matrix. -/
theorem mesoscopic_supremum_zero_of_all_length_calibrations
    (m₀ : ℕ → ℕ) (mean : ℕ → ℕ → ℝ) (target : ℝ)
    (hChoice : ∀ m : ℕ → ℕ, (∀ n, m₀ n ≤ m n ∧ m n ≤ 2 * m₀ n) →
      Tendsto (fun n => mean n (m n)) atTop (𝓝 target)) :
    Tendsto (fun n => finiteSignedMax (Finset.Icc (m₀ n) (2 * m₀ n))
      (mesoscopic_interval_nonempty (m₀ n)) (fun m => |mean n m - target|)) atTop (𝓝 0) := by
  apply finite_uniform_limit_of_all_selections _ _ mean target
  intro m hm
  exact hChoice m (fun n => Finset.mem_Icc.1 (hm n))

/-- Uniform calibration immediately works along every admissible length chooser;
this reverse implication makes the finite-supremum interpretation explicit. -/
theorem calibration_along_lengths_of_mesoscopic_supremum
    (m₀ : ℕ → ℕ) (mean : ℕ → ℕ → ℝ) (target : ℝ)
    (hUniform : Tendsto (fun n => finiteSignedMax (Finset.Icc (m₀ n) (2 * m₀ n))
      (mesoscopic_interval_nonempty (m₀ n)) (fun m => |mean n m - target|)) atTop (𝓝 0))
    (m : ℕ → ℕ) (hm : ∀ n, m₀ n ≤ m n ∧ m n ≤ 2 * m₀ n) :
    Tendsto (fun n => mean n (m n)) atTop (𝓝 target) := by
  have habs : Tendsto (fun n => |mean n (m n) - target|) atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) (fun n =>
      le_finiteSignedMax (mesoscopic_interval_nonempty (m₀ n))
        (fun m => |mean n m - target|) (Finset.mem_Icc.2 (hm n))) hUniform
  exact tendsto_iff_dist_tendsto_zero.2 (by simpa only [Real.dist_eq] using habs)

end CircularLawSections56.Section5
