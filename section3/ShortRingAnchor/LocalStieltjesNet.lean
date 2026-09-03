import ShortRingAnchor.ProbabilityModes
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma 3.5: an explicit horizontal net for every fixed compact interval

The single-point v3 estimate has no restriction on the real part of eta.
Consequently the radius-five two-dimensional net need not be generalized:
at one fixed imaginary part a one-dimensional floor grid suffices.
This module proves the grid, its size, interpolation, and probability union bound.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace ShortRingAnchor

/-- Lemma 3.5 net size, for the horizontal interval `[-R,R]`. -/
def horizontalGridSize (R delta : ℝ) : ℕ := Nat.ceil (2 * R / delta) + 1

/-- Lemma 3.5 net centers in real coordinates; the common imaginary part is separate. -/
def horizontalGridCenter (R delta : ℝ) (i : Fin (horizontalGridSize R delta)) : ℝ :=
  -R + (i.val : ℝ) * delta

/-- Lemma 3.5: the explicit grid covers every fixed compact interval. -/
theorem horizontalGrid_cover {R delta u : ℝ} (hdelta : 0 < delta)
    (hu : u ∈ Icc (-R) R) :
    ∃ i : Fin (horizontalGridSize R delta),
      |u - horizontalGridCenter R delta i| ≤ delta := by
  have hx : 0 ≤ u + R := by linarith [hu.1]
  have hi : Nat.floor ((u + R) / delta) < horizontalGridSize R delta := by
    apply Nat.lt_succ_of_le
    apply Nat.floor_le_of_le
    exact (div_le_div_of_nonneg_right (by linarith [hu.2]) hdelta.le).trans (Nat.le_ceil _)
  refine ⟨⟨Nat.floor ((u + R) / delta), hi⟩, ?_⟩
  have hlo := Nat.floor_le (div_nonneg hx hdelta.le)
  have hhi := Nat.lt_floor_add_one ((u + R) / delta)
  have hlo' := (le_div_iff₀ hdelta).mp hlo
  have hhi' := (div_lt_iff₀ hdelta).mp hhi
  simp only [horizontalGridCenter]
  rw [abs_of_nonneg (by linarith)]
  nlinarith

/-- Lemma 3.5: a fixed radius changes only the constant in the net cardinality. -/
theorem horizontalGridSize_le {R delta : ℝ} (hR : 0 ≤ R) (hdelta : 0 < delta) :
    (horizontalGridSize R delta : ℝ) ≤ 2 * R / delta + 2 := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ 2 * R / delta from
    div_nonneg (mul_nonneg (by norm_num) hR) hdelta.le)
  simp only [horizontalGridSize, Nat.cast_add, Nat.cast_one]
  linarith

/-- Lemma 3.5 interpolation. For Stieltjes transforms one uses `L = v⁻²`.
Only the two random matrix transforms need continuity; no free-law regularity is assumed here. -/
theorem horizontalGrid_comparison {R delta L E : ℝ}
    (hdelta : 0 < delta) (hL : 0 ≤ L) (f g : ℝ → ℂ)
    (hf : ∀ u w, ‖f u - f w‖ ≤ L * |u - w|)
    (hg : ∀ u w, ‖g u - g w‖ ≤ L * |u - w|)
    (hgrid : ∀ i : Fin (horizontalGridSize R delta),
      ‖f (horizontalGridCenter R delta i) - g (horizontalGridCenter R delta i)‖ ≤ E)
    {u : ℝ} (hu : u ∈ Icc (-R) R) :
    ‖f u - g u‖ ≤ E + 2 * L * delta := by
  obtain ⟨i, hi⟩ := horizontalGrid_cover hdelta hu
  let w := horizontalGridCenter R delta i
  have h1 := hf u w
  have h2 := hg w u
  have h3 := hgrid i
  have h4 : L * |u - w| ≤ L * delta := mul_le_mul_of_nonneg_left hi hL
  rw [abs_sub_comm w u] at h2
  calc
    ‖f u - g u‖ ≤ ‖f u - f w‖ + ‖f w - g u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖f u - f w‖ + (‖f w - g w‖ + ‖g w - g u‖) :=
      add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ E + 2 * L * delta := by linarith

/-- Lemma 3.5: the pointwise probability estimate becomes a compact uniform estimate.
The only probability loss is the explicitly computed number of horizontal grid points. -/
theorem measure_horizontal_comparison_bad_le
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    {R delta L E : ℝ} (hdelta : 0 < delta) (hL : 0 ≤ L)
    (f g : Omega → ℝ → ℂ) (q : ℝ≥0∞)
    (hf : ∀ sample u w, ‖f sample u - f sample w‖ ≤ L * |u - w|)
    (hg : ∀ sample u w, ‖g sample u - g sample w‖ ≤ L * |u - w|)
    (hpoint : ∀ i : Fin (horizontalGridSize R delta), mu {sample |
      E < ‖f sample (horizontalGridCenter R delta i) -
        g sample (horizontalGridCenter R delta i)‖} ≤ q) :
    mu {sample | ∃ u ∈ Icc (-R) R, E + 2 * L * delta < ‖f sample u - g sample u‖} ≤
      (horizontalGridSize R delta : ℝ≥0∞) * q := by
  classical
  let bad := fun i : Fin (horizontalGridSize R delta) => {sample |
    E < ‖f sample (horizontalGridCenter R delta i) -
      g sample (horizontalGridCenter R delta i)‖}
  have hsub : {sample | ∃ u ∈ Icc (-R) R,
      E + 2 * L * delta < ‖f sample u - g sample u‖} ⊆ ⋃ i, bad i := by
    intro sample hsample
    by_contra hnot
    have hgrid : ∀ i, ‖f sample (horizontalGridCenter R delta i) -
        g sample (horizontalGridCenter R delta i)‖ ≤ E := by
      intro i
      exact le_of_not_gt (fun hi => hnot (Set.mem_iUnion.mpr ⟨i, hi⟩))
    obtain ⟨u, hu, hsmall⟩ := hsample
    exact not_lt_of_ge (horizontalGrid_comparison hdelta hL
      (f sample) (g sample) (hf sample) (hg sample) hgrid hu) hsmall
  calc
    _ ≤ mu (⋃ i, bad i) := measure_mono hsub
    _ ≤ ∑ i, mu (bad i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin (horizontalGridSize R delta), q := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = _ := by simp

end ShortRingAnchor
