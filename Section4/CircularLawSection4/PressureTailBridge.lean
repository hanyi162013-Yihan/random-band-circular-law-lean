import CircularLawSection4.ExponentialTailSecondMoment
import CircularLawSection4.PressureL2Bridge

/-!
# Exponential replacement tails to pressure concentration

This module composes the generic exponential-tail `L²` closure with the
common-center replacement bridge and finite-uniform Efron--Stein theorem.
It isolates the remaining paper-specific input as two explicit tail bounds:
one for the original row observable and one for a freshly replaced row.
-/

open scoped ENNReal

namespace CircularLawSection4

/-- The explicit second-moment cap produced by an `A exp (-q t)` tail. -/
noncomputable def exponentialTailSecondMomentBound (A q : ℝ) : ℝ :=
  4 * ((Real.log (max 1 A) + 1) / q) ^ 2

/-- A global exponential tail on a finite uniform cube gives the precise
uniform-average squared bound needed by the replacement bridge. -/
theorem uniformAverage_sq_le_exponentialTailSecondMomentBound
    {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
    (Z : UniformCube α n → ℝ) (hZ0 : ∀ x, 0 ≤ Z x)
    (A q : ℝ) (hA : 0 ≤ A) (hq : 0 < q)
    (htail : ∀ t : ℝ, 0 < t →
      uniformCubeMeasure n {x | t < Z x} ≤
        ENNReal.ofReal (A * Real.exp (-(q * t)))) :
    uniformAverage (fun x => Z x ^ 2) ≤
      exponentialTailSecondMomentBound A q := by
  obtain ⟨_, hsquare⟩ :=
    memLp_two_and_integral_sq_le_of_exponential_tail
      (uniformCubeMeasure n) Z (measurable_of_finite Z) hZ0 A q hA hq htail
  rw [uniformCubeMeasure, integral_uniformOfFintype_eq_uniformAverage] at hsquare
  simpa only [exponentialTailSecondMomentBound] using hsquare

/-- Conditional exponential tails for both the old and independently
replaced coordinate imply the full finite-uniform pressure bound.

The first tail is with respect to the entire old cube.  The second is with
respect to a fresh uniform coordinate after the outside sample `x` is frozen.
Thus this theorem is the direct compositional target for the manuscript's
one-row operator-affine small-ball estimate. -/
theorem pressure_maximal_concentration_uniform_of_exponential_replacement_tails
    {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (n W : ℕ) (Y : Fin (2 * W).succ → UniformCube α n → ℝ)
    (center : Fin (2 * W).succ → Fin n → UniformCube α n → ℝ)
    (A q : ℝ) (hA : 0 ≤ A) (hq : 0 < q)
    (holdTail : ∀ r i t, 0 < t →
      uniformCubeMeasure n {x | t < |Y r x - center r i x|} ≤
        ENNReal.ofReal (A * Real.exp (-(q * t))))
    (hnewTail : ∀ r i x t, 0 < t →
      (PMF.uniformOfFintype α).toMeasure
          {a' | t < |Y r (uniformCubeReplace x i a') - center r i x|} ≤
        ENNReal.ofReal (A * Real.exp (-(q * t)))) :
    (∫ ω, maxCenteredAbs (uniformCubeMeasure n) Y ω
        ∂(uniformCubeMeasure n)) ≤
      Real.sqrt (((2 * W + 1 : ℕ) : ℝ) *
        ((1 / 2 : ℝ) * (n : ℝ) *
          (4 * exponentialTailSecondMomentBound A q))) := by
  apply pressure_maximal_concentration_uniform_of_center_sq_average_le
    n W Y center
  · intro r i
    have hsquare := uniformAverage_sq_le_exponentialTailSecondMomentBound
      (fun x => |Y r x - center r i x|) (fun x => abs_nonneg _)
      A q hA hq (holdTail r i)
    simpa only [sq_abs] using hsquare
  · intro r i
    calc
      uniformAverage (fun x => uniformAverage (fun a' : α =>
          (Y r (uniformCubeReplace x i a') - center r i x) ^ 2)) ≤
          uniformAverage (fun _x : UniformCube α n =>
            exponentialTailSecondMomentBound A q) := by
        apply uniformAverage_mono
        intro x
        obtain ⟨_, hsquare⟩ :=
          memLp_two_and_integral_sq_le_of_exponential_tail
            (PMF.uniformOfFintype α).toMeasure
            (fun a' => |Y r (uniformCubeReplace x i a') - center r i x|)
            (measurable_of_finite _) (fun a' => abs_nonneg _)
            A q hA hq (hnewTail r i x)
        rw [integral_uniformOfFintype_eq_uniformAverage] at hsquare
        simpa only [sq_abs, exponentialTailSecondMomentBound] using hsquare
      _ = exponentialTailSecondMomentBound A q :=
        uniformAverage_const _

end CircularLawSection4
