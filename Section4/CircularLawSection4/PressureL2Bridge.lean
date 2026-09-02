import CircularLawSection4.PressureEfronStein

/-!
# From one-row logarithmic `L²` control to replacement energy

This module records the algebraic step used after the manuscript's
operator-affine logarithm lemma.  If both the original observable and its
one-coordinate replacement have squared distance at most `V`, on average,
from a common frozen center, then their replacement energy is at most `4V`.
Combined with the finite-product Efron--Stein theorem this closes the pressure
estimate without a pointwise bounded-difference hypothesis.
-/

namespace CircularLawSection4

/-- Two `L²` bounds around the same frozen center control the squared
difference between an observable and one coordinate replacement. -/
theorem uniformResamplingEnergy_le_four_mul_of_center_sq_average_le
    {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
    (f center : UniformCube α n → ℝ) (i : Fin n) {V : ℝ}
    (hold : uniformAverage (fun x => (f x - center x) ^ 2) ≤ V)
    (hnew : uniformAverage (fun x => uniformAverage (fun a' : α =>
      (f (uniformCubeReplace x i a') - center x) ^ 2)) ≤ V) :
    uniformResamplingEnergy f i ≤ 4 * V := by
  rw [uniformResamplingEnergy_eq_replace_average]
  have hpoint (x : UniformCube α n) :
      uniformAverage (fun a' : α =>
          (f x - f (uniformCubeReplace x i a')) ^ 2) ≤
        2 * (f x - center x) ^ 2 +
          2 * uniformAverage (fun a' : α =>
            (f (uniformCubeReplace x i a') - center x) ^ 2) := by
    calc
      uniformAverage (fun a' : α =>
          (f x - f (uniformCubeReplace x i a')) ^ 2) ≤
          uniformAverage (fun a' : α =>
            2 * (f x - center x) ^ 2 +
              2 * (f (uniformCubeReplace x i a') - center x) ^ 2) := by
        apply uniformAverage_mono
        intro a'
        nlinarith [sq_nonneg
          ((f x - center x) +
            (f (uniformCubeReplace x i a') - center x))]
      _ = 2 * (f x - center x) ^ 2 +
          2 * uniformAverage (fun a' : α =>
            (f (uniformCubeReplace x i a') - center x) ^ 2) := by
        rw [uniformAverage_add, uniformAverage_const,
          uniformAverage_const_mul]
  calc
    uniformAverage (fun x => uniformAverage (fun a' : α =>
        (f x - f (uniformCubeReplace x i a')) ^ 2)) ≤
        uniformAverage (fun x =>
          2 * (f x - center x) ^ 2 +
            2 * uniformAverage (fun a' : α =>
              (f (uniformCubeReplace x i a') - center x) ^ 2)) :=
      uniformAverage_mono hpoint
    _ = 2 * uniformAverage (fun x => (f x - center x) ^ 2) +
        2 * uniformAverage (fun x => uniformAverage (fun a' : α =>
          (f (uniformCubeReplace x i a') - center x) ^ 2)) := by
      rw [uniformAverage_add, uniformAverage_const_mul,
        uniformAverage_const_mul]
    _ ≤ 4 * V := by linarith

/-- Finite-uniform pressure concentration driven by the `L²` output of an
operator-affine replacement estimate.  The centers may depend on both the
exterior degree and the coordinate being replaced. -/
theorem pressure_maximal_concentration_uniform_of_center_sq_average_le
    {α : Type*} [Fintype α] [Nonempty α]
    (n W : ℕ) (Y : Fin (2 * W).succ → UniformCube α n → ℝ)
    (center : Fin (2 * W).succ → Fin n → UniformCube α n → ℝ)
    {V : ℝ}
    (hold : ∀ r i,
      uniformAverage (fun x => (Y r x - center r i x) ^ 2) ≤ V)
    (hnew : ∀ r i,
      uniformAverage (fun x => uniformAverage (fun a' : α =>
        (Y r (uniformCubeReplace x i a') - center r i x) ^ 2)) ≤ V) :
    (∫ ω, maxCenteredAbs (uniformCubeMeasure n) Y ω
        ∂(uniformCubeMeasure n)) ≤
      Real.sqrt (((2 * W + 1 : ℕ) : ℝ) *
        ((1 / 2 : ℝ) * (n : ℝ) * (4 * V))) := by
  apply pressure_maximal_concentration_uniform_resampling n W Y
  intro r i
  exact uniformResamplingEnergy_le_four_mul_of_center_sq_average_le
    (Y r) (center r i) i (hold r i) (hnew r i)

end CircularLawSection4
