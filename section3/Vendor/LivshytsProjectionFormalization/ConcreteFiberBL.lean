/- Source snapshot: upstream-sources/livshyts-projection-formalization/LivshytsProjectionFormalization/ConcreteFiberBL.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.LivshytsProjectionFormalization.KernelCoordinateFrame

/-!
# Geometric Brascamp--Lieb on projection fibers

This file applies the abstract geometric Brascamp--Lieb inequality to the
concrete Parseval frame formed by the nonzero coordinate maps on a subspace.
The frame hypotheses are discharged by `KernelCoordinateFrame` rather than
being included in a projection-density assumption.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace LivshytsProjectionFormalization

/-- Geometric Brascamp--Lieb with an arbitrary finite index type and a real
Euclidean source. -/
def RealFiniteGeometricBrascampLieb : Prop :=
  ∀ {ι : Type} [Fintype ι] {m : ℕ}
    (B : ι → (CoordinateSpace ℝ m →L[ℝ] ℝ)) (c : ι → ℝ),
    (∀ i, 0 ≤ c i) →
    (∀ i, c i ≤ 1) →
    (∀ i, ‖B i‖ = 1) →
    (∀ x, ∑ i, c i * ‖B i x‖ ^ 2 = ‖x‖ ^ 2) →
    ∀ (f : ι → ℝ → ℝ≥0∞),
      (∀ i, Measurable (f i)) →
      (∫⁻ x, ∏ i, (f i (B i x)).rpow (c i) ∂volume) ≤
        ∏ i, (∫⁻ t, f i t ∂volume).rpow (c i)

/-- Geometric Brascamp--Lieb with an arbitrary finite index type and a complex
Euclidean source. -/
def ComplexFiniteGeometricBrascampLieb : Prop :=
  ∀ {ι : Type} [Fintype ι] {m : ℕ}
    (B : ι → (CoordinateSpace ℂ m →L[ℂ] ℂ)) (c : ι → ℝ),
    (∀ i, 0 ≤ c i) →
    (∀ i, c i ≤ 1) →
    (∀ i, ‖B i‖ = 1) →
    (∀ x, ∑ i, c i * ‖B i x‖ ^ 2 = ‖x‖ ^ 2) →
    ∀ (f : ι → ℂ → ℝ≥0∞),
      (∀ i, Measurable (f i)) →
      (∫⁻ x, ∏ i, (f i (B i x)).rpow (c i) ∂volume) ≤
        ∏ i, (∫⁻ z, f i z ∂volume).rpow (c i)

structure FiniteGeometricBrascampLiebInput : Prop where
  real : RealFiniteGeometricBrascampLieb
  complex : ComplexFiniteGeometricBrascampLieb

theorem real_kernelCoordinate_geometricBL
    (hGBL : RealFiniteGeometricBrascampLieb) {n : ℕ}
    (W : Submodule ℝ (CoordinateSpace ℝ n))
    (f : ActiveKernelCoordinate W → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i,
        (f i (normalizedKernelCoordinateMap W i x)).rpow
          (kernelCoordinateWeight W i) ∂volume) ≤
      ∏ i, (∫⁻ t, f i t ∂volume).rpow (kernelCoordinateWeight W i) := by
  exact hGBL (ι := ActiveKernelCoordinate W) (m := Module.finrank ℝ W)
    (fun i => normalizedKernelCoordinateMap W i)
    (fun i => kernelCoordinateWeight W i)
    (kernelCoordinateWeight_nonnegative W)
    (kernelCoordinateWeight_le_one W)
    (normalizedKernelCoordinateMap_norm W)
    (kernelCoordinateFrame_identity W) f hf

theorem complex_kernelCoordinate_geometricBL
    (hGBL : ComplexFiniteGeometricBrascampLieb) {n : ℕ}
    (W : Submodule ℂ (CoordinateSpace ℂ n))
    (f : ActiveKernelCoordinate W → ℂ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i,
        (f i (normalizedKernelCoordinateMap W i x)).rpow
          (kernelCoordinateWeight W i) ∂volume) ≤
      ∏ i, (∫⁻ z, f i z ∂volume).rpow (kernelCoordinateWeight W i) := by
  exact hGBL (ι := ActiveKernelCoordinate W) (m := Module.finrank ℂ W)
    (fun i => normalizedKernelCoordinateMap W i)
    (fun i => kernelCoordinateWeight W i)
    (kernelCoordinateWeight_nonnegative W)
    (kernelCoordinateWeight_le_one W)
    (normalizedKernelCoordinateMap_norm W)
    (kernelCoordinateFrame_identity W) f hf

end LivshytsProjectionFormalization

