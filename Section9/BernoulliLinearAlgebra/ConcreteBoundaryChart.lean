import BernoulliLinearAlgebra.ConcreteBoundaryGlobal
import BernoulliLinearAlgebra.ConcreteBoundaryComparison
import BernoulliLinearAlgebra.ChartPerturbation

/-!
# Concrete boundary comparison on and beyond the chart

This file assembles the actual five-block determinant coefficient, its
proved continuity, the concrete endpoint conditioning, and the explicit
upper-left perturbation.  The only input is a uniform terminal comparison
for the literal three-block coefficient function; the seven-block matching
module supplies that input.
-/

open scoped Matrix Matrix.Norms.Frobenius

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix

variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

local instance concreteChartSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W => (toLex x : W ⊕ₗ W)) toLex.injective

/-- The complete chart package for the literal boundary determinant and
literal three-block terminal coefficient.  No scaling, conditioning, or
continuity hypothesis is left to the caller. -/
def concreteGlobalChartBounds
    (z : ℂ) (CL BR : Matrix W W ℂ) (Kc : ℝ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (hTerminal : TerminalCoefficientComparison
      (threeBlockTerminalCoefficientOnPacket (w := W) z) Kc) :
    ChartVolumeBounds (Matrix (W ⊕ W) (W ⊕ W) ℂ) where
  chart := invertibleUpperLeftChart
  coefficient := globalBoundaryCoefficientNorm z CL BR
  volume := gramVolume
  lowerConstant := (Kc * endpointExteriorConstant CL BR)⁻¹
  upperConstant := Kc * endpointExteriorConstant CL BR
  continuous_coefficient :=
    continuous_globalBoundaryCoefficientNorm z CL BR
  continuous_volume := continuous_gramVolume_matrix
  bounds_on_chart := by
    intro Theta hTheta
    rcases hTheta with ⟨_hFull, h11⟩
    change IsUnit Theta.toBlocks₁₁.det at h11
    have h := concrete_endpoint_boundary_volume_on_chart
      Theta.toBlocks₁₁ Theta.toBlocks₁₂ Theta.toBlocks₂₁ Theta.toBlocks₂₂
      CL BR (globalBoundaryCoefficientNorm z CL BR Theta)
      (threeBlockTerminalCoefficientOnPacket (w := W) z) Kc
      h11 hCL hBR hTerminal
      (globalBoundaryCoefficientNorm_eq_on_chart z CL BR Theta h11)
    simpa [boundaryRelation, Matrix.fromBlocks_toBlocks] using h

/-- The coefficient--volume comparison for every invertible boundary
relation, including points where the upper-left block is singular. -/
theorem globalBoundaryCoefficientNorm_bounds_of_isUnit
    (z : ℂ) (CL BR : Matrix W W ℂ) (Kc : ℝ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (hTerminal : TerminalCoefficientComparison
      (threeBlockTerminalCoefficientOnPacket (w := W) z) Kc)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (hTheta : IsUnit Theta.det) :
    (Kc * endpointExteriorConstant CL BR)⁻¹ * gramVolume Theta ≤
        globalBoundaryCoefficientNorm z CL BR Theta ∧
      globalBoundaryCoefficientNorm z CL BR Theta ≤
        (Kc * endpointExteriorConstant CL BR) * gramVolume Theta := by
  exact (concreteGlobalChartBounds z CL BR Kc hCL hBR hTerminal).bounds_at_limit
    (invertibleUpperLeftChart_sequentiallyDenseAt Theta hTheta)

/-- Quantitative chart package driven by the endpoint-event bounds used in
the paper.  Jacobi supplies every inverse exterior bound internally. -/
def concreteGlobalChartBoundsOfHodgeBounds
    (z : ℂ) (CL BR : Matrix W W ℂ) (Kc D L : ℝ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (hD : 0 ≤ D)
    (hdet : ‖(endpointFactor CL BR).det‖⁻¹ ≤ D)
    (hforward : ∀ q : ℕ,
      ‖compound q (endpointFactor CL BR)‖ ≤ L)
    (hTerminal : TerminalCoefficientComparison
      (threeBlockTerminalCoefficientOnPacket (w := W) z) Kc) :
    ChartVolumeBounds (Matrix (W ⊕ W) (W ⊕ W) ℂ) where
  chart := invertibleUpperLeftChart
  coefficient := globalBoundaryCoefficientNorm z CL BR
  volume := gramVolume
  lowerConstant := (Kc * max 1 (max L (D * L)))⁻¹
  upperConstant := Kc * max 1 (max L (D * L))
  continuous_coefficient :=
    continuous_globalBoundaryCoefficientNorm z CL BR
  continuous_volume := continuous_gramVolume_matrix
  bounds_on_chart := by
    intro Theta hTheta
    rcases hTheta with ⟨_hFull, h11⟩
    change IsUnit Theta.toBlocks₁₁.det at h11
    have h := concrete_endpoint_boundary_volume_on_chart_of_hodgeBounds
      Theta.toBlocks₁₁ Theta.toBlocks₁₂ Theta.toBlocks₂₁ Theta.toBlocks₂₂
      CL BR (globalBoundaryCoefficientNorm z CL BR Theta)
      (threeBlockTerminalCoefficientOnPacket (w := W) z)
      Kc D L h11 hCL hBR hD hdet hforward hTerminal
      (globalBoundaryCoefficientNorm_eq_on_chart z CL BR Theta h11)
    simpa [boundaryRelation, Matrix.fromBlocks_toBlocks] using h

/-- Paper-quantitative coefficient--volume comparison for every invertible
boundary relation, after extending from the dense chart. -/
theorem globalBoundaryCoefficientNorm_bounds_of_hodgeBounds
    (z : ℂ) (CL BR : Matrix W W ℂ) (Kc D L : ℝ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (hD : 0 ≤ D)
    (hdet : ‖(endpointFactor CL BR).det‖⁻¹ ≤ D)
    (hforward : ∀ q : ℕ,
      ‖compound q (endpointFactor CL BR)‖ ≤ L)
    (hTerminal : TerminalCoefficientComparison
      (threeBlockTerminalCoefficientOnPacket (w := W) z) Kc)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (hTheta : IsUnit Theta.det) :
    (Kc * max 1 (max L (D * L)))⁻¹ * gramVolume Theta ≤
        globalBoundaryCoefficientNorm z CL BR Theta ∧
      globalBoundaryCoefficientNorm z CL BR Theta ≤
        (Kc * max 1 (max L (D * L))) * gramVolume Theta := by
  exact (concreteGlobalChartBoundsOfHodgeBounds z CL BR Kc D L
    hCL hBR hD hdet hforward hTerminal).bounds_at_limit
      (invertibleUpperLeftChart_sequentiallyDenseAt Theta hTheta)

/-- The same concrete coefficient norm is strictly positive for every
invertible boundary relation. -/
theorem globalBoundaryCoefficientNorm_pos_of_isUnit
    (z : ℂ) (CL BR : Matrix W W ℂ) (Kc : ℝ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (hTerminal : TerminalCoefficientComparison
      (threeBlockTerminalCoefficientOnPacket (w := W) z) Kc)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (hTheta : IsUnit Theta.det) :
    0 < globalBoundaryCoefficientNorm z CL BR Theta := by
  let B := concreteGlobalChartBounds z CL BR Kc hCL hBR hTerminal
  apply B.coefficient_pos_at_limit
    (invertibleUpperLeftChart_sequentiallyDenseAt Theta hTheta)
  · exact inv_pos.mpr <| mul_pos
      (lt_of_lt_of_le zero_lt_one hTerminal.one_le)
      (lt_of_lt_of_le zero_lt_one
        (one_le_exactExteriorConditioningConstant (endpointFactor CL BR)))
  · exact gramVolume_pos Theta

end BernoulliLinearAlgebra
