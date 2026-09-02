import BernoulliLinearAlgebra.BoundaryVolume
import BernoulliLinearAlgebra.ConcreteConditioning
import BernoulliLinearAlgebra.GramPositivity

/-!
# Boundary comparison with the actual endpoint factor

This specializes the Section 9.5 volume comparison to
`E = diag(C_L,B_R)`.  Its exterior-conditioning witness and constant are
constructed internally from the two endpoint invertibility hypotheses.
-/

open scoped Matrix Matrix.Norms.Frobenius

noncomputable section

namespace BernoulliLinearAlgebra

variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

local instance concreteBoundarySumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W => (toLex x : W ⊕ₗ W)) toLex.injective

/-- The internally constructed common exterior constant for the paper's
endpoint matrix `E = diag(C_L,B_R)`. -/
def endpointExteriorConstant (CL BR : Matrix W W ℂ) : ℝ :=
  exactExteriorConditioningConstant (endpointFactor CL BR)

/-- Section 9.5 on the invertible upper-left chart, with the concrete
endpoint matrix and its conditioning no longer passed as certificates. -/
theorem concrete_endpoint_boundary_volume_on_chart
    (Theta11 Theta12 Theta21 Theta22 CL BR : Matrix W W ℂ)
    (boundaryCoefficient : ℝ)
    (terminalCoefficient : Matrix (W ⊕ W) (W ⊕ W) ℂ → ℝ)
    (Kc : ℝ)
    (h11 : IsUnit Theta11.det)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (hTerminal : TerminalCoefficientComparison terminalCoefficient Kc)
    (hScale : boundaryCoefficient = ‖Theta11.det‖ *
      terminalCoefficient
        (endpointFactor CL BR *
          boundaryGraphS Theta11 Theta12 Theta21 Theta22)) :
    (Kc * endpointExteriorConstant CL BR)⁻¹ *
        gramVolume (boundaryRelation Theta11 Theta12 Theta21 Theta22) ≤
      boundaryCoefficient ∧
    boundaryCoefficient ≤ (Kc * endpointExteriorConstant CL BR) *
      gramVolume (boundaryRelation Theta11 Theta12 Theta21 Theta22) := by
  exact boundary_coefficient_volume_on_chart
    Theta11 Theta12 Theta21 Theta22
    (endpointFactor CL BR) boundaryCoefficient terminalCoefficient
    Kc (endpointExteriorConstant CL BR) h11
    (endpointFactor_exactConditioning CL BR hCL hBR)
    hTerminal hScale

/-- The same chart comparison with the paper's quantitative endpoint-event
bounds as inputs.  The inverse exterior bounds are derived internally by
Hodge--Jacobi, so no `ExteriorConditioning` or complementary-minor
certificate is supplied by the caller. -/
theorem concrete_endpoint_boundary_volume_on_chart_of_hodgeBounds
    (Theta11 Theta12 Theta21 Theta22 CL BR : Matrix W W ℂ)
    (boundaryCoefficient : ℝ)
    (terminalCoefficient : Matrix (W ⊕ W) (W ⊕ W) ℂ → ℝ)
    (Kc D L : ℝ)
    (h11 : IsUnit Theta11.det)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (hD : 0 ≤ D)
    (hdet : ‖(endpointFactor CL BR).det‖⁻¹ ≤ D)
    (hforward : ∀ q : ℕ,
      ‖compound q (endpointFactor CL BR)‖ ≤ L)
    (hTerminal : TerminalCoefficientComparison terminalCoefficient Kc)
    (hScale : boundaryCoefficient = ‖Theta11.det‖ *
      terminalCoefficient
        (endpointFactor CL BR *
          boundaryGraphS Theta11 Theta12 Theta21 Theta22)) :
    (Kc * max 1 (max L (D * L)))⁻¹ *
        gramVolume (boundaryRelation Theta11 Theta12 Theta21 Theta22) ≤
      boundaryCoefficient ∧
    boundaryCoefficient ≤ (Kc * max 1 (max L (D * L))) *
      gramVolume (boundaryRelation Theta11 Theta12 Theta21 Theta22) := by
  exact boundary_coefficient_volume_on_chart
    Theta11 Theta12 Theta21 Theta22
    (endpointFactor CL BR) boundaryCoefficient terminalCoefficient
    Kc (max 1 (max L (D * L))) h11
    (endpointFactor_conditioning_of_hodgeBounds CL BR hCL hBR hD hdet hforward)
    hTerminal hScale

/-- Strict positivity of the same concrete boundary coefficient. -/
theorem concrete_endpoint_boundary_coefficient_pos
    (Theta11 Theta12 Theta21 Theta22 CL BR : Matrix W W ℂ)
    (boundaryCoefficient : ℝ)
    (terminalCoefficient : Matrix (W ⊕ W) (W ⊕ W) ℂ → ℝ)
    (Kc : ℝ)
    (h11 : IsUnit Theta11.det)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (hTerminal : TerminalCoefficientComparison terminalCoefficient Kc)
    (hScale : boundaryCoefficient = ‖Theta11.det‖ *
      terminalCoefficient
        (endpointFactor CL BR *
          boundaryGraphS Theta11 Theta12 Theta21 Theta22)) :
    0 < boundaryCoefficient := by
  have hbounds := concrete_endpoint_boundary_volume_on_chart
    Theta11 Theta12 Theta21 Theta22 CL BR boundaryCoefficient
    terminalCoefficient Kc h11 hCL hBR hTerminal hScale
  have hKc : 0 < Kc := lt_of_lt_of_le zero_lt_one hTerminal.one_le
  have hKe : 0 < endpointExteriorConstant CL BR :=
    lt_of_lt_of_le zero_lt_one
      (one_le_exactExteriorConditioningConstant (endpointFactor CL BR))
  exact coefficient_pos_of_gramVolume_lower
    (boundaryRelation Theta11 Theta12 Theta21 Theta22)
    (inv_pos.mpr (mul_pos hKc hKe)) hbounds.1

end BernoulliLinearAlgebra
