import BernoulliLinearAlgebra.ThreeBlockZeroComparison
import BernoulliLinearAlgebra.ThreeBlockShiftTranslation
import BernoulliLinearAlgebra.ConcreteBoundaryChart
import BernoulliLinearAlgebra.ConcreteBoundaryExterior
import BernoulliLinearAlgebra.ConcreteRowScaling

/-!
# Fully instantiated terminal and boundary comparisons

This file closes the terminal-certificate interface for the raw
unit-entry-weight, finite-constant comparisons in Sections 9.4--9.5.
The literal three-block mask supplies the zero-shift comparison, and the
explicit diagonal coefficient translation transports it to every spectral
parameter.  Consequently the global boundary estimates below no longer ask
the caller for a `MaskExpansionCertificate` or an abstract
`TerminalCoefficientComparison`. The full weighted-profile version and
uniform asymptotic constants of Lemmas 7.5 and 7.7 are not asserted here.
-/

open scoped Matrix Matrix.Norms.Frobenius

noncomputable section

namespace BernoulliLinearAlgebra

variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

local instance concreteBoundaryFinalSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W => (toLex x : W ⊕ₗ W)) toLex.injective

/-- The completely explicit finite comparison constant for the literal
three-block terminal polynomial at spectral parameter `z`. -/
def threeBlockConcreteComparisonConstant (z : ℂ) : ℝ :=
  threeBlockZeroComparisonConstant (w := W) *
    threeBlockTranslationFactor (w := W) z

/-- The raw unit-entry-weight finite-constant core of Lemma 7.5, at an
arbitrary spectral parameter and with no remaining mask certificate. -/
theorem threeBlockTerminalCoefficientOnPacket_concreteComparison
    (z : ℂ) :
    TerminalCoefficientComparison
      (threeBlockTerminalCoefficientOnPacket (w := W) z)
      (threeBlockConcreteComparisonConstant (W := W) z) := by
  exact threeBlockTerminalCoefficientComparison_of_zero z
    (threeBlockZeroComparisonConstant (w := W))
    (threeBlockTerminalCoefficientOnPacket_zero_comparison (w := W))

/-- The global dense-chart package with the literal terminal comparison
installed internally. -/
def concreteGlobalChartBoundsFullyInstantiated
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det) :
    ChartVolumeBounds (Matrix (W ⊕ W) (W ⊕ W) ℂ) :=
  concreteGlobalChartBounds z CL BR
    (threeBlockConcreteComparisonConstant (W := W) z) hCL hBR
    (threeBlockTerminalCoefficientOnPacket_concreteComparison (W := W) z)

/-- The coefficient--volume comparison for every invertible boundary
relation, with all terminal mask and translation steps instantiated. -/
theorem globalBoundaryCoefficientNorm_bounds_fullyInstantiated
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (hTheta : IsUnit Theta.det) :
    (threeBlockConcreteComparisonConstant (W := W) z *
        endpointExteriorConstant CL BR)⁻¹ * gramVolume Theta ≤
        globalBoundaryCoefficientNorm z CL BR Theta ∧
      globalBoundaryCoefficientNorm z CL BR Theta ≤
        (threeBlockConcreteComparisonConstant (W := W) z *
          endpointExteriorConstant CL BR) * gramVolume Theta := by
  exact globalBoundaryCoefficientNorm_bounds_of_isUnit z CL BR
    (threeBlockConcreteComparisonConstant (W := W) z) hCL hBR
    (threeBlockTerminalCoefficientOnPacket_concreteComparison (W := W) z)
    Theta hTheta

/-- The quantitative chart package from the endpoint Hodge-event bounds,
again with the terminal comparison installed internally. -/
def concreteGlobalChartBoundsOfHodgeBoundsFullyInstantiated
    (z : ℂ) (CL BR : Matrix W W ℂ) (D L : ℝ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (hD : 0 ≤ D)
    (hdet : ‖(endpointFactor CL BR).det‖⁻¹ ≤ D)
    (hforward : ∀ q : ℕ, ‖compound q (endpointFactor CL BR)‖ ≤ L) :
    ChartVolumeBounds (Matrix (W ⊕ W) (W ⊕ W) ℂ) :=
  concreteGlobalChartBoundsOfHodgeBounds z CL BR
    (threeBlockConcreteComparisonConstant (W := W) z) D L
    hCL hBR hD hdet hforward
    (threeBlockTerminalCoefficientOnPacket_concreteComparison (W := W) z)

/-- Quantitative global comparison given explicit determinant and
Frobenius compound bounds, with no terminal-certificate argument left
to the application. This does not establish the probabilistic event
or the uniform asymptotic constant of Lemma 7.7. -/
theorem globalBoundaryCoefficientNorm_bounds_of_hodgeBounds_fullyInstantiated
    (z : ℂ) (CL BR : Matrix W W ℂ) (D L : ℝ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (hD : 0 ≤ D)
    (hdet : ‖(endpointFactor CL BR).det‖⁻¹ ≤ D)
    (hforward : ∀ q : ℕ, ‖compound q (endpointFactor CL BR)‖ ≤ L)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (hTheta : IsUnit Theta.det) :
    (threeBlockConcreteComparisonConstant (W := W) z *
        max 1 (max L (D * L)))⁻¹ * gramVolume Theta ≤
        globalBoundaryCoefficientNorm z CL BR Theta ∧
      globalBoundaryCoefficientNorm z CL BR Theta ≤
        (threeBlockConcreteComparisonConstant (W := W) z *
          max 1 (max L (D * L))) * gramVolume Theta := by
  exact globalBoundaryCoefficientNorm_bounds_of_hodgeBounds z CL BR
    (threeBlockConcreteComparisonConstant (W := W) z) D L
    hCL hBR hD hdet hforward
    (threeBlockTerminalCoefficientOnPacket_concreteComparison (W := W) z)
    Theta hTheta

/-- Strict positivity of the actual global boundary coefficient norm, with
the concrete terminal comparison supplied internally. -/
theorem globalBoundaryCoefficientNorm_pos_fullyInstantiated
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (hTheta : IsUnit Theta.det) :
    0 < globalBoundaryCoefficientNorm z CL BR Theta := by
  exact globalBoundaryCoefficientNorm_pos_of_isUnit z CL BR
    (threeBlockConcreteComparisonConstant (W := W) z) hCL hBR
    (threeBlockTerminalCoefficientOnPacket_concreteComparison (W := W) z)
    Theta hTheta

end BernoulliLinearAlgebra
