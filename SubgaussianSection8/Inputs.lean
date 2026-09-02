import SubgaussianSection8.Atom
import BernoulliSection9.ExternalInputs

/-! Cook's approved estimate, with its range covering the fixed atom parameter. -/
noncomputable section
namespace SubgaussianSection8
open BernoulliSection9

structure CookInput (A : Atom) extends CookDeformedSquareInput.{0, 0} where
  parameter_le : A.parameter ≤ subgaussianBound

instance (A : Atom) : Coe (CookInput A) CookDeformedSquareInput.{0, 0} :=
  ⟨CookInput.toCookDeformedSquareInput⟩

end SubgaussianSection8
