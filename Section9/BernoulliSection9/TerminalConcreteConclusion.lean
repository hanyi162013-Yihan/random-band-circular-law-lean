import BernoulliSection9.CoordinateTwoCookTruncated
import BernoulliSection9.TerminalConcreteEventBounds
import BernoulliSection9.TerminalConcreteCrossBounds
import BernoulliSection9.TerminalConcreteMeasurability
import BernoulliSection9.TerminalConcreteRRQR
import BernoulliSection9.TerminalSpectralBridge
import BernoulliSection9.TerminalUniformCook
import BernoulliSection9.TerminalResult
import Mathlib.Tactic

/-!
# Certificate-free concrete terminal small-ball conclusion

The public data in this module are exactly the row-scaled packet matrix,
the spectral shift, the global iid family, and Cook's approved input.  The
RRQR selections, the two complete squares, both conditioning sigma-fields,
the CUR deformations, and both norm truncations are definitions internal to
the proof.
-/

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

open MeasureTheory BernoulliLinearAlgebra

namespace TerminalAssembly

universe u

/-- The canonical exposure threshold used simultaneously by the terminal
value estimate and the reverse estimate. -/
def terminalConcreteExposureThreshold
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W : Nat}
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (t : Real) : Real := packetCoordinateMaxThreshold X t

/-- Purely numerical large-`W` obligations.  Crucially this structure does
not mention `Q`, any RRQR output, any realized random matrix, a sigma-field,
or a deformation.  Each field is a scalar inequality between the canonical
polynomial bounds defined in `TerminalConcreteScales`. -/
structure PacketTerminalCanonicalLargeWConditions
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W : Nat}
    (cook : CookDeformedSquareInput)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (Kz : Nat) (t : Real) : Prop where
  subgaussian_bound : X.subgaussianParameter <= cook.subgaussianBound
  W_large : 9 <= W
  t_nonneg : 0 <= t
  shift_bound : ‖z‖ <= (W : Real) ^ Kz
  pivot_small :
    terminalPivotInverseScale W (terminalCanonicalThreshold W Kz) *
        terminalUniformDeltaScale W z
          (terminalConcreteExposureThreshold X t) <= (2 : Real)⁻¹
  first_polynomial :
    terminalUniformFirstDeformationScale W
        (terminalCanonicalThreshold W Kz)
        (terminalConcreteExposureThreshold X t) z <=
      ((W / 3 : Nat) : Real) ^ terminalCanonicalFirstCookExponent Kz
  second_polynomial :
    terminalUniformSecondDeformationScale cook W Kz
        (terminalCanonicalThreshold W Kz)
        (terminalConcreteExposureThreshold X t) z <=
      ((W / 3 : Nat) : Real) ^
        terminalCanonicalSecondCookExponent cook Kz

/-- Uniform determinant factor.  It depends only on `W`, `Kz`, and Cook's
fixed exponent function; in particular it is independent of `Q` and of the
RRQR rank. -/
def terminalUniformDeterminantFactor
    (cook : CookDeformedSquareInput) (W Kz : Nat) : Real :=
  (2 : Real)⁻¹ ^ (2 * W) *
    ((((2 * W : Nat) : Real) ^ strongRRQRExponent)⁻¹ ^ (2 * W)) *
    ((((3 * W : Nat) : Real) ^
      (-cook.beta (terminalCanonicalFirstCookExponent Kz))) ^ (3 * W)) *
    ((((3 * W : Nat) : Real) ^
      (-cook.beta (terminalCanonicalSecondCookExponent cook Kz))) ^ (3 * W))

/-- Uniform threshold factor converting the selected large-singular-value
product back to Gram volume. -/
def terminalUniformGramThresholdFactor (W Kz : Nat) : Real :=
  (2 * terminalCanonicalThreshold W Kz) ^ (2 * W)

/-- A nonnegative, `Q`-uniform logarithmic value loss.  The `max 0` makes
nonnegativity definitional while only enlarging the loss. -/
def terminalUniformValueLoss
    (cook : CookDeformedSquareInput) (W Kz : Nat) : Real :=
  max 0
    (-Real.log (terminalUniformDeterminantFactor cook W Kz) +
      Real.log (terminalUniformGramThresholdFactor W Kz))

theorem terminalUniformValueLoss_nonneg
    (cook : CookDeformedSquareInput) (W Kz : Nat) :
    0 <= terminalUniformValueLoss cook W Kz := by
  exact le_max_left _ _

/-- The fixed `Q`-uniform two-Cook failure probability used by the final
packet theorem. -/
def terminalUniformBadProbability
    (cook : CookDeformedSquareInput) (W Kz : Nat) (t : Real) : Real :=
  Real.exp (-t) +
    (uniformCookFailureBound
      (cook.cookC (terminalCanonicalFirstCookExponent Kz))
      (cook.cookc (terminalCanonicalFirstCookExponent Kz)) W +
    uniformCookFailureBound
      (cook.cookC (terminalCanonicalSecondCookExponent cook Kz))
      (cook.cookc (terminalCanonicalSecondCookExponent cook Kz)) W)

/-- The single terminal loss used for every outer matrix `Q` of packet
width `W`.  It combines the uniform determinant/Gram loss with the already
proved sharp-support reverse loss. -/
def terminalUniformBaseLoss
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W : Nat}
    (cook : CookDeformedSquareInput) (Kz : Nat) (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (t : Real) : Real :=
  Real.log (threeBlockConcreteComparisonConstant (W := Fin W) z) +
    (terminalUniformValueLoss cook W Kz +
      terminalReverseLoss (Fin W) z (terminalConcreteExposureThreshold X t))

theorem terminalUniformBaseLoss_nonneg
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {W : Nat}
    (cook : CookDeformedSquareInput) (Kz : Nat) (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (t : Real) :
    0 <= terminalUniformBaseLoss cook Kz z X t := by
  have hcomparison : 0 <=
      Real.log (threeBlockConcreteComparisonConstant (W := Fin W) z) :=
    Real.log_nonneg
      (threeBlockTerminalCoefficientOnPacket_concreteComparison
        (W := Fin W) z).one_le
  exact add_nonneg hcomparison (add_nonneg
    (terminalUniformValueLoss_nonneg cook W Kz)
    (terminalReverseLoss_nonneg (Fin W) z
      (terminalConcreteExposureThreshold X t)))

/-- Certificate-free, `Q`-uniform caller-facing target for the concrete
terminal argument.  This is a definition of the proposition proved below;
the only non-paper datum in its parameter list is Cook's explicitly approved
literature input. -/
def PacketTerminalConcreteConclusion
    {Omega : Type*} [MeasurableSpace Omega]
    (cook : CookDeformedSquareInput)
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (W Kz : Nat) (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (t : Real) :=
  forall Q : Matrix (PacketOuter (Fin W)) (PacketOuter (Fin W)) Complex,
    PacketTerminalSmallBallResult mu Q z X
      (terminalUniformBaseLoss cook Kz z X t)
      (terminalUniformBadProbability cook W Kz t) t

end TerminalAssembly

end BernoulliSection9
