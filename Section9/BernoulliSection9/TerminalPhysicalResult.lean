import BernoulliSection9.TerminalConcreteConclusion
import BernoulliSection9.TerminalConcreteScaling

/-!
# Physical-normalization terminal small-ball result

This module is the caller-facing form of the concrete terminal theorem in
the original normalization.  The variance-one theorem is applied to the
internally row-scaled outer matrix `sigma • Q`; the common determinant
factor is then removed by the exact scaling identities of
`TerminalConcreteScaling`.
-/

open scoped Matrix

noncomputable section

namespace BernoulliSection9

open MeasureTheory BernoulliLinearAlgebra

namespace TerminalAssembly

universe u

/-- The certificate-free concrete terminal theorem in physical
normalization.  Its only analytic input is the already exposed Cook input;
the RRQR data, masks, deformations, and conditioning fields remain internal
to `PacketTerminalConcreteConclusion`. -/
noncomputable def physicalPacketTerminalSmallBallConclusion
    {Omega : Type u} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W Kz : Nat} {z sigma : Complex}
    (cook : CookDeformedSquareInput)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (t : Real)
    (C : PacketTerminalConcreteConclusion cook mu W Kz (sigma * z) X t)
    (hsigma : sigma ≠ 0)
    (Q : Matrix (PacketOuter (Fin W)) (PacketOuter (Fin W)) Complex) :
    TerminalSmallBallConclusion mu
      (TerminalConcreteScaling.physicalPacketTerminalCoefficientNorm
        sigma Q z)
      (TerminalConcreteScaling.physicalPacketTerminalValue sigma Q z X)
      (terminalUniformBaseLoss cook Kz (sigma * z) X t)
      (terminalUniformBadProbability cook W Kz t) :=
  TerminalConcreteScaling.physicalTerminalConclusion_of_rowScaled
    sigma hsigma Q z X (C (sigma • Q)).conclusion

end TerminalAssembly

end BernoulliSection9
