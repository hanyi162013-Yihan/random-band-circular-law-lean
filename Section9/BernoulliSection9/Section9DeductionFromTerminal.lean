import BernoulliSection9.TerminalConcreteConclusion
import BernoulliSection9.BoundarySmallBall
import BernoulliSection9.EndpointInterfaceData
import BernoulliSection9.ArbitraryFrameQuantitative

/-!
# Internal Section 9 bridge from the concrete terminal theorem

This module turns the certificate-free, outer-matrix-uniform terminal result
into the arbitrary-frame conclusion.  The coordinate boundary theorem is
constructed internally, and all endpoint inverse and exterior estimates are
deduced from `PaperEndpointGood`; no elimination, RRQR, compound-matrix, or
Hodge certificate is accepted from the caller.
-/

noncomputable section

namespace BernoulliSection9

open MeasureTheory BernoulliLinearAlgebra

/-- Deduce the literal arbitrary-frame small-ball conclusion from the uniform
concrete packet theorem.  This is an internal bridge: `Section9Results`
supplies and hides `C` in its caller-facing theorem.

The Hodge--Jacobi determinant-loss parameter is fixed to `delta⁻¹ ^ 2`.
Invertibility, operator control, nonnegativity, and the determinant inverse
bound are all consequences of `PaperEndpointGood`.
-/
theorem literalArbitraryFrameSmallBall_of_packetConcrete
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {W Kz r : Nat}
    (cook : CookDeformedSquareInput)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W)))
    (t : Real)
    (C : TerminalAssembly.PacketTerminalConcreteConclusion
      cook mu W Kz z X t)
    (CL BR : Matrix (Fin W) (Fin W) Complex)
    (B delta : Real)
    (endpoint : PaperEndpointGood CL BR B delta)
    (U V : ComplexFrame r (2 * W)) (h : r <= 2 * W) :
    ArbitraryFrameDeductionConclusion mu
      (literalArtificialCoefficientNorm z CL BR U V h)
      (literalFrameCoefficientNorm z CL BR U V h)
      (literalArtificialRandomValue z CL BR U V h X)
      (literalFrameRandomValue z CL BR U V h X)
      (literalBoundaryHodgeComparisonConstant W z B (delta⁻¹ ^ 2))⁻¹
      (literalBoundaryHodgeComparisonConstant W z B (delta⁻¹ ^ 2))
      (TerminalAssembly.terminalUniformBaseLoss cook Kz z X t)
      (TerminalAssembly.terminalUniformBadProbability cook W Kz t) := by
  let packetTerminal : BoundaryAssembly.LiteralPacketTerminalTheorem X z
      (TerminalAssembly.terminalUniformBaseLoss cook Kz z X t)
      (TerminalAssembly.terminalUniformBadProbability cook W Kz t) :=
    fun Q => (C Q).conclusion
  let coordinateTerminal :=
    BoundaryAssembly.literalCoordinateTerminalTheorem_of_packet
      X z CL BR endpoint.CL_det_isUnit endpoint.BR_det_isUnit
      (TerminalAssembly.terminalUniformBaseLoss cook Kz z X t)
      (TerminalAssembly.terminalUniformBadProbability cook W Kz t)
      (TerminalAssembly.terminalUniformBaseLoss_nonneg cook Kz z X t)
      packetTerminal
  exact literalArbitraryFrame_smallBall_deduction_of_endpointGood
    z CL BR endpoint.CL_det_isUnit endpoint.BR_det_isUnit
    B (delta⁻¹ ^ 2) endpoint.endpointOperatorGood
    endpoint.deltaInvSq_nonneg endpoint.endpointFactor_det_inv_norm_le
    U V h X
    (TerminalAssembly.terminalUniformBaseLoss cook Kz z X t)
    (TerminalAssembly.terminalUniformBadProbability cook W Kz t)
    (TerminalAssembly.terminalUniformBaseLoss_nonneg cook Kz z X t)
    coordinateTerminal

end BernoulliSection9
