import BernoulliSection9.InterfaceEndpointBridge
import BernoulliSection9.Section9DeductionFromTerminal

/-!
# Combined interface and arbitrary-frame bridge

This module combines the two-interface probability estimate with the
certificate-free deduction from the concrete terminal theorem.  Outside the
joint interface bad event, the normalized endpoint matrices and their scalar
bounds are obtained directly from `interfacePairProbabilityAndPaperEndpointGood`.
-/

noncomputable section

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory BernoulliLinearAlgebra

universe u

/-- Type-valued package containing both the pair-interface probability bound
and the arbitrary-frame conclusion at every point outside that bad event. -/
structure InterfacePairLiteralArbitraryFrameSmallBallConclusion
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W Kz r : Nat}
    (I : NguyenBottomSingularInput.{u, u})
    (SL SR : IidSubgaussianSquare Omega mu W)
    (cook : CookDeformedSquareInput)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W)))
    (t : Real)
    (U V : ComplexFrame r (2 * W)) (h : r <= 2 * W) : Type u where
  probability_bad :
    mu.real (interfacePairBadEvent I SL SR) <=
      2 * Real.exp (-(interfaceCombinedRate I / 2) * (W : Real))
  conclusion : ∀ omega ∉ interfacePairBadEvent I SL SR,
    ArbitraryFrameDeductionConclusion mu
      (literalArtificialCoefficientNorm z
        (normalizedInterfaceMatrix SL omega)
        (normalizedInterfaceMatrix SR omega) U V h)
      (literalFrameCoefficientNorm z
        (normalizedInterfaceMatrix SL omega)
        (normalizedInterfaceMatrix SR omega) U V h)
      (literalArtificialRandomValue z
        (normalizedInterfaceMatrix SL omega)
        (normalizedInterfaceMatrix SR omega) U V h X)
      (literalFrameRandomValue z
        (normalizedInterfaceMatrix SL omega)
        (normalizedInterfaceMatrix SR omega) U V h X)
      (literalBoundaryHodgeComparisonConstant W z
        (interfacePairOpNormBound SL SR)
        ((interfaceDeterminantLowerBound I W)⁻¹ ^ 2))⁻¹
      (literalBoundaryHodgeComparisonConstant W z
        (interfacePairOpNormBound SL SR)
        ((interfaceDeterminantLowerBound I W)⁻¹ ^ 2))
      (TerminalAssembly.terminalUniformBaseLoss cook Kz z X t)
      (TerminalAssembly.terminalUniformBadProbability cook W Kz t)

/-- The complete internal bridge from the pair of iid interface squares and
the uniform concrete terminal theorem to the literal arbitrary-frame
conclusion.  The two normalized endpoint matrices, their common operator
bound, and their determinant lower bound are fixed by the interface theorem;
no endpoint, exterior, elimination, or RRQR certificate is supplied by the
caller.
-/
noncomputable def
    interfacePairProbabilityAndLiteralArbitraryFrameSmallBall_of_packetConcrete
    {Omega : Type u} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W Kz r : Nat}
    (I : NguyenBottomSingularInput.{u, u})
    (SL SR : IidSubgaussianSquare Omega mu W)
    (hSL : SL.subgaussianParameter ≤ I.subgaussianBound)
    (hSR : SR.subgaussianParameter ≤ I.subgaussianBound)
    (hW : 0 < W)
    (hcutoffLarge :
      1 <= nguyenInterfaceCutoffRho I ^ 2 * (W : Real))
    (hlarge :
      32 <= interfaceCombinedRate I ^ 2 * (W : Real))
    (cook : CookDeformedSquareInput)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W)))
    (t : Real)
    (C : TerminalAssembly.PacketTerminalConcreteConclusion
      cook mu W Kz z X t)
    (U V : ComplexFrame r (2 * W)) (h : r <= 2 * W) :
    InterfacePairLiteralArbitraryFrameSmallBallConclusion
      (Kz := Kz) mu I SL SR cook z X t U V h := by
  have interface := interfacePairProbabilityAndPaperEndpointGood
    mu I SL SR hSL hSR hW hcutoffLarge hlarge
  refine
    { probability_bad := interface.1
      conclusion := ?_ }
  intro omega hgood
  exact literalArbitraryFrameSmallBall_of_packetConcrete cook z X t C
    (normalizedInterfaceMatrix SL omega)
    (normalizedInterfaceMatrix SR omega)
    (interfacePairOpNormBound SL SR)
    (interfaceDeterminantLowerBound I W) (interface.2 omega hgood) U V h

end BernoulliSection9
