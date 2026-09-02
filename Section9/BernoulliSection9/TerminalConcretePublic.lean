import BernoulliSection9.TerminalConcreteGoodEvent

/-!
# Public concrete terminal theorem

This module closes the last internal good-event interface.  The RRQR output,
the CUR elimination, both square embeddings, both conditioning sigma-fields,
and both truncated deformations are constructed by
`packetTerminalConcreteGoodEventControl`; none is accepted from the caller.
-/

noncomputable section

namespace BernoulliSection9

open MeasureTheory BernoulliLinearAlgebra

namespace TerminalAssembly

universe u

/-- The certificate-free, outer-matrix-uniform terminal small-ball theorem in
the row-scaled normalization.  Cook's estimate is the only external analytic
input. -/
noncomputable def packetTerminalConcreteConclusion
    {Omega : Type u} [MeasurableSpace Omega]
    (cook : CookDeformedSquareInput.{u, u})
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W : Nat} (Kz : Nat) (z : Complex)
    (X : IidSubgaussianFamily Omega mu (ThreeBlockVariable (Fin W)))
    (t : Real)
    (hnum : PacketTerminalCanonicalLargeWConditions cook z X Kz t) :
    PacketTerminalConcreteConclusion cook mu W Kz z X t := by
  intro Q
  have hWpos : 0 < W := by
    have hWlarge := hnum.W_large
    omega
  letI : Nonempty (Fin W) := Fin.pos_iff_nonempty.mp hWpos
  simpa [terminalUniformBaseLoss, terminalConcreteExposureThreshold] using
    packetTerminalSmallBallResult_of_goodEventControl
      mu Q z X
      (terminalUniformValueLoss cook W Kz)
      (terminalUniformBadProbability cook W Kz t) t
      (terminalUniformValueLoss_nonneg cook W Kz) hnum.t_nonneg
      (packetTerminalConcreteGoodEventControl cook mu Kz z X t hnum Q)

end TerminalAssembly

end BernoulliSection9
