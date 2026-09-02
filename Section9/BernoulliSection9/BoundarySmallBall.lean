import BernoulliSection9.ArbitraryFrameConcrete
import BernoulliLinearAlgebra.ChartPerturbation

/-!
# From the coordinate terminal theorem to every boundary relation

This file performs the dense-chart passage used immediately before the
artificial-frame limit.  The input is one theorem uniform in the terminal
outer matrix `Q`.  Upper-left perturbations are constructed internally, and
the resulting theorem is uniform over every invertible boundary relation.
-/

open scoped Matrix

noncomputable section

namespace BernoulliSection9

open Filter MeasureTheory
open BernoulliLinearAlgebra

namespace BoundaryAssembly

/-- The certificate-free probabilistic theorem supplied by the completed
three-block terminal argument.  This package is an internal bridge, not
an additional literature input. -/
def LiteralPacketTerminalTheorem
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {W : Nat}
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W)))
    (z : Complex) (baseLoss badProbability : Real) :=
  ∀ Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex,
    TerminalSmallBallConclusion mu
      (TerminalAssembly.packetTerminalCoefficientNorm Q z)
      (TerminalAssembly.packetTerminalValue Q z X)
      baseLoss badProbability

/-- Evaluation of the literal global boundary determinant is evaluation of
its complete squarefree coefficient vector. -/
theorem eval_globalBoundaryDetPolynomial_eq_evalSquarefree
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {W : Nat}
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W)))
    (z : Complex) (CL BR : Matrix (Fin W) (Fin W) Complex)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (omega : Omega) :
    MvPolynomial.eval (fun i ↦ (X.atom i omega : Complex))
        (globalBoundaryDetPolynomial z CL BR Theta) =
      evalSquarefree
        (fun S ↦ globalBoundaryCoeffVector z CL BR Theta S)
        X.atom omega := by
  rw [globalBoundaryDetPolynomial_eq_squarefreePolynomial]
  simpa [evalSquarefree, squarefreeMonomial] using
    (eval_squarefreePolynomial_eq_evalSquarefree
      (globalBoundaryCoeffVector z CL BR Theta)
      (fun i ↦ X.atom i omega))

/-- On the upper-left-invertible chart, the displayed boundary determinant
is the terminal determinant multiplied by the common scalar
`det Theta₁₁`. -/
theorem eval_globalBoundaryDetPolynomial_eq_det_mul_packetTerminalValue
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {W : Nat}
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W)))
    (z : Complex) (CL BR : Matrix (Fin W) (Fin W) Complex)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (h11 : IsUnit Theta.toBlocks₁₁.det) (omega : Omega) :
    MvPolynomial.eval (fun i ↦ (X.atom i omega : Complex))
        (globalBoundaryDetPolynomial z CL BR Theta) =
      Theta.toBlocks₁₁.det *
        TerminalAssembly.packetTerminalValue
          (endpointFactor CL BR *
            boundaryGraphS Theta.toBlocks₁₁ Theta.toBlocks₁₂
              Theta.toBlocks₂₁ Theta.toBlocks₂₂)
          z X omega := by
  rw [show globalBoundaryDetPolynomial z CL BR Theta =
      MvPolynomial.C Theta.toBlocks₁₁.det *
        threeBlockDetPolynomial
          (threeBlockOuterOfPacket
            (endpointFactor CL BR *
              transferCoordinateMap Theta.toBlocks₁₁ Theta.toBlocks₁₂
                Theta.toBlocks₂₁ Theta.toBlocks₂₂)) z by
    simpa [globalBoundaryDetPolynomial, globalConcreteKPolynomial] using
      (threeBlockConcreteKPolynomialShifted_det_eq z CL BR
        Theta.toBlocks₁₁ Theta.toBlocks₁₂
        Theta.toBlocks₂₁ Theta.toBlocks₂₂ h11)]
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_threeBlockDetPolynomial]
  simp only [TerminalAssembly.packetTerminalValue]
  rw [boundaryGraphS_eq_transferCoordinateMap]

/-- The packet theorem gives the complete boundary conclusion at every
point of the upper-left-invertible chart. -/
noncomputable def chartBoundaryTerminalConclusion
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {W : Nat}
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W)))
    (z : Complex) (CL BR : Matrix (Fin W) (Fin W) Complex)
    (baseLoss badProbability : Real)
    (packetTerminal : LiteralPacketTerminalTheorem X z
      baseLoss badProbability)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex)
    (h11 : IsUnit Theta.toBlocks₁₁.det) :
    TerminalSmallBallConclusion mu
      (globalBoundaryCoefficientNorm z CL BR Theta)
      (fun omega ↦ MvPolynomial.eval
        (fun i ↦ (X.atom i omega : Complex))
        (globalBoundaryDetPolynomial z CL BR Theta))
      baseLoss badProbability := by
  let Q : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) Complex :=
    endpointFactor CL BR *
      boundaryGraphS Theta.toBlocks₁₁ Theta.toBlocks₁₂
        Theta.toBlocks₂₁ Theta.toBlocks₂₂
  have hdet : Theta.toBlocks₁₁.det ≠ 0 :=
    isUnit_iff_ne_zero.mp h11
  have C := (packetTerminal Q).commonScale Theta.toBlocks₁₁.det hdet
  have hcoeff : globalBoundaryCoefficientNorm z CL BR Theta =
      ‖Theta.toBlocks₁₁.det‖ *
        TerminalAssembly.packetTerminalCoefficientNorm Q z := by
    simpa [Q, TerminalAssembly.packetTerminalCoefficientNorm] using
      (globalBoundaryCoefficientNorm_eq_on_chart z CL BR Theta h11)
  have hvalue :
      (fun omega ↦ MvPolynomial.eval
        (fun i ↦ (X.atom i omega : Complex))
        (globalBoundaryDetPolynomial z CL BR Theta)) =
      (fun omega ↦ Theta.toBlocks₁₁.det *
        TerminalAssembly.packetTerminalValue Q z X omega) := by
    funext omega
    simpa [Q] using
      (eval_globalBoundaryDetPolynomial_eq_det_mul_packetTerminalValue
        X z CL BR Theta h11 omega)
  simpa [hcoeff, hvalue] using C

/-- The chart theorem extends to every invertible boundary relation by the
explicit upper-left perturbation sequence.  The reverse-event field is not
used in this boundary passage, so the limiting conclusion uses the empty
event; the capped estimate, zero estimate, and Parseval identity remain
exact. -/
noncomputable def literalCoordinateTerminalTheorem_of_packet
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu] {W : Nat}
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W)))
    (z : Complex) (CL BR : Matrix (Fin W) (Fin W) Complex)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (baseLoss badProbability : Real) (hbase : 0 ≤ baseLoss)
    (packetTerminal : LiteralPacketTerminalTheorem X z
      baseLoss badProbability) :
    LiteralCoordinateTerminalTheorem mu X z CL BR
      baseLoss badProbability := by
  intro Theta hTheta
  let hdense :=
    invertibleUpperLeftChart_sequentiallyDenseAt Theta hTheta
  let ThetaSeq := Classical.choose hdense
  have hThetaSeqData := Classical.choose_spec hdense
  have hThetaSeqChart := hThetaSeqData.1
  have hThetaSeq := hThetaSeqData.2
  let coefficient : Nat → Real :=
    fun q ↦ globalBoundaryCoefficientNorm z CL BR (ThetaSeq q)
  let coefficientLimit : Real :=
    globalBoundaryCoefficientNorm z CL BR Theta
  let value : Nat → Omega → Complex := fun q omega ↦
    MvPolynomial.eval (fun i ↦ (X.atom i omega : Complex))
      (globalBoundaryDetPolynomial z CL BR (ThetaSeq q))
  let valueLimit : Omega → Complex := fun omega ↦
    MvPolynomial.eval (fun i ↦ (X.atom i omega : Complex))
      (globalBoundaryDetPolynomial z CL BR Theta)
  have Cseq : ∀ q, TerminalSmallBallConclusion mu
      (coefficient q) (value q) baseLoss badProbability := by
    intro q
    exact chartBoundaryTerminalConclusion X z CL BR baseLoss badProbability
      packetTerminal (ThetaSeq q) (hThetaSeqChart q).2
  have hcoefficient : Tendsto coefficient atTop (nhds coefficientLimit) := by
    exact (continuous_globalBoundaryCoefficientNorm z CL BR).continuousAt.tendsto.comp
      hThetaSeq
  have hcoefficientPos : 0 < coefficientLimit := by
    exact globalBoundaryCoefficientNorm_pos_fullyInstantiated z CL BR
      hCL hBR Theta hTheta
  have hcoefficientSeqPos : ∀ q, 0 < coefficient q :=
    fun q ↦ (Cseq q).coefficientNorm_pos
  have hvalue : ∀ omega,
      Tendsto (fun q ↦ value q omega) atTop (nhds (valueLimit omega)) := by
    intro omega
    have hcoeff : ∀ S : Finset (ThreeBlockVariable (Fin W)),
        Tendsto
          (fun q ↦ globalBoundaryCoeffVector z CL BR (ThetaSeq q) S)
          atTop (nhds (globalBoundaryCoeffVector z CL BR Theta S)) := by
      intro S
      exact ((coeffwiseContinuous_globalBoundaryDetPolynomial z CL BR)
        (squarefreeExponent S)).continuousAt.tendsto.comp hThetaSeq
    have hsum : Tendsto
        (fun q ↦ evalSquarefree
          (fun S ↦ globalBoundaryCoeffVector z CL BR (ThetaSeq q) S)
          X.atom omega)
        atTop
        (nhds (evalSquarefree
          (fun S ↦ globalBoundaryCoeffVector z CL BR Theta S)
          X.atom omega)) := by
      unfold evalSquarefree
      apply tendsto_finsetSum Finset.univ
      intro S _
      exact (hcoeff S).mul tendsto_const_nhds
    simpa [value, valueLimit,
      eval_globalBoundaryDetPolynomial_eq_evalSquarefree] using hsum
  have hvalueMeas : ∀ q, AEStronglyMeasurable (value q) mu := by
    intro q
    have hm : Measurable (fun omega ↦ evalSquarefree
        (fun S ↦ globalBoundaryCoeffVector z CL BR (ThetaSeq q) S)
        X.atom omega) :=
      TerminalAssembly.measurable_evalSquarefree _ _ X.measurable_atom
    apply Measurable.aestronglyMeasurable
    simpa [value, eval_globalBoundaryDetPolynomial_eq_evalSquarefree] using hm
  have hcapped : ∀ T : Real, 0 < T →
      ∫ omega, cappedLogLoss T coefficientLimit (valueLimit omega) ∂mu ≤
        baseLoss + badProbability * T := by
    intro T hT
    exact cappedIntegral_limit_le_of_uniform_bound mu T hT.le
      hcoefficient hcoefficientPos hcoefficientSeqPos hvalueMeas
      (Filter.Eventually.of_forall hvalue)
      (baseLoss + badProbability * T) (fun q ↦ (Cseq q).capped T hT)
  have hvalueLimitMeas : Measurable valueLimit := by
    have hm : Measurable (fun omega ↦ evalSquarefree
        (fun S ↦ globalBoundaryCoeffVector z CL BR Theta S)
        X.atom omega) :=
      TerminalAssembly.measurable_evalSquarefree _ _ X.measurable_atom
    simpa [valueLimit,
      eval_globalBoundaryDetPolynomial_eq_evalSquarefree] using hm
  have hzero : mu.real {omega | valueLimit omega = 0} ≤ badProbability := by
    apply zeroProbability_of_all_capped_bounds hbase
    intro T hT
    exact (cap_mul_zeroProbability_le_integral mu T coefficientLimit hT.le
      hcoefficientPos valueLimit hvalueLimitMeas).trans (hcapped T hT)
  have hparseval : coefficientLimit ^ 2 =
      ∫ omega, ‖valueLimit omega‖ ^ 2 ∂mu := by
    have hp := integral_norm_evalSquarefree_sq_eq_coeffNorm X
      (globalBoundaryCoeffVector z CL BR Theta)
    rw [show coefficientLimit =
        ‖globalBoundaryCoeffVector z CL BR Theta‖ by rfl]
    symm
    simpa [valueLimit,
      eval_globalBoundaryDetPolynomial_eq_evalSquarefree] using hp
  exact
    { coefficientNorm_pos := hcoefficientPos
      capped := hcapped
      zero_probability := hzero
      reverse_event := ∅
      reverse := by simp
      parseval := hparseval }

end BoundaryAssembly

end BernoulliSection9
