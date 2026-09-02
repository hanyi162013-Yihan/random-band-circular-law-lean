import BernoulliLinearAlgebra.ThreeBlockTerminal
import BernoulliLinearAlgebra.PolynomialCoefficientContinuity

/-!
# The global concrete boundary coefficient

This file packages the determinant of the displayed five-block matrix
`K_Theta` as an actual polynomial for an arbitrary boundary relation
`Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ`.  Its coefficient norm is the quantity
continued from the upper-left-invertible chart in Section 9.5.
-/

open scoped Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix MvPolynomial

variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

local instance concreteGlobalSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W => (toLex x : W ⊕ₗ W)) toLex.injective

/-- The literal polynomial-valued `K_Theta`, with the four blocks extracted
from the full boundary relation. -/
def globalConcreteKPolynomial
    (z : ℂ)
    (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :=
  threeBlockConcreteKPolynomialShifted z CL BR
    Theta.toBlocks₁₁ Theta.toBlocks₁₂ Theta.toBlocks₂₁ Theta.toBlocks₂₂

/-- The globally defined boundary determinant polynomial `D_Theta`. -/
def globalBoundaryDetPolynomial
    (z : ℂ)
    (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    MvPolynomial (ThreeBlockVariable W) ℂ :=
  (globalConcreteKPolynomial z CL BR Theta).det

/-- Its complete squarefree coefficient vector. -/
def globalBoundaryCoeffVector
    (z : ℂ)
    (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    CoeffSpace (ThreeBlockVariable W) :=
  WithLp.toLp 2 (fun S =>
    coeff (squarefreeExponent S)
      (globalBoundaryDetPolynomial z CL BR Theta))

/-- The coefficient norm `mathscr C(Theta)` used in Section 9.5. -/
def globalBoundaryCoefficientNorm
    (z : ℂ)
    (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) : ℝ :=
  ‖globalBoundaryCoeffVector z CL BR Theta‖

omit [LinearOrder W] in
@[simp] theorem globalBoundaryCoeffVector_apply
    (z : ℂ)
    (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (S : Finset (ThreeBlockVariable W)) :
    globalBoundaryCoeffVector z CL BR Theta S =
      coeff (squarefreeExponent S)
        (globalBoundaryDetPolynomial z CL BR Theta) := rfl

omit [LinearOrder W] in
/-- On the upper-left-invertible chart, the globally defined coefficient
norm has the exact `|det Theta11|` scaling supplied by the concrete second
elimination.  This is the paper's `hScale`, now a theorem rather than an
application hypothesis. -/
theorem globalBoundaryCoefficientNorm_eq_on_chart
    (z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ)
    (h11 : IsUnit Theta.toBlocks₁₁.det) :
    globalBoundaryCoefficientNorm z CL BR Theta =
      ‖Theta.toBlocks₁₁.det‖ *
        threeBlockTerminalCoefficientOnPacket (w := W) z
          (endpointFactor CL BR *
            boundaryGraphS Theta.toBlocks₁₁ Theta.toBlocks₁₂
              Theta.toBlocks₂₁ Theta.toBlocks₂₂) := by
  simpa [globalBoundaryCoefficientNorm, globalBoundaryCoeffVector,
    globalBoundaryDetPolynomial, globalConcreteKPolynomial,
    threeBlockBoundaryKCoefficientNormShifted,
    threeBlockBoundaryKCoeffVectorShifted,
    threeBlockTerminalCoefficientOnPacket,
    boundaryGraphS_eq_transferCoordinateMap] using
      (threeBlockBoundaryKCoefficientNormShifted_eq z CL BR
        Theta.toBlocks₁₁ Theta.toBlocks₁₂ Theta.toBlocks₂₁
        Theta.toBlocks₂₂ h11)

section Continuity

omit [LinearOrder W] in
/-- Every entry of the concrete polynomial matrix `K_Theta` is
coefficientwise continuous in the entries of `Theta`. -/
theorem coeffwiseContinuous_globalConcreteKPolynomial_entry
    (z : ℂ)
    (CL BR : Matrix W W ℂ)
    (i j : Packet3 W ⊕ (W ⊕ W)) :
    CoeffwiseContinuous fun Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ =>
      globalConcreteKPolynomial z CL BR Theta i j := by
  rcases i with i | i
  · rcases j with j | j
    · exact CoeffwiseContinuous.const _
    · exact CoeffwiseContinuous.const _
  · rcases j with j | j
    · rcases j with j | j
      · rcases i with i | i
        · simpa [globalConcreteKPolynomial,
            threeBlockConcreteKPolynomialShifted, concreteKTheta,
            boundaryPhysicalCoupling, boundaryOuterCoupling,
            packetOuterProjection, threeBlockCMatrix, Matrix.mul_apply,
            Matrix.one_apply] using
            (CoeffwiseContinuous.const
              (X := Matrix (W ⊕ W) (W ⊕ W) ℂ)
              (v := ThreeBlockVariable W)
              (if i = j then 1 else 0))
        · simpa [globalConcreteKPolynomial,
            threeBlockConcreteKPolynomialShifted, concreteKTheta,
            boundaryPhysicalCoupling, boundaryOuterCoupling,
            packetOuterProjection, threeBlockCMatrix, Matrix.mul_apply,
            Matrix.one_apply] using
            (CoeffwiseContinuous.const
              (X := Matrix (W ⊕ W) (W ⊕ W) ℂ)
              (v := ThreeBlockVariable W) 0)
      · rcases j with j | j
        · simpa [globalConcreteKPolynomial,
            threeBlockConcreteKPolynomialShifted, concreteKTheta,
            boundaryPhysicalCoupling, boundaryOuterCoupling,
            packetOuterProjection, threeBlockCMatrix, Matrix.mul_apply,
            Matrix.one_apply] using
            (CoeffwiseContinuous.const
              (X := Matrix (W ⊕ W) (W ⊕ W) ℂ)
              (v := ThreeBlockVariable W) 0)
        · rcases i with i | i
          · have h : CoeffwiseContinuous (v := ThreeBlockVariable W)
                (fun Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ =>
                  C (Theta.toBlocks₁₂ i j)) :=
                CoeffwiseContinuous.C (by
                  change Continuous (fun Theta :
                    Matrix (W ⊕ W) (W ⊕ W) ℂ =>
                      Theta (Sum.inl i) (Sum.inr j))
                  fun_prop)
            simpa [globalConcreteKPolynomial,
              threeBlockConcreteKPolynomialShifted, concreteKTheta,
              boundaryPhysicalCoupling, boundaryOuterCoupling,
              packetOuterProjection, threeBlockCMatrix, Matrix.mul_apply,
              Matrix.one_apply] using h.neg
          · have h : CoeffwiseContinuous (v := ThreeBlockVariable W)
                (fun Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ =>
                  C (Theta.toBlocks₂₂ i j)) :=
                CoeffwiseContinuous.C (by
                  change Continuous (fun Theta :
                    Matrix (W ⊕ W) (W ⊕ W) ℂ =>
                      Theta (Sum.inr i) (Sum.inr j))
                  fun_prop)
            simpa [globalConcreteKPolynomial,
              threeBlockConcreteKPolynomialShifted, concreteKTheta,
              boundaryPhysicalCoupling, boundaryOuterCoupling,
              packetOuterProjection, threeBlockCMatrix, Matrix.mul_apply,
              Matrix.one_apply] using h.neg
    · rcases i with i | i <;> rcases j with j | j
      · exact CoeffwiseContinuous.const _
      · have h : CoeffwiseContinuous (v := ThreeBlockVariable W)
            (fun Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ =>
              C (Theta.toBlocks₁₁ i j)) :=
            CoeffwiseContinuous.C (by
              change Continuous (fun Theta :
                Matrix (W ⊕ W) (W ⊕ W) ℂ =>
                  Theta (Sum.inl i) (Sum.inl j))
              fun_prop)
        simpa [globalConcreteKPolynomial,
          threeBlockConcreteKPolynomialShifted,
          concreteKTheta, endpointPivot, threeBlockCMatrix] using h.neg
      · exact CoeffwiseContinuous.const _
      · have h : CoeffwiseContinuous (v := ThreeBlockVariable W)
            (fun Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ =>
              C (Theta.toBlocks₂₁ i j)) :=
            CoeffwiseContinuous.C (by
              change Continuous (fun Theta :
                Matrix (W ⊕ W) (W ⊕ W) ℂ =>
                  Theta (Sum.inr i) (Sum.inl j))
              fun_prop)
        simpa [globalConcreteKPolynomial,
          threeBlockConcreteKPolynomialShifted,
          concreteKTheta, endpointPivot, threeBlockCMatrix] using h.neg

omit [LinearOrder W] in
/-- The displayed boundary determinant is coefficientwise continuous in
the full boundary relation. -/
theorem coeffwiseContinuous_globalBoundaryDetPolynomial
    (z : ℂ)
    (CL BR : Matrix W W ℂ) :
    CoeffwiseContinuous fun Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ =>
      globalBoundaryDetPolynomial z CL BR Theta := by
  apply coeffwiseContinuous_det
  exact coeffwiseContinuous_globalConcreteKPolynomial_entry z CL BR

omit [LinearOrder W] in
/-- The actual complete coefficient norm is continuous in `Theta`. -/
theorem continuous_globalBoundaryCoefficientNorm
    (z : ℂ)
    (CL BR : Matrix W W ℂ) :
    Continuous (globalBoundaryCoefficientNorm z CL BR) := by
  exact (coeffwiseContinuous_globalBoundaryDetPolynomial z CL BR).continuous_selectedCoeffNorm
    squarefreeExponent _

omit [LinearOrder W] in
/-- The Gram volume of the full boundary relation is continuous. -/
theorem continuous_gramVolume_matrix :
    Continuous (gramVolume : Matrix (W ⊕ W) (W ⊕ W) ℂ → ℝ) := by
  unfold gramVolume gramEnergy
  fun_prop

end Continuity

end BernoulliLinearAlgebra
