import BernoulliSection9.EndpointOperatorBounds
import BernoulliSection9.ArbitraryFrameConcrete
import BernoulliLinearAlgebra.ExteriorVolumeComparison
import Mathlib.Tactic

/-!
# Paper-quantitative arbitrary-frame deduction

This module replaces the exact (potentially very large) endpoint exterior
constant by a bound derived internally from the operator-norm and determinant
parts of the paper's endpoint good event.  In particular, callers do not
supply compound-matrix or Hodge--Jacobi certificates.
-/

open scoped BigOperators Matrix Matrix.Norms.Frobenius

noncomputable section

namespace BernoulliSection9

open Filter Matrix Set Set.powersetCard
open BernoulliLinearAlgebra

local instance endpointQuantitativeSumLinearOrder (W : Nat) :
    LinearOrder (Fin W ⊕ Fin W) :=
  LinearOrder.lift'
    (fun x : Fin W ⊕ Fin W => (toLex x : Fin W ⊕ₗ Fin W))
    toLex.injective

/-- Quantitative comparison constant obtained from the endpoint good event.
The first factor is the already proved three-block matching/shift constant;
the second is the Hodge--Jacobi conditioning constant with all forward
compound bounds generated internally. -/
def literalBoundaryHodgeComparisonConstant
    (W : Nat) (z : Complex) (B D : Real) : Real :=
  threeBlockConcreteComparisonConstant (W := Fin W) z *
    max 1 (max (endpointCompoundCrudeBound W B)
      (D * endpointCompoundCrudeBound W B))

theorem literalBoundaryHodgeComparisonConstant_pos
    (W : Nat) (z : Complex) (B D : Real) :
    0 < literalBoundaryHodgeComparisonConstant W z B D := by
  unfold literalBoundaryHodgeComparisonConstant
  have hterminal : 1 <=
      threeBlockConcreteComparisonConstant (W := Fin W) z := by
    unfold threeBlockConcreteComparisonConstant
    exact one_le_mul_of_one_le_of_one_le
      (threeBlockZeroComparisonConstant_one_le (w := Fin W))
      (threeBlockTranslationFactor_one_le (w := Fin W) z)
  have hhodge : 1 <= max 1
      (max (endpointCompoundCrudeBound W B)
        (D * endpointCompoundCrudeBound W B)) := le_max_left _ _
  exact mul_pos (zero_lt_one.trans_le hterminal)
    (zero_lt_one.trans_le hhodge)

/-- Every Frobenius compound of the endpoint factor is controlled by the
operator-norm part of the endpoint good event.  Degrees above `2W` vanish
and are handled internally. -/
theorem endpointFactor_compound_norm_le_endpointCompoundCrudeBound
    {W : Nat} (CL BR : Matrix (Fin W) (Fin W) Complex)
    (B : Real) (hgood : EndpointOperatorGood CL BR B) (q : Nat) :
    ‖compound q (endpointFactor CL BR)‖ <=
      endpointCompoundCrudeBound W B := by
  by_cases hq : q <= Fintype.card (Fin W ⊕ Fin W)
  · exact (compound_frobenius_le_gramVolume (endpointFactor CL BR) hq).trans
      (gramVolume_endpointFactor_le_of_endpointOperatorGood
        CL BR B hgood)
  · have hcard : Fintype.card (Fin W ⊕ Fin W) < q :=
      Nat.lt_of_not_ge hq
    have hzero : compound q (endpointFactor CL BR) = 0 := by
      ext s
      exact ((not_le_of_gt hcard) (by
        rw [← s.prop]
        exact Finset.card_le_univ s.val)).elim
    rw [hzero, norm_zero]
    unfold endpointCompoundCrudeBound
    positivity

/-- The scaled artificial coefficient bounds with the paper's endpoint
event as input.  The Hodge forward estimates are constructed by the
preceding theorem, rather than accepted as a certificate. -/
theorem literalArtificialCoefficientNorm_scaled_bounds_of_endpointGood
    {W r : Nat}
    (z : Complex) (CL BR : Matrix (Fin W) (Fin W) Complex)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (B D : Real) (hOp : EndpointOperatorGood CL BR B)
    (hD : 0 <= D)
    (hdet : ‖(endpointFactor CL BR).det‖⁻¹ <= D)
    (U V : ComplexFrame r (2 * W)) (h : r <= 2 * W) (q : Nat) :
    (literalBoundaryHodgeComparisonConstant W z B D)⁻¹ *
          normalizedGraphProduct W q <=
        literalArtificialCoefficientNorm z CL BR U V h q ∧
      literalArtificialCoefficientNorm z CL BR U V h q <=
        literalBoundaryHodgeComparisonConstant W z B D *
          normalizedGraphProduct W q := by
  let Theta := literalArtificialTheta U V h (naturalLambda q)
  let scale := ‖inverseNaturalLambda q ^ r‖
  have hLambda : naturalLambda q ≠ 0 :=
    inv_ne_zero (inverseNaturalLambda_ne_zero q)
  have hTheta : IsUnit Theta.det :=
    literalArtificialTheta_det_isUnit U V h (naturalLambda q) hLambda
  have hb := globalBoundaryCoefficientNorm_bounds_of_hodgeBounds_fullyInstantiated
    z CL BR D (endpointCompoundCrudeBound W B) hCL hBR hD hdet
      (endpointFactor_compound_norm_le_endpointCompoundCrudeBound
        CL BR B hOp) Theta hTheta
  have hscale : 0 <= scale := norm_nonneg _
  have hvolume : scale * gramVolume Theta = normalizedGraphProduct W q :=
    normalized_literalArtificialTheta_gramVolume U V h q
  have hnorm : literalArtificialCoefficientNorm z CL BR U V h q =
      scale * globalBoundaryCoefficientNorm z CL BR Theta :=
    literalArtificialCoefficientNorm_eq_scaled_global z CL BR U V h q
  constructor
  · calc
      (literalBoundaryHodgeComparisonConstant W z B D)⁻¹ *
          normalizedGraphProduct W q =
          scale * ((literalBoundaryHodgeComparisonConstant W z B D)⁻¹ *
            gramVolume Theta) := by rw [← hvolume]; ring
      _ <= scale * globalBoundaryCoefficientNorm z CL BR Theta :=
        mul_le_mul_of_nonneg_left (by
          simpa [literalBoundaryHodgeComparisonConstant] using hb.1) hscale
      _ = literalArtificialCoefficientNorm z CL BR U V h q := hnorm.symm
  · calc
      literalArtificialCoefficientNorm z CL BR U V h q =
          scale * globalBoundaryCoefficientNorm z CL BR Theta := hnorm
      _ <= scale * (literalBoundaryHodgeComparisonConstant W z B D *
          gramVolume Theta) := mul_le_mul_of_nonneg_left (by
            simpa [literalBoundaryHodgeComparisonConstant] using hb.2) hscale
      _ = literalBoundaryHodgeComparisonConstant W z B D *
          normalizedGraphProduct W q := by rw [← hvolume]; ring

/-- Concrete arbitrary-frame deduction on the endpoint good event.  The
only probabilistic premise is the uniform coordinate terminal theorem;
Section9Results constructs that theorem from Cook internally. -/
theorem literalArbitraryFrame_smallBall_deduction_of_endpointGood
    {Omega : Type*} [MeasurableSpace Omega] {mu : MeasureTheory.Measure Omega}
    {W r : Nat} [MeasureTheory.IsProbabilityMeasure mu]
    (z : Complex) (CL BR : Matrix (Fin W) (Fin W) Complex)
    (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (B D : Real) (hOp : EndpointOperatorGood CL BR B)
    (hD : 0 <= D)
    (hdet : ‖(endpointFactor CL BR).det‖⁻¹ <= D)
    (U V : ComplexFrame r (2 * W)) (h : r <= 2 * W)
    (X : IidSubgaussianFamily Omega mu
      (ThreeBlockVariable (Fin W)))
    (baseLoss badProbability : Real) (hbase : 0 <= baseLoss)
    (coordinateTerminal : LiteralCoordinateTerminalTheorem
      mu X z CL BR baseLoss badProbability) :
    ArbitraryFrameDeductionConclusion mu
      (literalArtificialCoefficientNorm z CL BR U V h)
      (literalFrameCoefficientNorm z CL BR U V h)
      (literalArtificialRandomValue z CL BR U V h X)
      (literalFrameRandomValue z CL BR U V h X)
      (literalBoundaryHodgeComparisonConstant W z B D)⁻¹
      (literalBoundaryHodgeComparisonConstant W z B D)
      baseLoss badProbability := by
  apply literalArbitraryFrame_smallBall_deduction_of_scaled_bounds
    z CL BR U V h X
    (literalBoundaryHodgeComparisonConstant W z B D)⁻¹
    (literalBoundaryHodgeComparisonConstant W z B D)
    baseLoss badProbability
  · exact inv_pos.mpr
      (literalBoundaryHodgeComparisonConstant_pos W z B D)
  · exact hbase
  · intro q
    exact (literalArtificialCoefficientNorm_scaled_bounds_of_endpointGood
      z CL BR hCL hBR B D hOp hD hdet U V h q).1
  · intro q
    exact (literalArtificialCoefficientNorm_scaled_bounds_of_endpointGood
      z CL BR hCL hBR B D hOp hD hdet U V h q).2
  · exact coordinateTerminal

end BernoulliSection9
