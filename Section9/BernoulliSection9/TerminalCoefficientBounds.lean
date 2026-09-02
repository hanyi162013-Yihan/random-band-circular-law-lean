import BernoulliSection9.MatrixGramVolumeSingular
import BernoulliLinearAlgebra.ConcreteBoundaryFinal

/-!
# Literal terminal coefficient bounds from the RRQR cutoff

The read-only dependency proves that the actual three-block squarefree
coefficient norm is comparable with `gramVolume Q`.  The local graph-volume
identity now converts that comparison to the exact product of singular
values above the RRQR threshold.  No mask or coefficient certificate is an
argument of these theorems.
-/

open scoped Matrix

noncomputable section

namespace BernoulliSection9

open Module

variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

local instance terminalCoefficientOuterOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift'
    (fun x : W ⊕ W => (toLex x : W ⊕ₗ W)) toLex.injective

/-- Equations (9.41)--(9.42), with their exact finite factors still visible.
The subsequent numerical estimate bounds both the concrete comparison
constant and `(2*tau)^(2W)` by `exp (C W log W)`. -/
theorem threeBlockTerminalCoefficient_product_bounds
    (z : Complex) (Q : Matrix (W ⊕ W) (W ⊕ W) Complex)
    (r : Nat) (tau : Real) (htau : 1 <= tau)
    (hlarge : ∀ i : Fin
        (finrank Complex (EuclideanSpace Complex (W ⊕ W))),
      (i : Nat) < r -> tau < (Matrix.toEuclideanLin Q).singularValues i)
    (hsmall : ∀ i : Fin
        (finrank Complex (EuclideanSpace Complex (W ⊕ W))),
      r <= (i : Nat) -> (Matrix.toEuclideanLin Q).singularValues i <= tau) :
    let K := BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
      (W := W) z
    let productScale := largeSingularProduct (Matrix.toEuclideanLin Q) r
    K⁻¹ * productScale <=
        BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket
          (w := W) z Q ∧
      BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket
          (w := W) z Q <=
        K * ((2 * tau) ^ (Fintype.card (W ⊕ W)) * productScale) := by
  dsimp only
  let K := BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
    (W := W) z
  let productScale := largeSingularProduct (Matrix.toEuclideanLin Q) r
  have hcomparison :=
    BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket_concreteComparison
      (W := W) z
  have hK : 0 <= K := zero_le_one.trans hcomparison.one_le
  have hvolumeLower : productScale <= BernoulliLinearAlgebra.gramVolume Q := by
    exact matrix_largeSingularProduct_le_gramVolume Q r
  have hvolumeUpper : BernoulliLinearAlgebra.gramVolume Q <=
      (2 * tau) ^ (Fintype.card (W ⊕ W)) * productScale := by
    exact gramVolume_le_threshold_factor_mul_matrixLargeSingularProduct
      Q r tau htau hlarge hsmall
  constructor
  · calc
      K⁻¹ * productScale <= K⁻¹ * BernoulliLinearAlgebra.gramVolume Q :=
        mul_le_mul_of_nonneg_left hvolumeLower (inv_nonneg.mpr hK)
      _ <= BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket
          (w := W) z Q := hcomparison.lower Q
  · calc
      BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket
          (w := W) z Q <= K * BernoulliLinearAlgebra.gramVolume Q :=
        hcomparison.upper Q
      _ <= K * ((2 * tau) ^ (Fintype.card (W ⊕ W)) * productScale) :=
        mul_le_mul_of_nonneg_left hvolumeUpper hK

/-- The literal terminal coefficient norm is strictly positive at a genuine
RRQR threshold.  This also covers `r = 0`, when the product is empty and
equals one. -/
theorem threeBlockTerminalCoefficient_pos_of_threshold
    (z : Complex) (Q : Matrix (W ⊕ W) (W ⊕ W) Complex)
    (r : Nat) (tau : Real) (htau : 1 <= tau)
    (hlarge : ∀ i : Fin
        (finrank Complex (EuclideanSpace Complex (W ⊕ W))),
      (i : Nat) < r -> tau < (Matrix.toEuclideanLin Q).singularValues i) :
    0 < BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket
      (w := W) z Q := by
  let K := BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
    (W := W) z
  let productScale := largeSingularProduct (Matrix.toEuclideanLin Q) r
  have hcomparison :=
    BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket_concreteComparison
      (W := W) z
  have hK : 0 < K := zero_lt_one.trans_le hcomparison.one_le
  have hproduct : 0 < productScale :=
    largeSingularProduct_pos _ r tau (zero_le_one.trans htau) hlarge
  have hlower := hcomparison.lower Q
  have hpositive : 0 < K⁻¹ * BernoulliLinearAlgebra.gramVolume Q := by
    apply mul_pos (inv_pos.mpr hK)
    exact hproduct.trans_le (matrix_largeSingularProduct_le_gramVolume Q r)
  exact hpositive.trans_le hlower

/-- Convert a value lower bound relative to the RRQR product into one
relative to Gram volume.  The exact additional loss is the logarithm of
the threshold factor `(2*tau)^(2W)`. -/
theorem exp_neg_add_log_thresholdFactor_mul_gramVolume_le
    (Q : Matrix (W ⊕ W) (W ⊕ W) Complex)
    (r : Nat) (tau valueLoss : Real) (htau : 1 <= tau)
    (hlarge : ∀ i : Fin
        (finrank Complex (EuclideanSpace Complex (W ⊕ W))),
      (i : Nat) < r -> tau < (Matrix.toEuclideanLin Q).singularValues i)
    (hsmall : ∀ i : Fin
        (finrank Complex (EuclideanSpace Complex (W ⊕ W))),
      r <= (i : Nat) -> (Matrix.toEuclideanLin Q).singularValues i <= tau) :
    let factor := (2 * tau) ^ (Fintype.card (W ⊕ W))
    Real.exp (-(valueLoss + Real.log factor)) *
        BernoulliLinearAlgebra.gramVolume Q <=
      Real.exp (-valueLoss) *
        largeSingularProduct (Matrix.toEuclideanLin Q) r := by
  dsimp only
  let factor : Real := (2 * tau) ^ (Fintype.card (W ⊕ W))
  have hbase : 0 < 2 * tau := by positivity
  have hfactor : 0 < factor := pow_pos hbase _
  have hvolume :=
    gramVolume_le_threshold_factor_mul_matrixLargeSingularProduct
      Q r tau htau hlarge hsmall
  have hexp : Real.exp (-(valueLoss + Real.log factor)) * factor =
      Real.exp (-valueLoss) := by
    have hcancel : Real.exp (-Real.log factor) * factor = 1 := by
      rw [Real.exp_neg, Real.exp_log hfactor]
      exact inv_mul_cancel₀ hfactor.ne'
    rw [neg_add, Real.exp_add, mul_assoc, hcancel, mul_one]
  calc
    Real.exp (-(valueLoss + Real.log factor)) *
        BernoulliLinearAlgebra.gramVolume Q <=
      Real.exp (-(valueLoss + Real.log factor)) *
        (factor * largeSingularProduct (Matrix.toEuclideanLin Q) r) :=
      mul_le_mul_of_nonneg_left hvolume (Real.exp_nonneg _)
    _ = Real.exp (-valueLoss) *
        largeSingularProduct (Matrix.toEuclideanLin Q) r := by
      rw [← mul_assoc, hexp]

end BernoulliSection9
