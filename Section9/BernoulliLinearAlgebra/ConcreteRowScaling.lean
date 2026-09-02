import BernoulliLinearAlgebra.ConcreteBoundaryGlobal
import BernoulliLinearAlgebra.TransferCoordinate

/-!
# Concrete temporary row scaling

This file instantiates Corollary 9.4 for the literal five-block polynomial
matrix used by the boundary argument.  Only the three packet rows are
scaled, so the determinant and its complete squarefree coefficient vector
acquire the factor `σ ^ (3 * card W)` rather than a factor from all five
blocks.
-/

open scoped Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix MvPolynomial

variable {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]

omit [DecidableEq W] [LinearOrder W] in
/-- The three packet blocks contain exactly `3 * card W` rows. -/
@[simp] theorem card_packet3 :
    Fintype.card (Packet3 W) = 3 * Fintype.card W := by
  simp [Packet3]
  omega

/-- The literal five-block polynomial matrix after multiplying precisely
the three physical packet rows by `σ`. -/
def scaledGlobalConcreteKPolynomial
    (σ z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :=
  scaleLeadingRows (C σ) (globalConcreteKPolynomial z CL BR Theta)

omit [LinearOrder W] in
/-- Concrete determinant form of temporary row scaling. -/
theorem scaledGlobalConcreteKPolynomial_det
    (σ z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    (scaledGlobalConcreteKPolynomial σ z CL BR Theta).det =
      C (σ ^ (3 * Fintype.card W)) *
        globalBoundaryDetPolynomial z CL BR Theta := by
  rw [scaledGlobalConcreteKPolynomial, scaleLeadingRows_det, card_packet3]
  simp [globalBoundaryDetPolynomial]

/-- Complete squarefree coefficient vector of the row-scaled determinant. -/
def scaledGlobalBoundaryCoeffVector
    (σ z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    CoeffSpace (ThreeBlockVariable W) :=
  WithLp.toLp 2 (fun S =>
    coeff (squarefreeExponent S)
      (scaledGlobalConcreteKPolynomial σ z CL BR Theta).det)

omit [LinearOrder W] in
/-- Coefficient-by-coefficient form of Corollary 9.4. -/
theorem scaledGlobalBoundaryCoeffVector_eq_smul
    (σ z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    scaledGlobalBoundaryCoeffVector σ z CL BR Theta =
      σ ^ (3 * Fintype.card W) •
        globalBoundaryCoeffVector z CL BR Theta := by
  ext S
  change coeff (squarefreeExponent S)
      (scaledGlobalConcreteKPolynomial σ z CL BR Theta).det =
    σ ^ (3 * Fintype.card W) *
      coeff (squarefreeExponent S)
        (globalBoundaryDetPolynomial z CL BR Theta)
  rw [scaledGlobalConcreteKPolynomial_det]
  rw [MvPolynomial.coeff_C_mul]

omit [LinearOrder W] in
/-- Euclidean norm of the complete coefficient vector after row scaling. -/
theorem norm_scaledGlobalBoundaryCoeffVector
    (σ z : ℂ) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    ‖scaledGlobalBoundaryCoeffVector σ z CL BR Theta‖ =
      ‖σ ^ (3 * Fintype.card W)‖ *
        globalBoundaryCoefficientNorm z CL BR Theta := by
  rw [scaledGlobalBoundaryCoeffVector_eq_smul, norm_smul]
  rfl

omit [LinearOrder W] in
/-- Inverse determinant normalization, in the exact direction displayed in
Corollary 9.4. -/
theorem globalBoundaryDetPolynomial_eq_inv_mul_scaled
    (σ z : ℂ) (hσ : σ ≠ 0) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    globalBoundaryDetPolynomial z CL BR Theta =
      C ((σ⁻¹) ^ (3 * Fintype.card W)) *
        (scaledGlobalConcreteKPolynomial σ z CL BR Theta).det := by
  rw [scaledGlobalConcreteKPolynomial_det]
  rw [← mul_assoc, ← map_mul]
  simp [hσ]

omit [LinearOrder W] in
/-- Inverse coefficient-norm normalization. -/
theorem globalBoundaryCoefficientNorm_eq_inv_mul_scaled
    (σ z : ℂ) (hσ : σ ≠ 0) (CL BR : Matrix W W ℂ)
    (Theta : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    globalBoundaryCoefficientNorm z CL BR Theta =
      ‖σ ^ (3 * Fintype.card W)‖⁻¹ *
        ‖scaledGlobalBoundaryCoeffVector σ z CL BR Theta‖ := by
  rw [norm_scaledGlobalBoundaryCoeffVector, ← mul_assoc,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (pow_ne_zero _ hσ)), one_mul]

end BernoulliLinearAlgebra
