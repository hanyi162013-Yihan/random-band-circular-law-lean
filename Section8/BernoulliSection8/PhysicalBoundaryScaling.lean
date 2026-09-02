import BernoulliSection10.PacketProbability
import BernoulliLinearAlgebra.ConcreteRowScaling
import Mathlib.Algebra.MvPolynomial.Monad

/-! # Exact raw-atom polynomial for the normalized physical boundary

The normalized polynomial is defined by substitution of `sigma⁻¹ X_e`
for every fresh entry of the actual five-block boundary determinant.
Scaling the three physical block rows identifies it with the variance-one
polynomial at `(sigma z, sigma CL, sigma BR)`, with a common determinant
factor `sigma⁻¹^(3W)`. Thus its coefficient norm and value acquire the
same factor, including at zero values.
-/

open scoped Matrix

noncomputable section

namespace BernoulliSection8

open Matrix MvPolynomial BernoulliSection10 BernoulliLinearAlgebra

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {w : Type*} [Fintype w] [DecidableEq w] [LinearOrder w]

theorem endpointFactor_smul (a : ℂ) (CL BR : Matrix w w ℂ) :
    endpointFactor (a • CL) (a • BR) = a • endpointFactor CL BR := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [endpointFactor]

theorem threeBlockDelta_scale_inverse
    (sigma : ℂ) (hsigma : sigma ≠ 0) (x : ThreeBlockVariable w → ℂ) :
    sigma • threeBlockDelta (fun e => sigma⁻¹ * x e) = threeBlockDelta x := by
  ext i j
  by_cases h : threeBlockFresh i j <;> simp [threeBlockDelta, h, hsigma]

/-- Only the physical rows are multiplied. The boundary equations stay
unchanged, so the exponent is `3W`, not the dimension `5W` of this matrix. -/
theorem scaleLeadingRows_packetLiteralK
    (sigma : ℂ) (hsigma : sigma ≠ 0) (z : ℂ) (CL BR : Matrix w w ℂ)
    (Theta : Matrix (w ⊕ w) (w ⊕ w) ℂ) (x : ThreeBlockVariable w → ℂ) :
    scaleLeadingRows sigma
      (packetLiteralK z CL BR Theta (fun e => sigma⁻¹ * x e)) =
    packetLiteralK (sigma * z) (sigma • CL) (sigma • BR) Theta x := by
  unfold scaleLeadingRows packetLiteralK
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add]
  congr 1
  · ext i j
    change sigma * (threeBlockDelta (fun e => sigma⁻¹ * x e) _ _ - z * (1 : Matrix _ _ ℂ) _ _) =
      threeBlockDelta x _ _ - (sigma * z) * (1 : Matrix _ _ ℂ) _ _
    have hd := congrFun (congrFun
      (threeBlockDelta_scale_inverse sigma hsigma x)
      ((threeBlockIndexEquiv w).symm i)) ((threeBlockIndexEquiv w).symm j)
    simp only [Matrix.smul_apply, smul_eq_mul] at hd
    rw [mul_sub, hd]
    ring
  · unfold packetEndpointCoupling
    rw [endpointFactor_smul, Matrix.mul_smul]

def normalizedPacketBoundaryPolynomial
    (sigma z : ℂ) (CL BR : Matrix w w ℂ)
    (Theta : Matrix (w ⊕ w) (w ⊕ w) ℂ) : MvPolynomial (ThreeBlockVariable w) ℂ :=
  bind₁ (fun e => C sigma⁻¹ * X e) (packetBoundaryPolynomial z CL BR Theta)

theorem eval_normalizedPacketBoundaryPolynomial
    (sigma z : ℂ) (CL BR : Matrix w w ℂ)
    (Theta : Matrix (w ⊕ w) (w ⊕ w) ℂ) (x : ThreeBlockVariable w → ℂ) :
    eval x (normalizedPacketBoundaryPolynomial sigma z CL BR Theta) =
      eval (fun e => sigma⁻¹ * x e) (packetBoundaryPolynomial z CL BR Theta) := by
  have h := eval₂Hom_bind₁ (RingHom.id ℂ) x (fun e => C sigma⁻¹ * X e)
    (packetBoundaryPolynomial z CL BR Theta)
  change eval x (normalizedPacketBoundaryPolynomial sigma z CL BR Theta) =
    eval (fun e => eval x (C sigma⁻¹ * X e)) (packetBoundaryPolynomial z CL BR Theta) at h
  simpa only [eval_mul, eval_C, eval_X] using h

theorem normalizedPacketBoundaryPolynomial_eq_scaled
    (sigma : ℂ) (hsigma : sigma ≠ 0) (z : ℂ) (CL BR : Matrix w w ℂ)
    (Theta : Matrix (w ⊕ w) (w ⊕ w) ℂ) :
    normalizedPacketBoundaryPolynomial sigma z CL BR Theta =
      C (sigma⁻¹ ^ (3 * Fintype.card w)) *
        packetBoundaryPolynomial (sigma * z) (sigma • CL) (sigma • BR) Theta := by
  apply MvPolynomial.funext
  intro x
  rw [eval_normalizedPacketBoundaryPolynomial, eval_mul, eval_C,
    eval_packetBoundaryPolynomial_eq_packetLiteralK_det,
    eval_packetBoundaryPolynomial_eq_packetLiteralK_det]
  rw [← scaleLeadingRows_packetLiteralK sigma hsigma z CL BR Theta x]
  simpa only [card_packet3] using
    det_eq_inv_pow_mul_scaleLeadingRows_det sigma hsigma
      (packetLiteralK z CL BR Theta (fun e => sigma⁻¹ * x e))

def normalizedPacketBoundaryCoefficient
    (sigma z : ℂ) (CL BR : Matrix w w ℂ)
    (Theta : Matrix (w ⊕ w) (w ⊕ w) ℂ) : ℝ :=
  ‖(WithLp.toLp 2 (fun S : Finset (ThreeBlockVariable w) =>
      coeff (squarefreeExponent S)
        (normalizedPacketBoundaryPolynomial sigma z CL BR Theta)) :
      CoeffSpace (ThreeBlockVariable w))‖

theorem normalizedPacketBoundaryCoefficient_eq_scaled
    (sigma : ℂ) (hsigma : sigma ≠ 0) (z : ℂ) (CL BR : Matrix w w ℂ)
    (Theta : Matrix (w ⊕ w) (w ⊕ w) ℂ) :
    normalizedPacketBoundaryCoefficient sigma z CL BR Theta =
      ‖sigma⁻¹ ^ (3 * Fintype.card w)‖ *
        packetBoundaryCoefficientNorm (sigma * z) (sigma • CL) (sigma • BR) Theta := by
  have hv : (WithLp.toLp 2 (fun S : Finset (ThreeBlockVariable w) =>
      coeff (squarefreeExponent S)
        (normalizedPacketBoundaryPolynomial sigma z CL BR Theta)) :
      CoeffSpace (ThreeBlockVariable w)) =
        sigma⁻¹ ^ (3 * Fintype.card w) •
          globalBoundaryCoeffVector (sigma * z) (sigma • CL) (sigma • BR) Theta := by
    ext S
    simp only [normalizedPacketBoundaryPolynomial_eq_scaled sigma hsigma,
      coeff_C_mul, globalBoundaryCoeffVector_apply]
    rfl
  rw [normalizedPacketBoundaryCoefficient, hv, norm_smul]
  rfl

def packetRowScale (W : ℕ) : ℂ := (Real.sqrt (3 * (W : ℝ)) : ℂ)

theorem packetRowScale_ne_zero (W : ℕ) (hW : 0 < W) : packetRowScale W ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))

theorem blockNormalization_eq_packetRowScale_inv (W : ℕ) :
    (blockNormalization W : ℂ) = (packetRowScale W)⁻¹ := by
  simp [blockNormalization, packetRowScale]

/-- The concrete coefficient norm in the raw variance-one atom variables. -/
def rademacherPacketBoundaryCoefficient (W : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) : ℝ :=
  normalizedPacketBoundaryCoefficient (packetRowScale W) z CL BR Theta

theorem packetBoundaryEval_eq_scaled_raw (W : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ)
    (x : PacketAtomRows W) :
    packetBoundaryEval W z CL BR Theta x =
      (packetRowScale W)⁻¹ ^ (3 * W) *
        eval (fun e => (x (packetIndexEquiv W e.1.1) (packetIndexEquiv W e.1.2) : ℂ))
          (packetBoundaryPolynomial ((packetRowScale W) * z)
            ((packetRowScale W) • CL) ((packetRowScale W) • BR) Theta) := by
  let raw : ThreeBlockVariable (Fin W) → ℂ :=
    fun e => (x (packetIndexEquiv W e.1.1) (packetIndexEquiv W e.1.2) : ℂ)
  have he : packetAtomAssignment W x = fun e => (packetRowScale W)⁻¹ * raw e := by
    funext e
    simp only [packetAtomAssignment, Complex.ofReal_mul,
      blockNormalization_eq_packetRowScale_inv, raw]
  rw [packetBoundaryEval, he, ← eval_normalizedPacketBoundaryPolynomial,
    normalizedPacketBoundaryPolynomial_eq_scaled _ (packetRowScale_ne_zero W hW),
    eval_mul, eval_C]
  simp only [Fintype.card_fin, raw]

end BernoulliSection8
