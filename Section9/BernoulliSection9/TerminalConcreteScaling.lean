import BernoulliSection9.TerminalAssembly
import Mathlib.Tactic

/-!
# Literal physical-to-variance-one scaling for the terminal determinant

This file formalizes equations (9.12)--(9.13) at the concrete three-packet
level.  The physical packet entries are `sigma⁻¹` times the variance-one
atoms.  Multiplying all `3W` packet rows by `sigma` changes the spectral
parameter and the outer deformation to `sigma * z` and `sigma • Q`, and
contributes exactly `sigma ^ (3 * card W)` to the determinant and its
complete squarefree coefficient vector.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliSection9

namespace TerminalConcreteScaling

open Matrix MvPolynomial

variable {Omega w : Type*} [MeasurableSpace Omega]
variable [Fintype w] [DecidableEq w]
variable {mu : MeasureTheory.Measure Omega}

abbrev PacketOuter (w : Type*) := TerminalAssembly.PacketOuter w

/-- The physical terminal matrix: the random packet entries have size
`sigma⁻¹`, while `z` and `Q` remain in the physical normalization. -/
def physicalThreeBlockH
    (sigma : ℂ) (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ)
    (z : ℂ) (x : BernoulliLinearAlgebra.ThreeBlockVariable w → ℂ) :
    Matrix (BernoulliLinearAlgebra.ThreeBlockIndex w)
      (BernoulliLinearAlgebra.ThreeBlockIndex w) ℂ :=
  BernoulliLinearAlgebra.threeBlockH
    (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) z
    (fun e ↦ sigma⁻¹ * x e)

/-- The same physical normalization at the polynomial level.  This is a
literal determinant matrix, rather than a definition by rescaling the
already constructed coefficient norm. -/
def physicalThreeBlockHPolynomial
    (sigma : ℂ) (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ)
    (z : ℂ) :
    Matrix (BernoulliLinearAlgebra.ThreeBlockIndex w)
      (BernoulliLinearAlgebra.ThreeBlockIndex w)
      (MvPolynomial (BernoulliLinearAlgebra.ThreeBlockVariable w) ℂ) :=
  (C sigma⁻¹ : MvPolynomial
      (BernoulliLinearAlgebra.ThreeBlockVariable w) ℂ) •
      BernoulliLinearAlgebra.threeBlockDeltaPolynomial (w := w) -
      (C z : MvPolynomial
        (BernoulliLinearAlgebra.ThreeBlockVariable w) ℂ) •
        (1 : Matrix (BernoulliLinearAlgebra.ThreeBlockIndex w)
        (BernoulliLinearAlgebra.ThreeBlockIndex w)
        (MvPolynomial (BernoulliLinearAlgebra.ThreeBlockVariable w) ℂ)) +
    (BernoulliLinearAlgebra.threeBlockEmb
      (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q)).map C

/-- Literal physical determinant polynomial. -/
def physicalThreeBlockDetPolynomial
    (sigma : ℂ) (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ)
    (z : ℂ) :
    MvPolynomial (BernoulliLinearAlgebra.ThreeBlockVariable w) ℂ :=
  (physicalThreeBlockHPolynomial sigma Q z).det

/-- Complete squarefree coefficient vector in the physical normalization. -/
def physicalPacketTerminalCoeffVector
    (sigma : ℂ) (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ)
    (z : ℂ) :
    BernoulliLinearAlgebra.CoeffSpace
      (BernoulliLinearAlgebra.ThreeBlockVariable w) :=
  WithLp.toLp 2 (fun S ↦
    (physicalThreeBlockDetPolynomial sigma Q z).coeff
      (BernoulliLinearAlgebra.squarefreeExponent S))

/-- Complete coefficient norm in the physical normalization. -/
def physicalPacketTerminalCoefficientNorm
    (sigma : ℂ) (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ)
    (z : ℂ) : ℝ :=
  ‖physicalPacketTerminalCoeffVector sigma Q z‖

/-- Physical determinant evaluated at the variance-one atoms. -/
def physicalPacketTerminalValue
    (sigma : ℂ) (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ)
    (z : ℂ)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (omega : Omega) : ℂ :=
  (physicalThreeBlockH sigma Q z
    (fun e ↦ (X.atom e omega : ℂ))).det

/-- There are exactly `3 * card w` physical packet rows. -/
@[simp] theorem card_threeBlockIndex :
    Fintype.card (BernoulliLinearAlgebra.ThreeBlockIndex w) =
      3 * Fintype.card w := by
  simp [BernoulliLinearAlgebra.ThreeBlockIndex,
    BernoulliLinearAlgebra.ThreeBlockOuter]
  omega

/-- Scaling the outer packet commutes literally with the packet-to-Boolean
coordinate reindexing. -/
theorem threeBlockOuterOfPacket_smul
    (sigma : ℂ) (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) :
    BernoulliLinearAlgebra.threeBlockOuterOfPacket (sigma • Q) =
      sigma • BernoulliLinearAlgebra.threeBlockOuterOfPacket Q := by
  ext i j
  rfl

/-- Scaling `Q` commutes with the literal outer embedding. -/
theorem threeBlockEmb_smul
    (sigma : ℂ)
    (Q : Matrix (BernoulliLinearAlgebra.ThreeBlockOuter w)
      (BernoulliLinearAlgebra.ThreeBlockOuter w) ℂ) :
    BernoulliLinearAlgebra.threeBlockEmb (sigma • Q) =
      sigma • BernoulliLinearAlgebra.threeBlockEmb Q := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [BernoulliLinearAlgebra.threeBlockEmb]

/-- Multiplication by `sigma` exactly removes the physical entry factor
`sigma⁻¹`. -/
theorem threeBlockDelta_physical_smul
    (sigma : ℂ) (hsigma : sigma ≠ 0)
    (x : BernoulliLinearAlgebra.ThreeBlockVariable w → ℂ) :
    sigma • BernoulliLinearAlgebra.threeBlockDelta
        (fun e ↦ sigma⁻¹ * x e) =
      BernoulliLinearAlgebra.threeBlockDelta x := by
  ext i j
  by_cases h : BernoulliLinearAlgebra.threeBlockFresh i j
  · simp [BernoulliLinearAlgebra.threeBlockDelta, h, hsigma]
  · simp [BernoulliLinearAlgebra.threeBlockDelta, h]

/-- Exact matrix identity behind (9.12): the variance-one terminal matrix is
`sigma` times the physical terminal matrix. -/
theorem rowScaled_threeBlockH_eq_smul_physical
    (sigma : ℂ) (hsigma : sigma ≠ 0)
    (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) (z : ℂ)
    (x : BernoulliLinearAlgebra.ThreeBlockVariable w → ℂ) :
    BernoulliLinearAlgebra.threeBlockH
        (BernoulliLinearAlgebra.threeBlockOuterOfPacket (sigma • Q))
        (sigma * z) x =
      sigma • physicalThreeBlockH sigma Q z x := by
  rw [physicalThreeBlockH, BernoulliLinearAlgebra.threeBlockH,
    BernoulliLinearAlgebra.threeBlockH, threeBlockOuterOfPacket_smul,
    threeBlockEmb_smul]
  rw [smul_add, smul_sub, threeBlockDelta_physical_smul sigma hsigma]
  congr 1
  ext i j
  simp [mul_assoc]

/-- Evaluation of the physical polynomial matrix gives the literal
physical matrix entry-for-entry. -/
@[simp] theorem eval_physicalThreeBlockHPolynomial
    (sigma : ℂ) (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ)
    (z : ℂ)
    (x : BernoulliLinearAlgebra.ThreeBlockVariable w → ℂ) :
    (eval x).mapMatrix (physicalThreeBlockHPolynomial sigma Q z) =
      physicalThreeBlockH sigma Q z x := by
  ext i j
  by_cases hfresh : BernoulliLinearAlgebra.threeBlockFresh i j <;>
    by_cases hij : i = j <;>
    simp [physicalThreeBlockHPolynomial, physicalThreeBlockH,
      BernoulliLinearAlgebra.threeBlockH,
      BernoulliLinearAlgebra.threeBlockDeltaPolynomial,
      BernoulliLinearAlgebra.threeBlockDelta, hfresh, hij]

/-- Evaluation of the physical determinant polynomial is the physical
terminal determinant. -/
theorem eval_physicalThreeBlockDetPolynomial
    (sigma : ℂ) (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ)
    (z : ℂ)
    (x : BernoulliLinearAlgebra.ThreeBlockVariable w → ℂ) :
    eval x (physicalThreeBlockDetPolynomial sigma Q z) =
      (physicalThreeBlockH sigma Q z x).det := by
  rw [physicalThreeBlockDetPolynomial, (eval x).map_det,
    eval_physicalThreeBlockHPolynomial]

/-- Polynomial analogue of `threeBlockDelta_physical_smul`. -/
theorem threeBlockDeltaPolynomial_physical_smul
    (sigma : ℂ) (hsigma : sigma ≠ 0) :
    (C sigma : MvPolynomial
        (BernoulliLinearAlgebra.ThreeBlockVariable w) ℂ) •
        ((C sigma⁻¹ : MvPolynomial
          (BernoulliLinearAlgebra.ThreeBlockVariable w) ℂ) •
          BernoulliLinearAlgebra.threeBlockDeltaPolynomial (w := w)) =
      BernoulliLinearAlgebra.threeBlockDeltaPolynomial (w := w) := by
  rw [smul_smul, ← map_mul]
  simp [hsigma]

/-- The polynomial-valued outer embedding commutes with physical row
scaling. -/
theorem map_threeBlockEmb_outer_smul
    (sigma : ℂ) (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) :
    (BernoulliLinearAlgebra.threeBlockEmb
      (BernoulliLinearAlgebra.threeBlockOuterOfPacket (sigma • Q))).map
        (C : ℂ → MvPolynomial
          (BernoulliLinearAlgebra.ThreeBlockVariable w) ℂ) =
      (C sigma : MvPolynomial
        (BernoulliLinearAlgebra.ThreeBlockVariable w) ℂ) •
        (BernoulliLinearAlgebra.threeBlockEmb
          (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q)).map
            (C : ℂ → MvPolynomial
              (BernoulliLinearAlgebra.ThreeBlockVariable w) ℂ) := by
  rw [threeBlockOuterOfPacket_smul, threeBlockEmb_smul]
  ext i j
  simp [map_mul]

/-- Polynomial matrix form of the exact row-scaling identity. -/
theorem rowScaled_threeBlockHPolynomial_eq_smul_physical
    (sigma : ℂ) (hsigma : sigma ≠ 0)
    (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) (z : ℂ) :
    BernoulliLinearAlgebra.threeBlockHPolynomial
        (BernoulliLinearAlgebra.threeBlockOuterOfPacket (sigma • Q))
        (sigma * z) =
      (C sigma : MvPolynomial
        (BernoulliLinearAlgebra.ThreeBlockVariable w) ℂ) •
        physicalThreeBlockHPolynomial sigma Q z := by
  rw [BernoulliLinearAlgebra.threeBlockHPolynomial,
    physicalThreeBlockHPolynomial, map_threeBlockEmb_outer_smul]
  rw [smul_add, smul_sub,
    threeBlockDeltaPolynomial_physical_smul sigma hsigma]
  rw [smul_smul, ← map_mul]

/-- Determinant-polynomial form of (9.12), with the exact exponent `3W`. -/
theorem rowScaled_threeBlockDetPolynomial_eq
    (sigma : ℂ) (hsigma : sigma ≠ 0)
    (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) (z : ℂ) :
    BernoulliLinearAlgebra.threeBlockDetPolynomial
        (BernoulliLinearAlgebra.threeBlockOuterOfPacket (sigma • Q))
        (sigma * z) =
      C (sigma ^ (3 * Fintype.card w)) *
        physicalThreeBlockDetPolynomial sigma Q z := by
  rw [BernoulliLinearAlgebra.threeBlockDetPolynomial,
    rowScaled_threeBlockHPolynomial_eq_smul_physical sigma hsigma,
    Matrix.det_smul, physicalThreeBlockDetPolynomial,
    card_threeBlockIndex, map_pow]

/-- Inverse direction displayed in (9.12). -/
theorem physicalThreeBlockDetPolynomial_eq_inv_mul_rowScaled
    (sigma : ℂ) (hsigma : sigma ≠ 0)
    (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) (z : ℂ) :
    physicalThreeBlockDetPolynomial sigma Q z =
      C (sigma⁻¹ ^ (3 * Fintype.card w)) *
        BernoulliLinearAlgebra.threeBlockDetPolynomial
          (BernoulliLinearAlgebra.threeBlockOuterOfPacket (sigma • Q))
          (sigma * z) := by
  rw [rowScaled_threeBlockDetPolynomial_eq sigma hsigma, ← mul_assoc,
    ← map_mul]
  simp [hsigma]

/-- Coefficient-by-coefficient form of (9.12). -/
theorem rowScaled_packetTerminalCoeffVector_eq_smul
    (sigma : ℂ) (hsigma : sigma ≠ 0)
    (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) (z : ℂ) :
    BernoulliLinearAlgebra.threeBlockDetCoeffVector
        (BernoulliLinearAlgebra.threeBlockOuterOfPacket (sigma • Q))
        (sigma * z) =
      sigma ^ (3 * Fintype.card w) •
        physicalPacketTerminalCoeffVector sigma Q z := by
  ext S
  change (BernoulliLinearAlgebra.threeBlockDetPolynomial
      (BernoulliLinearAlgebra.threeBlockOuterOfPacket (sigma • Q))
      (sigma * z)).coeff (BernoulliLinearAlgebra.squarefreeExponent S) = _
  rw [rowScaled_threeBlockDetPolynomial_eq sigma hsigma,
    MvPolynomial.coeff_C_mul]
  rfl

/-- The complete coefficient norm has the same common factor as the
determinant value. -/
theorem rowScaled_packetTerminalCoefficientNorm_eq
    (sigma : ℂ) (hsigma : sigma ≠ 0)
    (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) (z : ℂ) :
    TerminalAssembly.packetTerminalCoefficientNorm (sigma • Q) (sigma * z) =
      ‖sigma ^ (3 * Fintype.card w)‖ *
        physicalPacketTerminalCoefficientNorm sigma Q z := by
  rw [TerminalAssembly.packetTerminalCoefficientNorm,
    BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket,
    BernoulliLinearAlgebra.threeBlockDetCoefficientNorm,
    rowScaled_packetTerminalCoeffVector_eq_smul sigma hsigma,
    norm_smul]
  rfl

/-- Inverse coefficient-norm direction displayed in (9.12). -/
theorem physicalPacketTerminalCoefficientNorm_eq_inv_mul_rowScaled
    (sigma : ℂ) (hsigma : sigma ≠ 0)
    (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) (z : ℂ) :
    physicalPacketTerminalCoefficientNorm sigma Q z =
      ‖sigma ^ (3 * Fintype.card w)‖⁻¹ *
        TerminalAssembly.packetTerminalCoefficientNorm (sigma • Q)
          (sigma * z) := by
  rw [rowScaled_packetTerminalCoefficientNorm_eq sigma hsigma,
    ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (pow_ne_zero _ hsigma)),
    one_mul]

/-- Evaluated determinant form of (9.12). -/
theorem rowScaled_packetTerminalValue_eq
    (sigma : ℂ) (hsigma : sigma ≠ 0)
    (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) (z : ℂ)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (omega : Omega) :
    TerminalAssembly.packetTerminalValue (sigma • Q) (sigma * z) X omega =
      sigma ^ (3 * Fintype.card w) *
        physicalPacketTerminalValue sigma Q z X omega := by
  rw [TerminalAssembly.packetTerminalValue, physicalPacketTerminalValue,
    rowScaled_threeBlockH_eq_smul_physical sigma hsigma,
    Matrix.det_smul, card_threeBlockIndex]

/-- Inverse determinant-value direction displayed in (9.12). -/
theorem physicalPacketTerminalValue_eq_inv_mul_rowScaled
    (sigma : ℂ) (hsigma : sigma ≠ 0)
    (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) (z : ℂ)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (omega : Omega) :
    physicalPacketTerminalValue sigma Q z X omega =
      sigma⁻¹ ^ (3 * Fintype.card w) *
        TerminalAssembly.packetTerminalValue (sigma • Q) (sigma * z) X omega := by
  rw [rowScaled_packetTerminalValue_eq sigma hsigma, ← mul_assoc,
    ← mul_pow]
  simp [hsigma]

/-- Equation (9.13): the capped coefficient-to-value loss is invariant under
the literal physical-to-variance-one row scaling. -/
theorem cappedLogLoss_physical_eq_rowScaled
    (T : ℝ) (sigma : ℂ) (hsigma : sigma ≠ 0)
    (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) (z : ℂ)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (omega : Omega) :
    cappedLogLoss T (physicalPacketTerminalCoefficientNorm sigma Q z)
        (physicalPacketTerminalValue sigma Q z X omega) =
      cappedLogLoss T
        (TerminalAssembly.packetTerminalCoefficientNorm (sigma • Q)
          (sigma * z))
        (TerminalAssembly.packetTerminalValue (sigma • Q)
          (sigma * z) X omega) := by
  symm
  rw [rowScaled_packetTerminalCoefficientNorm_eq sigma hsigma,
    rowScaled_packetTerminalValue_eq sigma hsigma]
  exact cappedLogLoss_common_scale T
    (physicalPacketTerminalCoefficientNorm sigma Q z)
    (physicalPacketTerminalValue sigma Q z X omega)
    (sigma ^ (3 * Fintype.card w)) (pow_ne_zero _ hsigma)

/-- Equation (9.13): the physical and row-scaled determinants have exactly
the same zero event. -/
theorem physicalPacketTerminalValue_eq_zero_iff_rowScaled
    (sigma : ℂ) (hsigma : sigma ≠ 0)
    (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) (z : ℂ)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (omega : Omega) :
    physicalPacketTerminalValue sigma Q z X omega = 0 ↔
      TerminalAssembly.packetTerminalValue (sigma • Q)
        (sigma * z) X omega = 0 := by
  rw [rowScaled_packetTerminalValue_eq sigma hsigma]
  exact (common_scale_eq_zero_iff
    (physicalPacketTerminalValue sigma Q z X omega)
    (sigma ^ (3 * Fintype.card w)) (pow_ne_zero _ hsigma)).symm

/-- Set form of zero-event invariance, ready for probability statements. -/
theorem physicalPacketTerminalZeroEvent_eq_rowScaled
    (sigma : ℂ) (hsigma : sigma ≠ 0)
    (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) (z : ℂ)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w)) :
    {omega | physicalPacketTerminalValue sigma Q z X omega = 0} =
      {omega | TerminalAssembly.packetTerminalValue (sigma • Q)
        (sigma * z) X omega = 0} := by
  ext omega
  exact physicalPacketTerminalValue_eq_zero_iff_rowScaled
    sigma hsigma Q z X omega

/-! ## Caller-facing transfer of the complete terminal conclusion -/

/-- Internal common-scale transport kept in this low-level module so the
physical scaling bridge does not depend backwards on the arbitrary-frame
development. -/
private noncomputable def terminalConclusion_commonScale
    {coefficientNorm baseLoss badProbability : ℝ} {value : Omega → ℂ}
    (C : TerminalSmallBallConclusion mu coefficientNorm value
      baseLoss badProbability)
    (a : ℂ) (ha : a ≠ 0) :
    TerminalSmallBallConclusion mu (‖a‖ * coefficientNorm)
      (fun omega ↦ a * value omega) baseLoss badProbability := by
  have hnormA : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnormA0 : ‖a‖ ≠ 0 := hnormA.ne'
  have hcoefficient0 : coefficientNorm ≠ 0 := C.coefficientNorm_pos.ne'
  refine
    { coefficientNorm_pos := mul_pos hnormA C.coefficientNorm_pos
      capped := ?_
      zero_probability := ?_
      reverse_event := C.reverse_event
      reverse := ?_
      parseval := ?_ }
  · intro T hT
    have hfun :
        (fun omega ↦ cappedLogLoss T (‖a‖ * coefficientNorm)
          (a * value omega)) =
        (fun omega ↦ cappedLogLoss T coefficientNorm (value omega)) := by
      funext omega
      exact cappedLogLoss_common_scale T coefficientNorm (value omega) a ha
    rw [hfun]
    exact C.capped T hT
  · have hset : {omega | a * value omega = 0} =
        {omega | value omega = 0} := by
      ext omega
      exact common_scale_eq_zero_iff (value omega) a ha
    rw [hset]
    exact C.zero_probability
  · intro omega homega
    have hratio :
        ‖a * value omega‖ / (‖a‖ * coefficientNorm) =
          ‖value omega‖ / coefficientNorm := by
      rw [norm_mul]
      field_simp [hnormA0, hcoefficient0]
    rw [hratio]
    exact C.reverse omega homega
  · calc
      (‖a‖ * coefficientNorm) ^ 2 =
          ‖a‖ ^ 2 * coefficientNorm ^ 2 := by ring
      _ = ‖a‖ ^ 2 * ∫ omega, ‖value omega‖ ^ 2 ∂mu := by
        rw [C.parseval]
      _ = ∫ omega, ‖a‖ ^ 2 * ‖value omega‖ ^ 2 ∂mu := by
        rw [MeasureTheory.integral_const_mul]
      _ = ∫ omega, ‖a * value omega‖ ^ 2 ∂mu := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with omega
        rw [norm_mul]
        ring

/-- A complete row-scaled terminal conclusion transfers back to the
physical `sigma⁻¹` entry normalization without any caller-side rewriting.
The internal common scalar is exactly `sigma⁻¹ ^ (3 * card w)`. -/
noncomputable def physicalTerminalConclusion_of_rowScaled
    (sigma : ℂ) (hsigma : sigma ≠ 0)
    (Q : Matrix (PacketOuter w) (PacketOuter w) ℂ) (z : ℂ)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    {baseLoss badProbability : ℝ}
    (C : TerminalSmallBallConclusion mu
      (TerminalAssembly.packetTerminalCoefficientNorm (sigma • Q)
        (sigma * z))
      (TerminalAssembly.packetTerminalValue (sigma • Q) (sigma * z) X)
      baseLoss badProbability) :
    TerminalSmallBallConclusion mu
      (physicalPacketTerminalCoefficientNorm sigma Q z)
      (physicalPacketTerminalValue sigma Q z X)
      baseLoss badProbability := by
  let a : ℂ := sigma⁻¹ ^ (3 * Fintype.card w)
  have ha : a ≠ 0 := pow_ne_zero _ (inv_ne_zero hsigma)
  let D := terminalConclusion_commonScale C a ha
  have hnorm : ‖a‖ = ‖sigma ^ (3 * Fintype.card w)‖⁻¹ := by
    simp [a, norm_pow]
  have hcoefficient :
      ‖a‖ * TerminalAssembly.packetTerminalCoefficientNorm (sigma • Q)
          (sigma * z) =
        physicalPacketTerminalCoefficientNorm sigma Q z := by
    rw [physicalPacketTerminalCoefficientNorm_eq_inv_mul_rowScaled
      sigma hsigma Q z, hnorm]
  have hvalue :
      (fun omega ↦ a * TerminalAssembly.packetTerminalValue
        (sigma • Q) (sigma * z) X omega) =
        physicalPacketTerminalValue sigma Q z X := by
    funext omega
    exact (physicalPacketTerminalValue_eq_inv_mul_rowScaled
      sigma hsigma Q z X omega).symm
  simpa only [hcoefficient, hvalue] using D

end TerminalConcreteScaling

end BernoulliSection9
