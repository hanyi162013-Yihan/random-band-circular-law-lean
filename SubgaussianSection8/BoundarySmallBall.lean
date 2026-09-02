import SubgaussianSection8.Inputs
import SubgaussianSection8.IID
import BernoulliSection8.PhysicalBoundaryScaling
import BernoulliSection9.TerminalConcretePublic
import BernoulliSection9.TerminalCanonicalLargeW
import BernoulliSection9.BoundarySmallBall

/-! # Cook's terminal estimate for the actual normalized boundary packet

The observed polynomial is `packetBoundaryEval`, exactly the boundary
expression of the three physical block rows. Its coefficient norm is
extracted from the actual normalized polynomial in variance-one atoms.
The only analytic input is the explicit Cook estimate. The atom family,
canonical width inequalities, row normalization and dense boundary-chart
passage are all discharged here. Endpoints and the outside relation are
deterministic parameters; their invertibility is the ordinary good-event
condition used by the global proof.
-/

open MeasureTheory
open scoped Matrix

noncomputable section

namespace SubgaussianSection8
open BernoulliSection8

open BernoulliSection9 BernoulliSection9.TerminalAssembly
open BernoulliSection10 BernoulliLinearAlgebra

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def subgaussianBoundaryWidthThreshold (Ξ : Atom) (cook : CookInput Ξ) (z : ℂ) : ℕ :=
  max (terminalCanonicalLargeWThreshold cook 1 (cook.subgaussianBound : ℝ))
    (max 1 (Nat.ceil (3 * ‖z‖ ^ 2)))

theorem packetRowScale_shift_bound (Ξ : Atom) (W : ℕ) (z : ℂ)
    (hW : 0 < W) (hz : 3 * ‖z‖ ^ 2 ≤ (W : ℝ)) :
    ‖packetRowScale W * z‖ ≤ (W : ℝ) ^ (1 : ℕ) := by
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hsq : (Real.sqrt (3 * (W : ℝ)) * ‖z‖) ^ 2 =
      3 * (W : ℝ) * ‖z‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hnonneg : 0 ≤ Real.sqrt (3 * (W : ℝ)) * ‖z‖ := by positivity
  simp only [norm_mul, packetRowScale, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), pow_one]
  nlinarith [mul_le_mul_of_nonneg_left hz hWpos.le]

theorem isUnit_det_smul (Ξ : Atom) {W : ℕ} (sigma : ℂ) (hsigma : sigma ≠ 0)
    (A : Matrix (Fin W) (Fin W) ℂ) (hA : IsUnit A.det) : IsUnit (sigma • A).det := by
  rw [Matrix.det_smul]
  exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hsigma)).mul hA

def subgaussianBoundaryBaseLoss (Ξ : Atom) (cook : CookInput Ξ) (W : ℕ) (z : ℂ) : ℝ :=
  terminalUniformBaseLoss cook 1 (packetRowScale W * z) ((packetFamily Ξ) W) (W : ℝ)

def subgaussianBoundaryBadProbability (Ξ : Atom) (cook : CookInput Ξ) (W : ℕ) : ℝ :=
  terminalUniformBadProbability cook W 1 (W : ℝ)

theorem subgaussianBoundaryWidthThreshold_pos (Ξ : Atom) (cook : CookInput Ξ) (z : ℂ) :
    0 < (subgaussianBoundaryWidthThreshold Ξ) cook z := by
  have h : 1 ≤ (subgaussianBoundaryWidthThreshold Ξ) cook z :=
    (le_max_left _ _).trans (le_max_right _ _)
  omega

theorem subgaussianBoundaryBaseLoss_nonneg (Ξ : Atom) (cook : CookInput Ξ) (W : ℕ) (z : ℂ) :
    0 ≤ (subgaussianBoundaryBaseLoss Ξ) cook W z :=
  terminalUniformBaseLoss_nonneg cook 1 _ _ _

theorem subgaussianBoundaryBadProbability_nonneg (Ξ : Atom) (cook : CookInput Ξ) (W : ℕ) :
    0 ≤ (subgaussianBoundaryBadProbability Ξ) cook W := by
  have h1 := cook.C_nonneg (terminalCanonicalFirstCookExponent 1)
  have h2 := cook.C_nonneg (terminalCanonicalSecondCookExponent cook 1)
  unfold subgaussianBoundaryBadProbability terminalUniformBadProbability uniformCookFailureBound
  positivity

/-- The capped coefficient-relative estimate and zero-probability bound for
the literal normalized packet. No terminal, RRQR, conditioning or polynomial
certificate is supplied by the caller. -/
def subgaussianBoundarySmallBall (Ξ : Atom)
    (cook : CookInput Ξ) (W : ℕ) (z : ℂ)
    (hW : (subgaussianBoundaryWidthThreshold Ξ) cook z ≤ W)
    (CL BR : Matrix (Fin W) (Fin W) ℂ) (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) (hTheta : IsUnit Theta.det) :
    TerminalSmallBallConclusion (packetAtomRowsLaw W Ξ.law)
      (rademacherPacketBoundaryCoefficient W z CL BR Theta)
      (packetBoundaryEval W z CL BR Theta)
      ((subgaussianBoundaryBaseLoss Ξ) cook W z)
      ((subgaussianBoundaryBadProbability Ξ) cook W) := by
  have hW0 : 0 < W := by
    have h1 : 1 ≤ W := (le_max_left _ _).trans ((le_max_right _ _).trans hW)
    omega
  have hthreshold : terminalCanonicalLargeWThreshold cook 1
      (cook.subgaussianBound : ℝ) ≤ W := (le_max_left _ _).trans hW
  have hnormz : 3 * ‖z‖ ^ 2 ≤ (W : ℝ) := by
    exact (Nat.le_ceil _).trans (by
      exact_mod_cast ((le_max_right _ _).trans ((le_max_right _ _).trans hW) :
        Nat.ceil (3 * ‖z‖ ^ 2) ≤ W))
  have hshift := (packetRowScale_shift_bound Ξ) W z hW0 hnormz
  have hsub : (((packetFamily Ξ) W).subgaussianParameter : ℝ) ≤
      (cook.subgaussianBound : ℝ) := by
    simpa using (show (Ξ.parameter : ℝ) ≤ (cook.subgaussianBound : ℝ) by
      exact_mod_cast cook.parameter_le)
  let C := packetTerminalConcreteConclusion cook (packetAtomRowsLaw W Ξ.law)
    1 (packetRowScale W * z) ((packetFamily Ξ) W) (W : ℝ)
      (packetTerminalCanonicalLargeWConditions_of_ge_threshold cook 1
        (cook.subgaussianBound : ℝ) (by exact_mod_cast cook.subgaussianBound_one_le)
        (packetRowScale W * z) ((packetFamily Ξ) W) hsub hsub hthreshold hshift)
  have hsigma := packetRowScale_ne_zero W hW0
  have hraw := BoundaryAssembly.literalCoordinateTerminalTheorem_of_packet
    ((packetFamily Ξ) W) (packetRowScale W * z)
    ((packetRowScale W) • CL) ((packetRowScale W) • BR)
    ((isUnit_det_smul Ξ) _ hsigma CL hCL) ((isUnit_det_smul Ξ) _ hsigma BR hBR)
    ((subgaussianBoundaryBaseLoss Ξ) cook W z) ((subgaussianBoundaryBadProbability Ξ) cook W)
    (terminalUniformBaseLoss_nonneg cook 1 _ _ _) (fun Q => (C Q).conclusion)
    Theta hTheta
  have hscaled := hraw.commonScale ((packetRowScale W)⁻¹ ^ (3 * W))
    (pow_ne_zero _ (inv_ne_zero hsigma))
  have hcoeff : rademacherPacketBoundaryCoefficient W z CL BR Theta =
      ‖(packetRowScale W)⁻¹ ^ (3 * W)‖ *
        packetBoundaryCoefficientNorm (packetRowScale W * z)
          ((packetRowScale W) • CL) ((packetRowScale W) • BR) Theta := by
    simpa only [rademacherPacketBoundaryCoefficient, Fintype.card_fin] using
      normalizedPacketBoundaryCoefficient_eq_scaled (packetRowScale W) hsigma z CL BR Theta
  have hvalue : packetBoundaryEval W z CL BR Theta =
      fun x => (packetRowScale W)⁻¹ ^ (3 * W) *
        MvPolynomial.eval (fun e => (((packetFamily Ξ) W).atom e x : ℂ))
          (packetBoundaryPolynomial (packetRowScale W * z)
            ((packetRowScale W) • CL) ((packetRowScale W) • BR) Theta) := by
    funext x
    exact packetBoundaryEval_eq_scaled_raw W hW0 z CL BR Theta x
  rw [hcoeff, hvalue]
  exact hscaled

/-- The explicit inverse comparison factor for the coefficient-to-Gram
bound, before any asymptotic simplification of its deterministic constants. -/
def subgaussianBoundaryInverseGamma (Ξ : Atom) (W : ℕ) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ‖(packetRowScale W)⁻¹ ^ (3 * W)‖ *
    (packetEndpointComparisonConstant (packetRowScale W * z)
      ((packetRowScale W) • CL) ((packetRowScale W) • BR))⁻¹

theorem subgaussianBoundaryInverseGamma_pos (Ξ : Atom) (W : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ) :
    0 < (subgaussianBoundaryInverseGamma Ξ) W z CL BR := by
  exact mul_pos (norm_pos_iff.mpr (pow_ne_zero _ (inv_ne_zero (packetRowScale_ne_zero W hW))))
    (inv_pos.mpr (packetEndpointComparisonConstant_pos _ _ _))

theorem subgaussianPacketBoundaryCoefficient_gram_lower (Ξ : Atom)
    (W : ℕ) (hW : 0 < W) (z : ℂ)
    (CL BR : Matrix (Fin W) (Fin W) ℂ) (hCL : IsUnit CL.det) (hBR : IsUnit BR.det)
    (Theta : Matrix (Fin W ⊕ Fin W) (Fin W ⊕ Fin W) ℂ) (hTheta : IsUnit Theta.det) :
    (subgaussianBoundaryInverseGamma Ξ) W z CL BR * gramVolume Theta ≤
      rademacherPacketBoundaryCoefficient W z CL BR Theta := by
  have hsigma := packetRowScale_ne_zero W hW
  have h := (globalBoundaryCoefficientNorm_bounds_fullyInstantiated
    (packetRowScale W * z) ((packetRowScale W) • CL) ((packetRowScale W) • BR)
    ((isUnit_det_smul Ξ) _ hsigma CL hCL) ((isUnit_det_smul Ξ) _ hsigma BR hBR)
    Theta hTheta).1
  rw [rademacherPacketBoundaryCoefficient,
    normalizedPacketBoundaryCoefficient_eq_scaled _ hsigma]
  simpa only [Fintype.card_fin, subgaussianBoundaryInverseGamma,
    packetEndpointComparisonConstant, mul_assoc] using
      mul_le_mul_of_nonneg_left h (norm_nonneg ((packetRowScale W)⁻¹ ^ (3 * W)))

end SubgaussianSection8
