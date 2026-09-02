import BernoulliSection9.SquarefreeParseval
import BernoulliSection9.TerminalLossBounds
import BernoulliSection9.TerminalProbability
import BernoulliLinearAlgebra.ConcreteBoundaryFinal
import Mathlib.Tactic

/-!
# Terminal small-ball assembly

This module connects the literal three-block determinant and coefficient
vector from the read-only Section 9.1.3 development to the probability and
loss bookkeeping proved in this project.  In particular, measurability,
integrability, strict positivity of the coefficient norm, the reverse
estimate on a coordinatewise bounded event, and Parseval are discharged
internally.

The final section also records the internal bridge from
the two canonical conditional Cook squares to the literal three-block
determinant.  It is deliberately not presented as a caller-facing
assumption or as an RRQR certificate.
-/

open scoped BigOperators ProbabilityTheory Matrix.Norms.L2Operator

noncomputable section

namespace BernoulliSection9

open MeasureTheory

namespace TerminalAssembly

universe u

abbrev PacketOuter (w : Type*) := w ⊕ w

/-- Literal terminal determinant evaluated at the iid packet atoms. -/
def packetTerminalValue
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    {mu : Measure Omega}
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (omega : Omega) : Complex :=
  (BernoulliLinearAlgebra.threeBlockH
    (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) z
    (fun i => (X.atom i omega : Complex))).det

/-- The literal coefficient norm attached to `packetTerminalValue`. -/
def packetTerminalCoefficientNorm
    {w : Type*} [Fintype w] [DecidableEq w]
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex) : Real :=
  BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket z Q

/-- Re-express the literal determinant as the squarefree evaluator used by
the Parseval module. -/
theorem packetTerminalValue_eq_evalSquarefree
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    {mu : Measure Omega}
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (omega : Omega) :
    packetTerminalValue Q z X omega =
      evalSquarefree
        (fun S => BernoulliLinearAlgebra.threeBlockDetCoefficient
          (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) z S)
        X.atom omega := by
  rw [packetTerminalValue]
  rw [← BernoulliLinearAlgebra.eval_threeBlockDetPolynomial]
  exact eval_threeBlockDetPolynomial_eq_evalSquarefree
    (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) z
    (fun i => X.atom i omega)

/-- Every squarefree monomial in measurable atoms is measurable. -/
theorem measurable_squarefreeMonomial
    {Omega iota : Type*} [MeasurableSpace Omega]
    (X : iota -> Omega -> Real) (hX : forall i, Measurable (X i))
    (S : Finset iota) :
    Measurable (fun omega => squarefreeMonomial X S omega) := by
  classical
  unfold squarefreeMonomial
  fun_prop

/-- A finite squarefree polynomial in measurable real atoms is measurable. -/
theorem measurable_evalSquarefree
    {Omega iota : Type*} [MeasurableSpace Omega]
    [Fintype iota]
    (c : Finset iota -> Complex) (X : iota -> Omega -> Real)
    (hX : forall i, Measurable (X i)) :
    Measurable (fun omega => evalSquarefree c X omega) := by
  classical
  unfold evalSquarefree
  apply Finset.measurable_sum
  intro S _hS
  exact (measurable_squarefreeMonomial X hX S).complex_ofReal.const_mul (c S)

/-- Measurability of the literal terminal determinant is automatic from the
iid-family measurability fields. -/
theorem measurable_packetTerminalValue
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    {mu : Measure Omega}
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w)) :
    Measurable (packetTerminalValue Q z X) := by
  rw [show packetTerminalValue Q z X = fun omega =>
      evalSquarefree
        (fun S => BernoulliLinearAlgebra.threeBlockDetCoefficient
          (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) z S)
        X.atom omega by
    funext omega
    exact packetTerminalValue_eq_evalSquarefree Q z X omega]
  exact measurable_evalSquarefree _ _ X.measurable_atom

/-- The paper's special capped loss is measurable whenever its value is. -/
theorem measurable_cappedLogLoss_comp
    {Omega : Type*} [MeasurableSpace Omega]
    (T c : Real) (value : Omega -> Complex) (hvalue : Measurable value) :
    Measurable (fun omega => cappedLogLoss T c (value omega)) := by
  unfold cappedLogLoss
  apply Measurable.ite
  · exact hvalue (measurableSet_singleton 0)
  · exact measurable_const
  · exact Measurable.min measurable_const
      (Real.continuous_posLog.measurable.comp
        (measurable_const.div hvalue.norm))

/-- For positive caps, the terminal capped loss is integrable without any
extra moment hypothesis, since it is measurable and bounded by the cap. -/
theorem integrable_cappedLogLoss_packetTerminalValue
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (T : Real) (hT : 0 < T) :
    Integrable (fun omega => cappedLogLoss T
      (packetTerminalCoefficientNorm Q z)
      (packetTerminalValue Q z X omega)) mu := by
  apply (integrable_const T).mono'
  · exact (measurable_cappedLogLoss_comp T
      (packetTerminalCoefficientNorm Q z)
      (packetTerminalValue Q z X)
      (measurable_packetTerminalValue Q z X)).aestronglyMeasurable
  · filter_upwards [] with omega
    rw [Real.norm_of_nonneg (cappedLogLoss_nonneg hT.le)]
    exact cappedLogLoss_le_cap

/-- Exact Parseval for the literal three-block terminal determinant. -/
theorem packetTerminal_parseval
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w)) :
    packetTerminalCoefficientNorm Q z ^ 2 =
      ∫ omega, norm (packetTerminalValue Q z X omega) ^ 2 ∂mu := by
  symm
  simpa [packetTerminalValue, packetTerminalCoefficientNorm,
    BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket] using
    integral_norm_threeBlockH_det_sq
      (μ := mu) (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) z X

/-! ## A deliberately coarse reverse fallback -/

/-- The coordinatewise bounded event underlying `E_max`. -/
def coordinatewiseBoundedEvent
    {Omega iota : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega}
    (X : IidSubgaussianFamily Omega mu iota) (M : Real) : Set Omega :=
  {omega | forall i, abs (X.atom i omega) <= M}

/-- On `E_max`, every squarefree monomial is bounded by the full ambient
power. -/
theorem norm_squarefreeMonomial_le_full_power
    {Omega iota : Type*} [MeasurableSpace Omega] [Fintype iota]
    (Y : iota -> Omega -> Real) (M : Real) (hM : 1 <= M)
    (omega : Omega) (homega : forall i, abs (Y i omega) <= M)
    (S : Finset iota) :
    norm (squarefreeMonomial Y S omega) <= M ^ Fintype.card iota := by
  classical
  have hprod : (∏ i ∈ S, abs (Y i omega)) <= ∏ _i ∈ S, M := by
    exact Finset.prod_le_prod
      (fun _ _ => abs_nonneg _)
      (fun i _ => homega i)
  calc
    norm (squarefreeMonomial Y S omega) = ∏ i ∈ S, abs (Y i omega) := by
      simp [squarefreeMonomial, Real.norm_eq_abs]
    _ <= ∏ _i ∈ S, M := hprod
    _ = M ^ S.card := by simp
    _ <= M ^ Fintype.card iota :=
      pow_le_pow_right₀ hM (Finset.card_le_card (Finset.subset_univ S))

/-- A mechanically useful but non-sharp triangle estimate.  It sums over
all subsets of the `7 W^2` fresh-entry labels, so its cardinality factor is
`2^(7 W^2)`.  Consequently this lemma has quadratic loss and is **not** the
paper's `O(W log W)` reverse estimate (7.22). -/
theorem norm_packetTerminalValue_le_quadraticFallback
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    {mu : Measure Omega}
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (M : Real) (hM : 1 <= M)
    (omega : Omega) (homega : omega ∈ coordinatewiseBoundedEvent X M) :
    norm (packetTerminalValue Q z X omega) <=
      ((Fintype.card
          (Finset (BernoulliLinearAlgebra.ThreeBlockVariable w)) : Nat) : Real) *
        M ^ Fintype.card (BernoulliLinearAlgebra.ThreeBlockVariable w) *
          packetTerminalCoefficientNorm Q z := by
  classical
  let coeff := BernoulliLinearAlgebra.threeBlockDetCoeffVector
    (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) z
  have hcoeff (S : Finset (BernoulliLinearAlgebra.ThreeBlockVariable w)) :
      norm (coeff S) <= packetTerminalCoefficientNorm Q z := by
    simpa [coeff, packetTerminalCoefficientNorm,
      BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket,
      BernoulliLinearAlgebra.threeBlockDetCoefficientNorm] using
      (PiLp.norm_apply_le coeff S)
  have hmonomial (S : Finset
      (BernoulliLinearAlgebra.ThreeBlockVariable w)) :
      norm (squarefreeMonomial X.atom S omega) <=
        M ^ Fintype.card (BernoulliLinearAlgebra.ThreeBlockVariable w) := by
    exact norm_squarefreeMonomial_le_full_power X.atom M hM omega homega S
  rw [packetTerminalValue_eq_evalSquarefree]
  calc
    norm (evalSquarefree
        (fun S => BernoulliLinearAlgebra.threeBlockDetCoefficient
          (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) z S)
        X.atom omega) <=
        ∑ S : Finset (BernoulliLinearAlgebra.ThreeBlockVariable w),
          norm (BernoulliLinearAlgebra.threeBlockDetCoefficient
            (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) z S *
              (squarefreeMonomial X.atom S omega : Complex)) := by
      exact norm_sum_le _ _
    _ <= ∑ _S : Finset (BernoulliLinearAlgebra.ThreeBlockVariable w),
        packetTerminalCoefficientNorm Q z *
          M ^ Fintype.card (BernoulliLinearAlgebra.ThreeBlockVariable w) := by
      apply Finset.sum_le_sum
      intro S _hS
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul (hcoeff S) (hmonomial S)
        (norm_nonneg _) (by
          exact norm_nonneg
            (BernoulliLinearAlgebra.threeBlockDetCoeffVector
              (BernoulliLinearAlgebra.threeBlockOuterOfPacket Q) z))
    _ = ((Fintype.card
          (Finset (BernoulliLinearAlgebra.ThreeBlockVariable w)) : Nat) : Real) *
        M ^ Fintype.card (BernoulliLinearAlgebra.ThreeBlockVariable w) *
          packetTerminalCoefficientNorm Q z := by
      simp
      ring

/-- Quadratic-loss reverse fallback.  The sharp paper estimate must instead
sum only over valid partial-permutation matchings (and account for diagonal
translation); this theorem is intentionally not used by the public result. -/
theorem packetTerminal_reverse_quadraticFallback
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w] [LinearOrder w]
    {mu : Measure Omega}
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (M reverseLoss : Real) (hM : 1 <= M) (hreverseLoss : 0 <= reverseLoss)
    (hfactor :
      ((Fintype.card
          (Finset (BernoulliLinearAlgebra.ThreeBlockVariable w)) : Nat) : Real) *
        M ^ Fintype.card (BernoulliLinearAlgebra.ThreeBlockVariable w) <=
          Real.exp reverseLoss) :
    ∀ omega, omega ∈ coordinatewiseBoundedEvent X M ->
      Real.posLog
        (norm (packetTerminalValue Q z X omega) /
          packetTerminalCoefficientNorm Q z) <= reverseLoss := by
  have hcomparison :=
    BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket_concreteComparison
      (W := w) z
  have hKpos : 0 <
      BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
        (W := w) z :=
    lt_of_lt_of_le zero_lt_one hcomparison.one_le
  have hcoefficientPos : 0 < packetTerminalCoefficientNorm Q z := by
    have hlowerPos : 0 <
        (BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
          (W := w) z)⁻¹ * BernoulliLinearAlgebra.gramVolume Q :=
      mul_pos (inv_pos.mpr hKpos) (BernoulliLinearAlgebra.gramVolume_pos Q)
    exact hlowerPos.trans_le (by
      simpa [packetTerminalCoefficientNorm] using hcomparison.lower Q)
  intro omega homega
  apply posLog_value_div_coefficient_le hreverseLoss
    hcoefficientPos
  exact (norm_packetTerminalValue_le_quadraticFallback
    Q z X M hM omega homega).trans (by
      have hc := hcoefficientPos.le
      nlinarith [mul_le_mul_of_nonneg_right hfactor hc])

section ConcreteCoefficientComparison

variable {w : Type*} [Fintype w] [DecidableEq w] [LinearOrder w]

/-- The stable Section 9.1.3 theorem gives the literal packet coefficient
norm a two-sided Gram-volume comparison, with no mask certificate left in
the signature. -/
theorem packetTerminalCoefficientNorm_bounds
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex) (z : Complex) :
    let K := BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
      (W := w) z
    K⁻¹ * BernoulliLinearAlgebra.gramVolume Q <=
        packetTerminalCoefficientNorm Q z ∧
      packetTerminalCoefficientNorm Q z <=
        K * BernoulliLinearAlgebra.gramVolume Q := by
  dsimp only
  constructor
  · simpa [packetTerminalCoefficientNorm] using
      (BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket_concreteComparison
        (W := w) z).lower Q
  · simpa [packetTerminalCoefficientNorm] using
      (BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket_concreteComparison
        (W := w) z).upper Q

/-- In particular the literal coefficient norm is strictly positive for
every deterministic outer deformation, including singular ones. -/
theorem packetTerminalCoefficientNorm_pos
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex) (z : Complex) :
    0 < packetTerminalCoefficientNorm Q z := by
  let K := BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
    (W := w) z
  have hcmp := packetTerminalCoefficientNorm_bounds Q z
  have hKone : 1 <= K :=
    (BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket_concreteComparison
        (W := w) z).one_le
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hKone
  have hlower : 0 < K⁻¹ * BernoulliLinearAlgebra.gramVolume Q :=
    mul_pos (inv_pos.mpr hKpos) (BernoulliLinearAlgebra.gramVolume_pos Q)
  exact hlower.trans_le hcmp.1

end ConcreteCoefficientComparison

/-- Internal output expected from the RRQR/CUR/two-Cook part of the proof.
It mentions only its mathematical conclusion: a measurable exceptional
event and a lower bound relative to Gram volume.  This structure is not a
literature input and is not intended to occur in the final public theorem. -/
structure PacketTerminalGoodEventControl
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    (mu : Measure Omega)
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (valueLoss badProbability : Real) where
  bad : Set Omega
  measurable_bad : MeasurableSet bad
  probability_bad : mu.real bad <= badProbability
  value_lower : forall omega, omega ∉ bad ->
    Real.exp (-valueLoss) * BernoulliLinearAlgebra.gramVolume Q <=
      norm (packetTerminalValue Q z X omega)

/-- The exact upper interface from the two canonical conditional Cook calls
to `PacketTerminalGoodEventControl`.  The Cook input is an explicit theorem
parameter.  All sigma-field independence and both failure probabilities are
proved by `twoBalancedCook_probability_and_det`.

The last two hypotheses are the sole still-internal concrete matrix bridge:
the RRQR pivot/Gram-volume comparison and the CUR determinant identity after
reindexing the actual three-block residual.  They are not intended to remain
in the public Section 9 theorem. -/
noncomputable def packetTerminalGoodEventControl_of_twoBalancedCook
    {Omega w : Type u} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w]
    (cook : CookDeformedSquareInput.{u, u})
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    {W a b c e : Nat}
    (S : IidSubgaussianFamily Omega mu (ResidualFreshEntry a b c e W))
    (ha : a <= W) (hc : c <= W)
    (hs : a + b = c + e) (hsW : a + b <= 2 * W)
    (profile1 : CookProfile (balancedSquareSize W a b c))
    (profile2 : CookProfile
      (W + a + b - balancedSquareSize W a b c))
    (L1 L2 : Real)
    (deform1 : Omega -> Matrix (Fin (balancedSquareSize W a b c))
      (Fin (balancedSquareSize W a b c)) Complex)
    (deform2 : Omega ->
      Matrix (Fin (W + a + b - balancedSquareSize W a b c))
        (Fin (W + a + b - balancedSquareSize W a b c)) Complex)
    (cross12 : Omega ->
      Matrix (Fin (balancedSquareSize W a b c))
        (Fin (W + a + b - balancedSquareSize W a b c)) Complex)
    (cross21 : Omega ->
      Matrix (Fin (W + a + b - balancedSquareSize W a b c))
        (Fin (balancedSquareSize W a b c)) Complex)
    (bottom : Omega ->
      Matrix (Fin (W + a + b - balancedSquareSize W a b c))
        (Fin (W + a + b - balancedSquareSize W a b c)) Complex)
    (hsubgaussian : S.subgaussianParameter <= cook.subgaussianBound)
    (hprofile1 : forall i j,
      cook.lowerWeight <= profile1.weight i j ∧
        profile1.weight i j <= cook.upperWeight)
    (hprofile2 : forall i j,
      cook.lowerWeight <= profile2.weight i j ∧
        profile2.weight i j <= cook.upperWeight)
    (hn1 : 2 <= balancedSquareSize W a b c)
    (hn2 : 2 <= W + a + b - balancedSquareSize W a b c)
    (hL1 : 0 <= L1) (hL2 : 0 <= L2)
    (hdeform1Meas : forall i j,
      @StronglyMeasurable Omega Complex _
        (S.firstBalancedConditioningSigma ha hc hs hsW)
        (fun omega => deform1 omega i j))
    (hdeform2Meas : forall i j,
      @StronglyMeasurable Omega Complex _
        (S.secondBalancedConditioningSigma ha hc hs hsW)
        (fun omega => deform2 omega i j))
    (hdeform1Norm : ∀ᵐ omega ∂mu,
      norm (deform1 omega) <=
        (balancedSquareSize W a b c : Real) ^ L1)
    (hdeform2Norm : ∀ᵐ omega ∂mu,
      norm (deform2 omega) <=
        ((W + a + b - balancedSquareSize W a b c : Nat) : Real) ^ L2)
    (hsecond : forall omega,
      secondCookSchur
          (profiledMatrix (S.firstBalancedCookSquare ha hc hs hsW)
            profile1 omega + deform1 omega)
          (cross12 omega) (cross21 omega) (bottom omega) =
        profiledMatrix (S.secondBalancedCookSquare ha hc hs hsW)
          profile2 omega + deform2 omega)
    (valueLoss pivotLower : Real) (hpivotLower : 0 <= pivotLower)
    (hscale :
      Real.exp (-valueLoss) * BernoulliLinearAlgebra.gramVolume Q <=
        pivotLower *
          (((balancedSquareSize W a b c : Real) ^ (-cook.beta L1)) ^
              balancedSquareSize W a b c *
            (((W + a + b - balancedSquareSize W a b c : Nat) : Real) ^
              (-cook.beta L2)) ^
                (W + a + b - balancedSquareSize W a b c)))
    (hterminal : forall omega,
      pivotLower *
          norm ((Matrix.fromBlocks
            (profiledMatrix (S.firstBalancedCookSquare ha hc hs hsW)
                profile1 omega + deform1 omega)
            (cross12 omega) (cross21 omega) (bottom omega)).det) <=
        norm (packetTerminalValue Q z X omega)) :
    PacketTerminalGoodEventControl mu Q z X valueLoss
      (cookFailureBound (cook.cookC L1) (cook.cookc L1)
          (balancedSquareSize W a b c) +
        cookFailureBound (cook.cookC L2) (cook.cookc L2)
          (W + a + b - balancedSquareSize W a b c)) := by
  let bad := twoBalancedCookBadEvent cook S ha hc hs hsW
    profile1 profile2 L1 L2 deform1 deform2
  have hCook := twoBalancedCook_probability_and_det cook mu S ha hc hs hsW
    profile1 profile2 L1 L2 deform1 deform2 cross12 cross21 bottom
    hsubgaussian hprofile1 hprofile2 hn1 hn2 hL1 hL2 hdeform1Meas hdeform2Meas
    hdeform1Norm hdeform2Norm hsecond
  have hmeas1 := (cook.firstBalanced_conditional mu S ha hc hs hsW
    profile1 L1 deform1 hsubgaussian hprofile1 hn1 hL1 hdeform1Meas hdeform1Norm).1
  have hmeas2 := (cook.secondBalanced_conditional mu S ha hc hs hsW
    profile2 L2 deform2 hsubgaussian hprofile2 hn2 hL2 hdeform2Meas hdeform2Norm).1
  refine
    { bad := bad
      measurable_bad := ?_
      probability_bad := ?_
      value_lower := ?_ }
  · simpa [bad, twoBalancedCookBadEvent] using hmeas1.union hmeas2
  · simpa [bad] using hCook.1
  · intro omega homega
    have hresidual := hCook.2 omega (by simpa [bad] using homega)
    exact hscale.trans ((mul_le_mul_of_nonneg_left hresidual hpivotLower).trans
      (hterminal omega))

/-- Once the RRQR/CUR/two-Cook part supplies `PacketTerminalGoodEventControl`,
all four conclusions of Proposition 7.3 follow for the literal determinant.
The coefficient comparison and Parseval theorem are installed internally. -/
noncomputable def packetTerminalSmallBallConclusion_of_goodEventControl
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w] [LinearOrder w]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (valueLoss badProbability : Real)
    (hvalueLoss : 0 <= valueLoss)
    (control : PacketTerminalGoodEventControl mu Q z X
      valueLoss badProbability)
    (reverseEvent : Set Omega)
    (hreverse : ∀ omega, omega ∈ reverseEvent ->
      Real.posLog
        (norm (packetTerminalValue Q z X omega) /
          packetTerminalCoefficientNorm Q z) <=
        Real.log (BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
          (W := w) z) + valueLoss) :
    TerminalSmallBallConclusion mu (packetTerminalCoefficientNorm Q z)
      (packetTerminalValue Q z X)
      (Real.log (BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
        (W := w) z) + valueLoss)
      badProbability := by
  let K := BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
    (W := w) z
  let coefficientLoss := Real.log K
  have hKone : 1 <= K :=
    (BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket_concreteComparison
        (W := w) z).one_le
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hKone
  have hcoefficientLoss : 0 <= coefficientLoss := by
    exact Real.log_nonneg hKone
  have hcoeff : packetTerminalCoefficientNorm Q z <=
      Real.exp coefficientLoss * BernoulliLinearAlgebra.gramVolume Q := by
    rw [show Real.exp coefficientLoss = K by
      exact Real.exp_log hKpos]
    exact (packetTerminalCoefficientNorm_bounds Q z).2
  have hcapped : forall T : Real, 0 < T ->
      ∫ omega, cappedLogLoss T (packetTerminalCoefficientNorm Q z)
        (packetTerminalValue Q z X omega) ∂mu <=
        (coefficientLoss + valueLoss) + badProbability * T := by
    intro T hT
    exact integral_cappedLogLoss_le_of_common_product_bounds
      mu T (packetTerminalCoefficientNorm Q z)
      (BernoulliLinearAlgebra.gramVolume Q)
      coefficientLoss valueLoss badProbability
      (packetTerminalValue Q z X) control.bad hT.le
      hcoefficientLoss hvalueLoss
      (le_of_lt (packetTerminalCoefficientNorm_pos Q z))
      (BernoulliLinearAlgebra.gramVolume_pos Q)
      hcoeff control.measurable_bad
      (integrable_cappedLogLoss_packetTerminalValue mu Q z X T hT)
      control.probability_bad control.value_lower
  exact terminalSmallBallConclusion_of_capped
    mu (packetTerminalCoefficientNorm Q z) (packetTerminalValue Q z X)
    (coefficientLoss + valueLoss) badProbability
    (packetTerminalCoefficientNorm_pos Q z)
    (add_nonneg hcoefficientLoss hvalueLoss)
    (measurable_packetTerminalValue Q z X)
    (fun T hT => integrable_cappedLogLoss_packetTerminalValue
      mu Q z X T hT)
    hcapped reverseEvent (by
      simpa [coefficientLoss, K] using hreverse)
    (packetTerminal_parseval mu Q z X)

/-- A terminal conclusion with the quadratic reverse bound above.
Its reverse loss is weaker than the bound in `prop:local-terminal`, so it
is not exported as the paper's quantitative result. -/
noncomputable def packetTerminalSmallBallConclusion_with_quadraticReverseFallback
    {Omega w : Type*} [MeasurableSpace Omega]
    [Fintype w] [DecidableEq w] [LinearOrder w]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Q : Matrix (PacketOuter w) (PacketOuter w) Complex)
    (z : Complex)
    (X : IidSubgaussianFamily Omega mu
      (BernoulliLinearAlgebra.ThreeBlockVariable w))
    (valueLoss badProbability M : Real)
    (hvalueLoss : 0 <= valueLoss) (hM : 1 <= M)
    (control : PacketTerminalGoodEventControl mu Q z X
      valueLoss badProbability)
    (hreverseFactor :
      ((Fintype.card
          (Finset (BernoulliLinearAlgebra.ThreeBlockVariable w)) : Nat) : Real) *
        M ^ Fintype.card (BernoulliLinearAlgebra.ThreeBlockVariable w) <=
          Real.exp
            (Real.log
              (BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
                (W := w) z) + valueLoss)) :
    TerminalSmallBallConclusion mu (packetTerminalCoefficientNorm Q z)
      (packetTerminalValue Q z X)
      (Real.log (BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
        (W := w) z) + valueLoss)
      badProbability := by
  apply packetTerminalSmallBallConclusion_of_goodEventControl
    mu Q z X valueLoss badProbability hvalueLoss control
    (coordinatewiseBoundedEvent X M)
  exact packetTerminal_reverse_quadraticFallback
    Q z X M
      (Real.log
        (BernoulliLinearAlgebra.threeBlockConcreteComparisonConstant
          (W := w) z) + valueLoss)
    hM
    (add_nonneg
      (Real.log_nonneg
        (BernoulliLinearAlgebra.threeBlockTerminalCoefficientOnPacket_concreteComparison
            (W := w) z).one_le)
      hvalueLoss)
    hreverseFactor

end TerminalAssembly

end BernoulliSection9
