import BernoulliSection9.ArbitraryFrameSmallBall

/-!
# Final arbitrary-frame deduction

This module supplies the glue in the proof of the arbitrary-frame small-ball
theorem at the end of Section 9.2.  For a finite monomial basis it evaluates
the exterior coefficient tensors from `ArbitraryFrame`, proves pointwise
convergence of the normalized artificial polynomials, passes the terminal
capped estimate through the limit, and obtains the zero-probability estimate.

The only probabilistic upstream parameter is a family of
`TerminalSmallBallConclusion`s, one for each artificial relation.  It is
intended to be supplied internally by the coordinate-frame terminal theorem
in `Section9Results`; it is not an elimination, mask, RRQR, or frame-completion
certificate.  In particular, the caller supplies arbitrary complex frames
`U,V`, while their unitary completions remain hidden inside `ArbitraryFrame`.
-/

open scoped BigOperators Matrix ComplexConjugate Real

noncomputable section

namespace BernoulliSection9

open Filter Matrix MeasureTheory Set Set.powersetCard

/-- The Euclidean coefficient norm of the normalized artificial polynomial
at the cofinal parameter `lambda_q = q + 1`. -/
def normalizedArtificialCoefficientNorm {a : Type*} [Fintype a]
    {n r : ℕ} (U V : ComplexFrame r n) (h : r ≤ n)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ)
    (q : ℕ) : ℝ :=
  ‖(WithLp.toLp 2
    (fun b => normalizedExteriorCoefficient U V h Q q b) :
      EuclideanSpace ℂ a)‖

/-- The Euclidean coefficient norm `Gamma_(U,V)^(r)` of the limiting
arbitrary-frame polynomial. -/
def frameCoefficientNorm {a : Type*} [Fintype a]
    {n r : ℕ} (U V : ComplexFrame r n) (h : r ≤ n)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ) : ℝ :=
  ‖(WithLp.toLp 2
    (fun b => limitingFrameCoefficient U V h Q b) :
      EuclideanSpace ℂ a)‖

/-- Equation (9.55), restated using the named coefficient norms used by the
deduction theorem. -/
theorem normalizedArtificialCoefficientNorm_tendsto
    {a : Type*} [Fintype a] {n r : ℕ}
    (U V : ComplexFrame r n) (h : r ≤ n)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ) :
    Tendsto (normalizedArtificialCoefficientNorm U V h Q)
      atTop (nhds (frameCoefficientNorm U V h Q)) := by
  exact normalizedExteriorCoefficientNorm_tendsto U V h Q

/-- Evaluate the normalized artificial exterior polynomial in a finite
monomial family. -/
def normalizedArtificialPolynomialValue
    {Ω a : Type*} [Fintype a] {n r : ℕ}
    (U V : ComplexFrame r n) (h : r ≤ n)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ)
    (atom : a → Ω → ℂ) (q : ℕ) (ω : Ω) : ℂ :=
  ∑ b, normalizedExteriorCoefficient U V h Q q b * atom b ω

/-- Evaluate the limiting arbitrary-frame polynomial in the same monomial
family. -/
def framePolynomialValue
    {Ω a : Type*} [Fintype a] {n r : ℕ}
    (U V : ComplexFrame r n) (h : r ≤ n)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ)
    (atom : a → Ω → ℂ) (ω : Ω) : ℂ :=
  ∑ b, limitingFrameCoefficient U V h Q b * atom b ω

/-- Equation (9.53), evaluated at an arbitrary point `ω`.  Finiteness of the
monomial basis turns coefficientwise convergence into pointwise polynomial
convergence. -/
theorem normalizedArtificialPolynomialValue_tendsto
    {Ω a : Type*} [Fintype a] {n r : ℕ}
    (U V : ComplexFrame r n) (h : r ≤ n)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ)
    (atom : a → Ω → ℂ) (ω : Ω) :
    Tendsto
      (fun q => normalizedArtificialPolynomialValue U V h Q atom q ω)
      atTop (nhds (framePolynomialValue U V h Q atom ω)) := by
  unfold normalizedArtificialPolynomialValue framePolynomialValue
  apply tendsto_finset_sum Finset.univ
  intro b _
  exact (normalizedExteriorCoefficient_tendsto U V h Q b).mul_const
    (atom b ω)

theorem normalizedArtificialPolynomialValue_measurable
    {Ω a : Type*} [MeasurableSpace Ω] [Fintype a] {n r : ℕ}
    (U V : ComplexFrame r n) (h : r ≤ n)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ)
    (atom : a → Ω → ℂ) (hatom : ∀ b, Measurable (atom b)) (q : ℕ) :
    Measurable (normalizedArtificialPolynomialValue U V h Q atom q) := by
  unfold normalizedArtificialPolynomialValue
  apply Finset.measurable_fun_sum
  intro b _
  exact (hatom b).const_mul _

theorem framePolynomialValue_measurable
    {Ω a : Type*} [MeasurableSpace Ω] [Fintype a] {n r : ℕ}
    (U V : ComplexFrame r n) (h : r ≤ n)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard (Fin n) k) (powersetCard (Fin n) k) ℂ)
    (atom : a → Ω → ℂ) (hatom : ∀ b, Measurable (atom b)) :
    Measurable (framePolynomialValue U V h Q atom) := by
  unfold framePolynomialValue
  apply Finset.measurable_fun_sum
  intro b _
  exact (hatom b).const_mul _

/-- The capped integral dominates `T` times the mass of the zero set.  This
provides the measure-theoretic link between the limiting capped estimate
and the zero-probability conclusion. -/
theorem cap_mul_zeroProbability_le_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (T c : ℝ) (hT : 0 ≤ T) (hc : 0 < c)
    (value : Ω → ℂ) (hvalue : Measurable value) :
    T * μ.real {ω | value ω = 0} ≤
      ∫ ω, cappedLogLoss T c (value ω) ∂μ := by
  let zeroSet : Set Ω := {ω | value ω = 0}
  let indicator : Ω → ℝ := zeroSet.indicator (fun _ => T)
  have hzero : MeasurableSet zeroSet := by
    exact hvalue (measurableSet_singleton 0)
  have hind : Integrable indicator μ := by
    exact (integrable_const T).indicator hzero
  have hlossMeas : AEStronglyMeasurable
      (fun ω => cappedLogLoss T c (value ω)) μ :=
    aestronglyMeasurable_cappedLogLoss μ T c value hc
      hvalue.aestronglyMeasurable
  have hloss : Integrable (fun ω => cappedLogLoss T c (value ω)) μ := by
    apply Integrable.of_bound hlossMeas T
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,
      abs_of_nonneg (cappedLogLoss_nonneg hT)]
    exact cappedLogLoss_le_cap
  have hpoint : ∀ ω, indicator ω ≤ cappedLogLoss T c (value ω) := by
    intro ω
    by_cases hω : value ω = 0
    · simp [indicator, zeroSet, hω]
    · simp [indicator, zeroSet, hω, cappedLogLoss_nonneg hT]
  calc
    T * μ.real {ω | value ω = 0} = ∫ ω, indicator ω ∂μ := by
      rw [show {ω | value ω = 0} = zeroSet from rfl]
      rw [show (∫ ω, indicator ω ∂μ) = μ.real zeroSet * T by
        simpa [indicator] using
          (MeasureTheory.integral_indicator_const (μ := μ) T hzero)]
      ring
    _ ≤ ∫ ω, cappedLogLoss T c (value ω) ∂μ :=
      integral_mono hind hloss hpoint

/-- Caller-ready output of the Section 9.2 limiting argument.  Besides the
final estimates, it records both limits used to obtain them, making the
coefficient-norm trust boundary explicit. -/
structure ArbitraryFrameDeductionConclusion
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (artificialCoefficientNorm : ℕ → ℝ) (coefficientNorm : ℝ)
    (artificialValue : ℕ → Ω → ℂ) (value : Ω → ℂ)
    (lower upper baseLoss badProbability : ℝ) where
  coefficientNorm_limit :
    Tendsto artificialCoefficientNorm atTop (nhds coefficientNorm)
  value_limit : ∀ ω,
    Tendsto (fun q => artificialValue q ω) atTop (nhds (value ω))
  coefficientNorm_pos : 0 < coefficientNorm
  coefficientNorm_bounds : lower ≤ coefficientNorm ∧ coefficientNorm ≤ upper
  capped : ∀ T : ℝ, 0 < T →
    ∫ ω, cappedLogLoss T coefficientNorm (value ω) ∂μ ≤
      baseLoss + badProbability * T
  zero_probability : μ.real {ω | value ω = 0} ≤ badProbability

/-- Final deduction of the arbitrary-frame coefficient and small-ball
estimates.  The normalized graph factor is the exact expression from (9.54),
and its limit removes the artificial parameter.  No unitary-completion or
RRQR data appears in the signature. -/
theorem arbitraryFrame_smallBall_deduction
    {Ω a : Type*} [MeasurableSpace Ω] [Fintype a]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {W r : ℕ} (U V : ComplexFrame r (2 * W)) (h : r ≤ 2 * W)
    (Q : (k : ℕ) → a →
      Matrix (powersetCard (Fin (2 * W)) k)
        (powersetCard (Fin (2 * W)) k) ℂ)
    (atom : a → Ω → ℂ)
    (lower upper baseLoss badProbability : ℝ)
    (hlowerPos : 0 < lower) (hbase : 0 ≤ baseLoss)
    (hatom : ∀ b, Measurable (atom b))
    (hlower : ∀ q,
      lower * normalizedGraphProduct W q ≤
        normalizedArtificialCoefficientNorm U V h Q q)
    (hupper : ∀ q,
      normalizedArtificialCoefficientNorm U V h Q q ≤
        upper * normalizedGraphProduct W q)
    (terminal : ∀ q,
      TerminalSmallBallConclusion μ
        (normalizedArtificialCoefficientNorm U V h Q q)
        (normalizedArtificialPolynomialValue U V h Q atom q)
        baseLoss badProbability) :
    ArbitraryFrameDeductionConclusion μ
      (normalizedArtificialCoefficientNorm U V h Q)
      (frameCoefficientNorm U V h Q)
      (normalizedArtificialPolynomialValue U V h Q atom)
      (framePolynomialValue U V h Q atom)
      lower upper baseLoss badProbability := by
  have hnorm : Tendsto
      (normalizedArtificialCoefficientNorm U V h Q) atTop
      (nhds (frameCoefficientNorm U V h Q)) :=
    normalizedArtificialCoefficientNorm_tendsto U V h Q
  have hvalue : ∀ ω, Tendsto
      (fun q => normalizedArtificialPolynomialValue U V h Q atom q ω)
      atTop (nhds (framePolynomialValue U V h Q atom ω)) :=
    fun ω => normalizedArtificialPolynomialValue_tendsto U V h Q atom ω
  have hbounds : lower ≤ frameCoefficientNorm U V h Q ∧
      frameCoefficientNorm U V h Q ≤ upper :=
    limit_mem_interval_of_scaled_bounds hnorm
      (normalizedGraphProduct_tendsto W) hlower hupper
  have hnormPos : 0 < frameCoefficientNorm U V h Q :=
    hlowerPos.trans_le hbounds.1
  have hseqMeas : ∀ q, AEStronglyMeasurable
      (normalizedArtificialPolynomialValue U V h Q atom q) μ :=
    fun q => (normalizedArtificialPolynomialValue_measurable
      U V h Q atom hatom q).aestronglyMeasurable
  have hframeMeas : Measurable (framePolynomialValue U V h Q atom) :=
    framePolynomialValue_measurable U V h Q atom hatom
  have hcapped : ∀ T : ℝ, 0 < T →
      ∫ ω, cappedLogLoss T (frameCoefficientNorm U V h Q)
          (framePolynomialValue U V h Q atom ω) ∂μ ≤
        baseLoss + badProbability * T := by
    intro T hT
    exact cappedIntegral_limit_le_of_uniform_bound μ T hT.le hnorm hnormPos
      (fun q => (terminal q).coefficientNorm_pos) hseqMeas
      (Filter.Eventually.of_forall hvalue)
      (baseLoss + badProbability * T) (fun q => (terminal q).capped T hT)
  have hzero : μ.real
      {ω | framePolynomialValue U V h Q atom ω = 0} ≤ badProbability := by
    apply zeroProbability_of_all_capped_bounds hbase
    intro T hT
    exact (cap_mul_zeroProbability_le_integral μ T
      (frameCoefficientNorm U V h Q) hT.le hnormPos
      (framePolynomialValue U V h Q atom) hframeMeas).trans
        (hcapped T hT)
  exact
    { coefficientNorm_limit := hnorm
      value_limit := hvalue
      coefficientNorm_pos := hnormPos
      coefficientNorm_bounds := hbounds
      capped := hcapped
      zero_probability := hzero }

end BernoulliSection9
