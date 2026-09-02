import BernoulliSection9.ExternalInputs
import BernoulliLinearAlgebra.CoefficientTranslation
import BernoulliLinearAlgebra.GlobalBoundarySquarefree
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-!
# Parseval for squarefree polynomials in independent variables

For a finite iid family of centered, variance-one real random variables, the
squarefree monomials are an orthonormal family in `L²`.  Consequently a
squarefree polynomial with complex coefficients has second moment equal to
the squared Euclidean norm of its coefficient vector.

No probability estimate is assumed here.  Independence, centering,
variance one, measurability and finite moments all come from
`IidSubgaussianFamily`.
-/

open scoped BigOperators ComplexConjugate ProbabilityTheory

noncomputable section

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory

/-- The squarefree monomial indexed by `S`. -/
def squarefreeMonomial {Ω ι : Type*} [MeasurableSpace Ω]
    (X : ι → Ω → ℝ) (S : Finset ι) (ω : Ω) : ℝ :=
  ∏ i ∈ S, X i ω

/-- Evaluation of a complex-coefficient squarefree polynomial at a real
family `X`. -/
def evalSquarefree {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (c : Finset ι → ℂ) (X : ι → Ω → ℝ) (ω : Ω) : ℂ :=
  ∑ S : Finset ι, c S * (squarefreeMonomial X S ω : ℂ)

/-- The coordinate factor whose full product is the product of two
squarefree monomials. -/
private def squarefreePairFactor {Ω ι : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] (X : ι → Ω → ℝ) (S T : Finset ι)
    (i : ι) (ω : Ω) : ℝ :=
  (if i ∈ S then X i ω else 1) * (if i ∈ T then X i ω else 1)

private theorem squarefreeMonomial_mul_eq_prod_pairFactor
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (X : ι → Ω → ℝ) (S T : Finset ι) (ω : Ω) :
    squarefreeMonomial X S ω * squarefreeMonomial X T ω =
      ∏ i : ι, squarefreePairFactor X S T i ω := by
  classical
  calc
    squarefreeMonomial X S ω * squarefreeMonomial X T ω =
        (∏ i : ι, if i ∈ S then X i ω else 1) *
          (∏ i : ι, if i ∈ T then X i ω else 1) := by
      simp [squarefreeMonomial]
    _ = ∏ i : ι, squarefreePairFactor X S T i ω := by
      rw [← Finset.prod_mul_distrib]
      rfl

/-- A finite product of mutually independent integrable real variables is
integrable.  This auxiliary lemma keeps the moment bookkeeping local. -/
private theorem integrable_finsetProd_of_iIndep
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [DecidableEq ι]
    (f : ι → Ω → ℝ) (hf_indep : iIndepFun f μ)
    (hf_meas : ∀ i, Measurable (f i))
    (hf_int : ∀ i, Integrable (f i) μ) (s : Finset ι) :
    Integrable (∏ i ∈ s, f i) μ := by
  letI : IsProbabilityMeasure μ := hf_indep.isProbabilityMeasure
  induction s using Finset.induction_on with
  | empty =>
      change Integrable (fun _ : Ω ↦ (1 : ℝ)) μ
      exact integrable_const (1 : ℝ)
  | @insert i s hi ih =>
      have h_ind :=
        (hf_indep.indepFun_finsetProd_of_notMem hf_meas hi).symm
      have h_mul := h_ind.integrable_mul (hf_int i) ih
      simpa [Finset.prod_insert hi, mul_comm] using h_mul

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [Fintype ι] [DecidableEq ι]

private theorem pairFactor_measurable
    (X : IidSubgaussianFamily Ω μ ι) (S T : Finset ι) (i : ι) :
    Measurable (squarefreePairFactor X.atom S T i) := by
  change Measurable (fun ω ↦
    (if i ∈ S then X.atom i ω else 1) *
      (if i ∈ T then X.atom i ω else 1))
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
  · simpa only [if_pos hiS, if_pos hiT] using
      (X.measurable_atom i).fun_mul (X.measurable_atom i)
  · simpa only [if_pos hiS, if_neg hiT, mul_one] using
      X.measurable_atom i
  · simpa only [if_neg hiS, if_pos hiT, one_mul] using
      X.measurable_atom i
  · simpa only [if_neg hiS, if_neg hiT, one_mul] using
      (measurable_const : Measurable (fun _ : Ω ↦ (1 : ℝ)))

private theorem pairFactor_independent
    (X : IidSubgaussianFamily Ω μ ι) (S T : Finset ι) :
    iIndepFun (squarefreePairFactor X.atom S T) μ := by
  let f : ι → ℝ → ℝ := fun i x ↦
    (if i ∈ S then x else 1) * (if i ∈ T then x else 1)
  have hf : ∀ i, Measurable (f i) := by
    intro i
    by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
    · dsimp [f]
      simp only [if_pos hiS, if_pos hiT]
      fun_prop
    · dsimp [f]
      simp only [if_pos hiS, if_neg hiT, mul_one]
      fun_prop
    · dsimp [f]
      simp only [if_neg hiS, if_pos hiT, one_mul]
      fun_prop
    · dsimp [f]
      simp only [if_neg hiS, if_neg hiT, one_mul]
      fun_prop
  change iIndepFun (fun i ↦ f i ∘ X.atom i) μ
  exact X.independent.comp f hf

private theorem pairFactor_integrable
    (X : IidSubgaussianFamily Ω μ ι) (S T : Finset ι) (i : ι) :
    Integrable (squarefreePairFactor X.atom S T i) μ := by
  change Integrable (fun ω ↦
    (if i ∈ S then X.atom i ω else 1) *
      (if i ∈ T then X.atom i ω else 1)) μ
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
  · have hmem : MemLp (X.atom i) 2 μ := by
      simpa using (X.subgaussian i).memLp 2
    have hsquare : Integrable (fun ω ↦ (X.atom i ω) ^ 2) μ :=
      (memLp_two_iff_integrable_sq
        (X.measurable_atom i).aestronglyMeasurable).mp hmem
    simpa [hiS, hiT, pow_two] using hsquare
  · simpa [hiS, hiT] using
      (X.subgaussian i).integrable
  · simpa [hiS, hiT] using
      (X.subgaussian i).integrable
  · letI : IsProbabilityMeasure μ := X.independent.isProbabilityMeasure
    simpa [hiS, hiT] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ)

private theorem integral_pairFactor
    [IsProbabilityMeasure μ]
    (X : IidSubgaussianFamily Ω μ ι) (S T : Finset ι) (i : ι) :
    ∫ ω, squarefreePairFactor X.atom S T i ω ∂μ =
      if (i ∈ S ↔ i ∈ T) then 1 else 0 := by
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
  · simp only [squarefreePairFactor, hiS, hiT, if_pos, true_iff]
    simpa [pow_two] using X.variance_one i
  · simp [squarefreePairFactor, hiS, hiT, X.centered i]
  · simp [squarefreePairFactor, hiS, hiT, X.centered i]
  · simp [squarefreePairFactor, hiS, hiT]

/-- Products of two distinct squarefree monomials are orthogonal; every
squarefree monomial has second moment one. -/
theorem integral_squarefreeMonomial_mul
    [IsProbabilityMeasure μ]
    (X : IidSubgaussianFamily Ω μ ι) (S T : Finset ι) :
    ∫ ω, squarefreeMonomial X.atom S ω * squarefreeMonomial X.atom T ω ∂μ =
      if S = T then 1 else 0 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall
    (squarefreeMonomial_mul_eq_prod_pairFactor X.atom S T))]
  rw [(pairFactor_independent X S T).integral_fun_prod_eq_prod_integral]
  · by_cases hST : S = T
    · subst T
      simp [integral_pairFactor]
    · have hex : ∃ i : ι, ¬(i ∈ S ↔ i ∈ T) := by
        by_contra h
        push_neg at h
        exact hST (Finset.ext h)
      obtain ⟨i, hi⟩ := hex
      rw [if_neg hST]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by
        rw [integral_pairFactor]
        simp [hi])
  · exact fun i ↦ (pairFactor_measurable X S T i).aestronglyMeasurable

/-- The product of any two squarefree monomials is integrable. -/
theorem integrable_squarefreeMonomial_mul
    (X : IidSubgaussianFamily Ω μ ι) (S T : Finset ι) :
    Integrable (fun ω ↦
      squarefreeMonomial X.atom S ω * squarefreeMonomial X.atom T ω) μ := by
  rw [show (fun ω ↦ squarefreeMonomial X.atom S ω *
      squarefreeMonomial X.atom T ω) =
      (fun ω ↦ ∏ i : ι, squarefreePairFactor X.atom S T i ω) by
    funext ω
    exact squarefreeMonomial_mul_eq_prod_pairFactor X.atom S T ω]
  have h := integrable_finsetProd_of_iIndep
      (squarefreePairFactor X.atom S T) (pairFactor_independent X S T)
      (pairFactor_measurable X S T) (pairFactor_integrable X S T) Finset.univ
  exact h.congr (Filter.Eventually.of_forall fun ω ↦ by
    simp only [Finset.prod_apply])

@[simp] theorem evalSquarefree_re
    (c : Finset ι → ℂ) (X : ι → Ω → ℝ) (ω : Ω) :
    (evalSquarefree c X ω).re =
      ∑ S : Finset ι, (c S).re * squarefreeMonomial X S ω := by
  simp [evalSquarefree]

@[simp] theorem evalSquarefree_im
    (c : Finset ι → ℂ) (X : ι → Ω → ℝ) (ω : Ω) :
    (evalSquarefree c X ω).im =
      ∑ S : Finset ι, (c S).im * squarefreeMonomial X S ω := by
  simp [evalSquarefree]

/-- Pointwise expansion of the squared modulus into the Gram sum of
squarefree monomials. -/
theorem norm_evalSquarefree_sq_eq_double_sum
    (c : Finset ι → ℂ) (X : ι → Ω → ℝ) (ω : Ω) :
    ‖evalSquarefree c X ω‖ ^ 2 =
      ∑ T : Finset ι, ∑ S : Finset ι,
        ((c S).re * (c T).re + (c S).im * (c T).im) *
          (squarefreeMonomial X S ω * squarefreeMonomial X T ω) := by
  rw [Complex.sq_norm, Complex.normSq_apply,
    evalSquarefree_re, evalSquarefree_im]
  simp only [Finset.sum_mul, Finset.mul_sum]
  ring_nf
  simp_rw [Finset.sum_add_distrib]
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro T _ <;>
    apply Finset.sum_congr rfl <;>
    intro S _ <;>
    ring

private theorem integrable_squarefreePairTerm
    (X : IidSubgaussianFamily Ω μ ι) (c : Finset ι → ℂ)
    (S T : Finset ι) :
    Integrable (fun ω ↦
      ((c S).re * (c T).re + (c S).im * (c T).im) *
        (squarefreeMonomial X.atom S ω *
          squarefreeMonomial X.atom T ω)) μ := by
  exact (integrable_squarefreeMonomial_mul X S T).const_mul _

/-- Parseval's identity for a finite squarefree polynomial with complex
coefficients evaluated on an iid centered variance-one real family. -/
theorem integral_norm_evalSquarefree_sq
    [IsProbabilityMeasure μ]
    (X : IidSubgaussianFamily Ω μ ι) (c : Finset ι → ℂ) :
    ∫ ω, ‖evalSquarefree c X.atom ω‖ ^ 2 ∂μ =
      ∑ S : Finset ι, ‖c S‖ ^ 2 := by
  calc
    ∫ ω, ‖evalSquarefree c X.atom ω‖ ^ 2 ∂μ =
        ∫ ω, ∑ T : Finset ι, ∑ S : Finset ι,
          ((c S).re * (c T).re + (c S).im * (c T).im) *
            (squarefreeMonomial X.atom S ω *
              squarefreeMonomial X.atom T ω) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦
        norm_evalSquarefree_sq_eq_double_sum c X.atom ω
    _ = ∑ T : Finset ι, ∑ S : Finset ι,
        ∫ ω,
          ((c S).re * (c T).re + (c S).im * (c T).im) *
            (squarefreeMonomial X.atom S ω *
              squarefreeMonomial X.atom T ω) ∂μ := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro T _
        rw [integral_finset_sum]
        exact fun S _ ↦ integrable_squarefreePairTerm X c S T
      · intro T _
        exact integrable_finsetSum Finset.univ fun S _ ↦
          integrable_squarefreePairTerm X c S T
    _ = ∑ S : Finset ι, ‖c S‖ ^ 2 := by
      simp_rw [integral_const_mul,
        integral_squarefreeMonomial_mul X]
      classical
      simp only [ite_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      apply Finset.sum_congr rfl
      intro S _
      rw [Complex.sq_norm, Complex.normSq_apply]

/-- Euclidean coefficient-vector form of squarefree Parseval. -/
theorem integral_norm_evalSquarefree_sq_eq_coeffNorm
    [IsProbabilityMeasure μ]
    (X : IidSubgaussianFamily Ω μ ι)
    (c : BernoulliLinearAlgebra.CoeffSpace ι) :
    ∫ ω, ‖evalSquarefree (fun S ↦ c S) X.atom ω‖ ^ 2 ∂μ = ‖c‖ ^ 2 := by
  rw [integral_norm_evalSquarefree_sq X]
  exact BernoulliLinearAlgebra.coeffEnergy_eq_norm_sq c

/-- Evaluating the polynomial reconstructed from a squarefree coefficient
vector agrees literally with `evalSquarefree`. -/
private theorem squarefreeExponent_prod_apply
    (S : Finset ι) (x : ι → ℂ) :
    (BernoulliLinearAlgebra.squarefreeExponent S).prod
        (fun i e ↦ x i ^ e) = ∏ i ∈ S, x i := by
  rw [Finsupp.prod_of_support_subset (s := S)]
  · simp [BernoulliLinearAlgebra.squarefreeExponent]
  · intro i hi
    simpa [BernoulliLinearAlgebra.squarefreeExponent] using hi
  · intro i hi
    exact pow_zero (x i)

theorem eval_squarefreePolynomial_eq_evalSquarefree
    (c : BernoulliLinearAlgebra.CoeffSpace ι) (x : ι → ℝ) :
    MvPolynomial.eval (fun i ↦ (x i : ℂ))
        (BernoulliLinearAlgebra.squarefreePolynomial c) =
      evalSquarefree (fun S ↦ c S) (fun i (_ : Unit) ↦ x i) () := by
  classical
  simp only [BernoulliLinearAlgebra.squarefreePolynomial,
    MvPolynomial.eval_sum, MvPolynomial.eval_monomial,
    evalSquarefree, squarefreeMonomial, Complex.ofReal_prod]
  apply Finset.sum_congr rfl
  intro S _
  rw [squarefreeExponent_prod_apply]

/-- The generic evaluator is exactly the evaluation of the stable
three-block determinant polynomial, not merely an abstract polynomial with
the same coefficient norm. -/
theorem eval_threeBlockDetPolynomial_eq_evalSquarefree
    {w : Type*} [Fintype w] [DecidableEq w]
    (Q : Matrix (BernoulliLinearAlgebra.ThreeBlockOuter w)
      (BernoulliLinearAlgebra.ThreeBlockOuter w) ℂ)
    (z : ℂ) (x : BernoulliLinearAlgebra.ThreeBlockVariable w → ℝ) :
    MvPolynomial.eval (fun i ↦ (x i : ℂ))
        (BernoulliLinearAlgebra.threeBlockDetPolynomial Q z) =
      evalSquarefree
        (fun S ↦ BernoulliLinearAlgebra.threeBlockDetCoeffVector Q z S)
        (fun i (_ : Unit) ↦ x i) () := by
  rw [← BernoulliLinearAlgebra.squarefreePolynomial_coefficients_eq
    (BernoulliLinearAlgebra.threeBlockDetPolynomial Q z)
    (BernoulliLinearAlgebra.hasSquarefreeSupport_threeBlockDetPolynomial Q z)]
  simpa only [BernoulliLinearAlgebra.threeBlockDetCoeffVector_apply,
    BernoulliLinearAlgebra.threeBlockDetCoefficient] using
    (eval_squarefreePolynomial_eq_evalSquarefree
      (WithLp.toLp 2 (fun S ↦
        (BernoulliLinearAlgebra.threeBlockDetPolynomial Q z).coeff
          (BernoulliLinearAlgebra.squarefreeExponent S))) x)

/-- Parseval for the literal three-block determinant polynomial from the
stable Section 9.1.3 development. -/
theorem integral_norm_eval_threeBlockDetPolynomial_sq
    {w : Type*} [Fintype w] [DecidableEq w]
    [IsProbabilityMeasure μ]
    (Q : Matrix (BernoulliLinearAlgebra.ThreeBlockOuter w)
      (BernoulliLinearAlgebra.ThreeBlockOuter w) ℂ)
    (z : ℂ)
    (X : IidSubgaussianFamily Ω μ
      (BernoulliLinearAlgebra.ThreeBlockVariable w)) :
    ∫ ω, ‖MvPolynomial.eval (fun i ↦ (X.atom i ω : ℂ))
        (BernoulliLinearAlgebra.threeBlockDetPolynomial Q z)‖ ^ 2 ∂μ =
      BernoulliLinearAlgebra.threeBlockDetCoefficientNorm Q z ^ 2 := by
  calc
    ∫ ω, ‖MvPolynomial.eval (fun i ↦ (X.atom i ω : ℂ))
        (BernoulliLinearAlgebra.threeBlockDetPolynomial Q z)‖ ^ 2 ∂μ =
        ∫ ω, ‖evalSquarefree
          (fun S ↦ BernoulliLinearAlgebra.threeBlockDetCoeffVector Q z S)
          X.atom ω‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ by
        have hv :
            MvPolynomial.eval (fun i ↦ (X.atom i ω : ℂ))
                (BernoulliLinearAlgebra.threeBlockDetPolynomial Q z) =
              evalSquarefree
                (fun S ↦ BernoulliLinearAlgebra.threeBlockDetCoeffVector Q z S)
                X.atom ω := by
          simpa [evalSquarefree, squarefreeMonomial] using
            (eval_threeBlockDetPolynomial_eq_evalSquarefree Q z
              (fun i ↦ X.atom i ω))
        exact congrArg (fun q : ℂ ↦ ‖q‖ ^ 2) hv
    _ = ‖BernoulliLinearAlgebra.threeBlockDetCoeffVector Q z‖ ^ 2 :=
      integral_norm_evalSquarefree_sq_eq_coeffNorm X
        (BernoulliLinearAlgebra.threeBlockDetCoeffVector Q z)
    _ = BernoulliLinearAlgebra.threeBlockDetCoefficientNorm Q z ^ 2 := rfl

/-- Matrix-determinant form of the same identity, using the stable literal
evaluation theorem for `threeBlockH`. -/
theorem integral_norm_threeBlockH_det_sq
    {w : Type*} [Fintype w] [DecidableEq w]
    [IsProbabilityMeasure μ]
    (Q : Matrix (BernoulliLinearAlgebra.ThreeBlockOuter w)
      (BernoulliLinearAlgebra.ThreeBlockOuter w) ℂ)
    (z : ℂ)
    (X : IidSubgaussianFamily Ω μ
      (BernoulliLinearAlgebra.ThreeBlockVariable w)) :
    ∫ ω, ‖(BernoulliLinearAlgebra.threeBlockH Q z
        (fun i ↦ (X.atom i ω : ℂ))).det‖ ^ 2 ∂μ =
      BernoulliLinearAlgebra.threeBlockDetCoefficientNorm Q z ^ 2 := by
  simpa only [BernoulliLinearAlgebra.eval_threeBlockDetPolynomial] using
    integral_norm_eval_threeBlockDetPolynomial_sq Q z X

end BernoulliSection9
