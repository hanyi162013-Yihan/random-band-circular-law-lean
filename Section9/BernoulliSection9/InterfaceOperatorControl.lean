import BernoulliSection9.InterfaceControl
import BernoulliSection9.SubgaussianOperatorNorm

/-!
# Complete interface control

This file combines the Nguyen bottom-singular-value event with the operator-
norm event proved directly from the subgaussian MGF field of
`IidSubgaussianSquare`.  Thus the caller-facing package controls the upper and
lower normalized determinant and the normalized inverse without adding an
operator-norm theorem input.
-/

open scoped Matrix.Norms.L2Operator ENNReal NNReal

noncomputable section

namespace BernoulliSection9

open MeasureTheory ProbabilityTheory

universe u

/-- The single interface failure event: Nguyen's bottom-spectrum event union
the internally proved subgaussian operator-norm event. -/
def interfaceCombinedBadEvent
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {n : ℕ}
    (I : NguyenBottomSingularInput)
    (S : IidSubgaussianSquare Ω μ n) : Set Ω :=
  nguyenInterfaceBadEvent I S (nguyenInterfaceA I)
      (nguyenInterfaceEpsilon0 I) (nguyenInterfaceCutoff I n) ∪
    subgaussianOpNormBadEvent S

/-- A common exponential rate for the Nguyen and subgaussian-norm events. -/
def interfaceCombinedRate (I : NguyenBottomSingularInput) : ℝ :=
  min (nguyenInterfaceRate I / 2) 1

lemma interfaceCombinedRate_pos (I : NguyenBottomSingularInput) :
    0 < interfaceCombinedRate I := by
  exact lt_min (half_pos (nguyenInterfaceRate_pos I)) zero_lt_one

lemma interfaceCombinedRate_le_nguyenHalf (I : NguyenBottomSingularInput) :
    interfaceCombinedRate I ≤ nguyenInterfaceRate I / 2 :=
  min_le_left _ _

lemma interfaceCombinedRate_le_one (I : NguyenBottomSingularInput) :
    interfaceCombinedRate I ≤ 1 :=
  min_le_right _ _

/-- A large-`n` condition at the common rate already implies the condition
needed by the canonical Nguyen package. -/
lemma nguyen_probability_large_of_combined_large
    (I : NguyenBottomSingularInput) (n : ℕ)
    (hlarge : 32 ≤ interfaceCombinedRate I ^ 2 * (n : ℝ)) :
    32 ≤ nguyenInterfaceRate I ^ 2 * (n : ℝ) := by
  have hr0 : 0 ≤ interfaceCombinedRate I :=
    (interfaceCombinedRate_pos I).le
  have hq0 : 0 ≤ nguyenInterfaceRate I := (nguyenInterfaceRate_pos I).le
  have hrq : interfaceCombinedRate I ≤ nguyenInterfaceRate I := by
    calc
      interfaceCombinedRate I ≤ nguyenInterfaceRate I / 2 :=
        interfaceCombinedRate_le_nguyenHalf I
      _ ≤ nguyenInterfaceRate I := by linarith
  have hsquare : interfaceCombinedRate I ^ 2 ≤
      nguyenInterfaceRate I ^ 2 := by nlinarith
  exact hlarge.trans (mul_le_mul_of_nonneg_right hsquare (by positivity))

/-- The union of the two interface bad events has a genuine exponentially
small bound.  The only probabilistic input here is Nguyen's approved input;
the operator-norm estimate is derived from `S.subgaussian`. -/
theorem interfaceCombinedBadEvent_probability_exp
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ}
    (I : NguyenBottomSingularInput.{u, u})
    (S : IidSubgaussianSquare Ω μ n)
    (hS : S.subgaussianParameter ≤ I.subgaussianBound) (hn : 0 < n)
    (hcutoffLarge :
      1 ≤ nguyenInterfaceCutoffRho I ^ 2 * (n : ℝ))
    (hlarge : 32 ≤ interfaceCombinedRate I ^ 2 * (n : ℝ)) :
    μ.real (interfaceCombinedBadEvent I S) ≤
      Real.exp (-(interfaceCombinedRate I / 2) * (n : ℝ)) := by
  let q := interfaceCombinedRate I
  have hNguyen :=
    (nguyenInterfaceCanonicalDetInverseControl μ I S hS hn hcutoffLarge
      (nguyen_probability_large_of_combined_large I n hlarge)).1
  have hNorm := normalizedRawComplexMatrix_opNorm_tail S hn
  have hqpos : 0 < q := interfaceCombinedRate_pos I
  have hqNguyen : q ≤ nguyenInterfaceRate I / 2 :=
    interfaceCombinedRate_le_nguyenHalf I
  have hqOne : q ≤ 1 := interfaceCombinedRate_le_one I
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hNguyen' :
      μ.real
          (nguyenInterfaceBadEvent I S (nguyenInterfaceA I)
            (nguyenInterfaceEpsilon0 I) (nguyenInterfaceCutoff I n)) ≤
        Real.exp (-q * (n : ℝ)) := by
    refine hNguyen.trans (Real.exp_le_exp.mpr ?_)
    simpa only [neg_mul] using
      (neg_le_neg (mul_le_mul_of_nonneg_right hqNguyen hn0))
  have hNorm' : μ.real (subgaussianOpNormBadEvent S) ≤
      Real.exp (-q * (n : ℝ)) := by
    refine hNorm.trans (Real.exp_le_exp.mpr ?_)
    have hmul : q * (n : ℝ) ≤ 1 * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hqOne hn0
    norm_num at hmul ⊢
    exact hmul
  calc
    μ.real (interfaceCombinedBadEvent I S) ≤
        μ.real
            (nguyenInterfaceBadEvent I S (nguyenInterfaceA I)
              (nguyenInterfaceEpsilon0 I) (nguyenInterfaceCutoff I n)) +
          μ.real (subgaussianOpNormBadEvent S) := by
            exact measureReal_union_le _ _
    _ ≤ Real.exp (-q * (n : ℝ)) + Real.exp (-q * (n : ℝ)) :=
      add_le_add hNguyen' hNorm'
    _ = 2 * Real.exp (-q * (n : ℝ)) := by ring
    _ ≤ 2 * (n : ℝ) * Real.exp (-q * (n : ℝ)) := by
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hexp : 0 ≤ Real.exp (-q * (n : ℝ)) := (Real.exp_pos _).le
      nlinarith
    _ ≤ Real.exp (-(q / 2) * (n : ℝ)) :=
      two_mul_nat_exp_neg_le_exp_half q hqpos n hlarge
    _ = Real.exp (-(interfaceCombinedRate I / 2) * (n : ℝ)) := by rfl

/-- Complete canonical interface package.  Off one explicit exponentially
small event, the normalized iid square has bounded operator norm, determinant
between an exponential lower bound and the resulting Hadamard upper bound,
and exponentially bounded inverse norm. -/
theorem interfaceCanonicalDetUpperLowerInverseControl
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ}
    (I : NguyenBottomSingularInput.{u, u})
    (S : IidSubgaussianSquare Ω μ n)
    (hS : S.subgaussianParameter ≤ I.subgaussianBound) (hn : 0 < n)
    (hcutoffLarge :
      1 ≤ nguyenInterfaceCutoffRho I ^ 2 * (n : ℝ))
    (hlarge : 32 ≤ interfaceCombinedRate I ^ 2 * (n : ℝ)) :
    μ.real (interfaceCombinedBadEvent I S) ≤
        Real.exp (-(interfaceCombinedRate I / 2) * (n : ℝ)) ∧
      ∀ ω ∉ interfaceCombinedBadEvent I S,
        ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) •
            S.rawMatrix ω)‖ ≤ subgaussianOpNormConstant S ∧
        Real.exp
            (-nguyenInterfaceDetLoss I (nguyenInterfaceCutoffRho I) *
              (n : ℝ)) ≤
          ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) •
            S.rawMatrix ω).det‖ ∧
        ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) •
            S.rawMatrix ω).det‖ ≤ (subgaussianOpNormConstant S) ^ n ∧
        ‖((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) •
            S.rawMatrix ω)⁻¹‖ ≤
          Real.exp (nguyenInterfaceInvLoss I * (n : ℝ)) := by
  refine ⟨interfaceCombinedBadEvent_probability_exp μ I S hS hn
    hcutoffLarge hlarge, ?_⟩
  have hNguyenPackage :=
    nguyenInterfaceCanonicalDetInverseControl μ I S hS hn hcutoffLarge
      (nguyen_probability_large_of_combined_large I n hlarge)
  intro ω hgood
  have hsplit :
      ω ∉ nguyenInterfaceBadEvent I S (nguyenInterfaceA I)
          (nguyenInterfaceEpsilon0 I) (nguyenInterfaceCutoff I n) ∧
        ω ∉ subgaussianOpNormBadEvent S := by
    simpa [interfaceCombinedBadEvent] using hgood
  have hop := norm_invSqrtThreeN_raw_le_of_opNormGood S ω hn hsplit.2
  have hNguyen := hNguyenPackage.2 ω hsplit.1
  let A : Matrix (Fin n) (Fin n) ℂ :=
    ((((Real.sqrt (3 * (n : ℝ)))⁻¹ : ℝ) : ℂ) • S.rawMatrix ω)
  have hdetUpper : ‖A.det‖ ≤ (subgaussianOpNormConstant S) ^ n := by
    calc
      ‖A.det‖ ≤ ‖A‖ ^ n := norm_det_le_pow_norm A
      _ ≤ (subgaussianOpNormConstant S) ^ n := by
        exact pow_le_pow_left₀ (norm_nonneg A) hop n
  exact ⟨hop, hNguyen.1, hdetUpper, hNguyen.2⟩

end BernoulliSection9
