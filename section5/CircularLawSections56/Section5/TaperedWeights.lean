import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic

/-!
# Discrete normalization of tapered weights

This file isolates the deterministic finite-set layer of `cor:tapered-indicator` in
Section 5.  A nonnegative raw tapered weight is normalized by its mass on the active
set.  Bounds for the raw weight and for that mass then give the normalized bounds in
`eq:tapered-discrete-bounds`.

The bounded-variation construction, the tapered anchor from Section 3, and the
projective wrappers from Section 4 remain ordinary upstream inputs: they are used only
to establish the real inequalities accepted by the theorems below.  The final product
estimate records the isolated-weight loss for any selected monomial.
-/

open scoped BigOperators

namespace CircularLawSections56.Section5

variable {ι : Type*}

/-- Total raw tapered mass on the finite active set. -/
noncomputable def taperedNormalizer
    (active : Finset ι) (rawWeight : ι → ℝ) : ℝ :=
  ∑ i ∈ active, rawWeight i

/-- Raw tapered weight divided by its mass on the active set. -/
noncomputable def taperedNormalizedWeight
    (active : Finset ι) (rawWeight : ι → ℝ) (i : ι) : ℝ :=
  rawWeight i / taperedNormalizer active rawWeight

/-- Nonnegative raw weights have nonnegative total mass. -/
theorem taperedNormalizer_nonneg
    (active : Finset ι) (rawWeight : ι → ℝ)
    (hRawNonneg : ∀ i ∈ active, 0 ≤ rawWeight i) :
    0 ≤ taperedNormalizer active rawWeight := by
  unfold taperedNormalizer
  exact Finset.sum_nonneg hRawNonneg

/-- Transport raw and normalizer bounds to normalized tapered-weight bounds.

This is the purely algebraic content of `eq:tapered-discrete-bounds`.  Positivity of the
lower normalizer bound makes every division legitimate.  Nonnegativity of the raw
endpoint bounds is exactly what is needed when replacing the true normalizer by its
upper or lower comparison value. -/
theorem taperedNormalizedWeight_bounds
    (active : Finset ι) (rawWeight : ι → ℝ)
    (rawLower rawUpper normalizerLower normalizerUpper : ℝ)
    (hRawLowerNonneg : 0 ≤ rawLower)
    (hRawUpperNonneg : 0 ≤ rawUpper)
    (hNormalizerLowerPos : 0 < normalizerLower)
    (hNormalizerLower :
      normalizerLower ≤ taperedNormalizer active rawWeight)
    (hNormalizerUpper :
      taperedNormalizer active rawWeight ≤ normalizerUpper)
    (hRawBounds : ∀ i ∈ active,
      rawLower ≤ rawWeight i ∧ rawWeight i ≤ rawUpper) :
    ∀ i ∈ active,
      rawLower / normalizerUpper ≤
          taperedNormalizedWeight active rawWeight i ∧
        taperedNormalizedWeight active rawWeight i ≤
          rawUpper / normalizerLower := by
  intro i hi
  have hNormalizerPos : 0 < taperedNormalizer active rawWeight :=
    hNormalizerLowerPos.trans_le hNormalizerLower
  have hNormalizerUpperPos : 0 < normalizerUpper :=
    hNormalizerPos.trans_le hNormalizerUpper
  constructor
  · unfold taperedNormalizedWeight
    apply (le_div_iff₀ hNormalizerPos).2
    calc
      (rawLower / normalizerUpper) * taperedNormalizer active rawWeight ≤
          (rawLower / normalizerUpper) * normalizerUpper :=
        mul_le_mul_of_nonneg_left hNormalizerUpper
          (div_nonneg hRawLowerNonneg hNormalizerUpperPos.le)
      _ = rawLower := div_mul_cancel₀ rawLower hNormalizerUpperPos.ne'
      _ ≤ rawWeight i := (hRawBounds i hi).1
  · unfold taperedNormalizedWeight
    apply (div_le_iff₀ hNormalizerPos).2
    calc
      rawWeight i ≤ rawUpper := (hRawBounds i hi).2
      _ = (rawUpper / normalizerLower) * normalizerLower :=
        (div_mul_cancel₀ rawUpper hNormalizerLowerPos.ne').symm
      _ ≤ (rawUpper / normalizerLower) *
          taperedNormalizer active rawWeight :=
        mul_le_mul_of_nonneg_left hNormalizerLower
          (div_nonneg hRawUpperNonneg hNormalizerLowerPos.le)

/-- Normalized tapered weights have total mass one whenever the raw total mass is
positive. -/
theorem sum_taperedNormalizedWeight_eq_one
    (active : Finset ι) (rawWeight : ι → ℝ)
    (hNormalizerPos : 0 < taperedNormalizer active rawWeight) :
    (∑ i ∈ active, taperedNormalizedWeight active rawWeight i) = 1 := by
  simp only [taperedNormalizedWeight]
  rw [← Finset.sum_div]
  simp only [taperedNormalizer]
  exact div_self hNormalizerPos.ne'

/-- A uniform lower bound on selected factors gives the corresponding monomial bound.

The exponent is exactly the number of selected indices, so this theorem makes the
isolated-weight loss explicit and independent of how the selected set was produced. -/
theorem selected_product_ge_edgeLower_pow_card
    (selected : Finset ι) (weight : ι → ℝ) (edgeLower : ℝ)
    (hEdgeLowerNonneg : 0 ≤ edgeLower)
    (hEach : ∀ i ∈ selected, edgeLower ≤ weight i) :
    edgeLower ^ selected.card ≤ ∏ i ∈ selected, weight i := by
  calc
    edgeLower ^ selected.card = ∏ _i ∈ selected, edgeLower := by simp
    _ ≤ ∏ i ∈ selected, weight i := by
      apply Finset.prod_le_prod
      · intro i hi
        exact hEdgeLowerNonneg
      · intro i hi
        exact hEach i hi

/-- Product form of `eq:tapered-discrete-bounds` for a selected family.

Every selected index must lie in the active set.  The raw lower bound and normalizer
upper bound then yield a common normalized edge bound, whose `selected.card`-th power is
the explicit isolated-monomial lower bound. -/
theorem selected_taperedNormalizedWeight_product_lower_bound
    (active selected : Finset ι) (rawWeight : ι → ℝ)
    (rawLower rawUpper normalizerLower normalizerUpper : ℝ)
    (hSelected : selected ⊆ active)
    (hRawLowerNonneg : 0 ≤ rawLower)
    (hRawUpperNonneg : 0 ≤ rawUpper)
    (hNormalizerLowerPos : 0 < normalizerLower)
    (hNormalizerLower :
      normalizerLower ≤ taperedNormalizer active rawWeight)
    (hNormalizerUpper :
      taperedNormalizer active rawWeight ≤ normalizerUpper)
    (hRawBounds : ∀ i ∈ active,
      rawLower ≤ rawWeight i ∧ rawWeight i ≤ rawUpper) :
    (rawLower / normalizerUpper) ^ selected.card ≤
      ∏ i ∈ selected, taperedNormalizedWeight active rawWeight i := by
  have hNormalizerPos : 0 < taperedNormalizer active rawWeight :=
    hNormalizerLowerPos.trans_le hNormalizerLower
  have hNormalizerUpperPos : 0 < normalizerUpper :=
    hNormalizerPos.trans_le hNormalizerUpper
  apply selected_product_ge_edgeLower_pow_card
  · exact div_nonneg hRawLowerNonneg hNormalizerUpperPos.le
  · intro i hi
    exact (taperedNormalizedWeight_bounds active rawWeight
      rawLower rawUpper normalizerLower normalizerUpper
      hRawLowerNonneg hRawUpperNonneg hNormalizerLowerPos
      hNormalizerLower hNormalizerUpper hRawBounds i (hSelected hi)).1

end CircularLawSections56.Section5
