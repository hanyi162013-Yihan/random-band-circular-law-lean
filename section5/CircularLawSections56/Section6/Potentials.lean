import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite logarithmic potentials and the circular-law target

This file isolates the scalar potential bookkeeping used in Section 6.  It has no
dependency on the other project modules: a finite family `singularValues : Fin n → ℝ`
stands for the singular values of a shifted matrix.

Both finite potentials use Lean's totalized field operations.  In particular, when
`n = 0`, the sum over `Fin 0` is zero and the displayed average is `0 / 0 = 0`.
All comparison results with their usual analytic meaning therefore either assume
`0 < n` or explicitly handle this empty case.
-/

open scoped BigOperators

namespace CircularLawSections56.Section6

section FinitePotentials

/-- The normalized raw logarithmic potential of a finite singular-value family.

For `n = 0` this is definitionally a totalized empty average, hence equals zero.
For matrix applications the entries are positive singular values, so `Real.log`
agrees with the ordinary finite logarithm. -/
noncomputable def rawLogPotential {n : ℕ}
    (singularValues : Fin n → ℝ) : ℝ :=
  (∑ i, Real.log (singularValues i)) / (n : ℝ)

/-- The normalized logarithmic potential after replacing every singular value `s`
by `max s cutoff`.

For `n = 0` this uses the same totalized convention as `rawLogPotential` and is zero.
-/
noncomputable def truncatedLogPotential {n : ℕ}
    (singularValues : Fin n → ℝ) (cutoff : ℝ) : ℝ :=
  (∑ i, Real.log (max (singularValues i) cutoff)) / (n : ℝ)

@[simp]
theorem rawLogPotential_fin_zero
    (singularValues : Fin 0 → ℝ) :
    rawLogPotential singularValues = 0 := by
  simp [rawLogPotential]

@[simp]
theorem truncatedLogPotential_fin_zero
    (singularValues : Fin 0 → ℝ) (cutoff : ℝ) :
    truncatedLogPotential singularValues cutoff = 0 := by
  simp [truncatedLogPotential]

/-- Truncation can only increase the logarithmic potential of a nonempty family of
positive singular values.  The statement is slightly stronger than the usual cutoff
form because the comparison holds for every real cutoff. -/
theorem rawLogPotential_le_truncatedLogPotential_any_cutoff
    {n : ℕ} (hn : 0 < n) (singularValues : Fin n → ℝ)
    (hPositive : ∀ i, 0 < singularValues i) (cutoff : ℝ) :
    rawLogPotential singularValues ≤
      truncatedLogPotential singularValues cutoff := by
  unfold rawLogPotential truncatedLogPotential
  have hnReal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  apply (div_le_div_iff_of_pos_right hnReal).2
  apply Finset.sum_le_sum
  intro i hi
  exact Real.log_le_log (hPositive i) (le_max_left _ _)

/-- The standard nonnegative-cutoff form of
`rawLogPotential_le_truncatedLogPotential_any_cutoff`. -/
theorem rawLogPotential_le_truncatedLogPotential
    {n : ℕ} (hn : 0 < n) (singularValues : Fin n → ℝ)
    (hPositive : ∀ i, 0 < singularValues i) {cutoff : ℝ}
    (_hCutoff : 0 ≤ cutoff) :
    rawLogPotential singularValues ≤
      truncatedLogPotential singularValues cutoff :=
  rawLogPotential_le_truncatedLogPotential_any_cutoff
    hn singularValues hPositive cutoff

/-- The cutoff error is exactly the normalized sum of its pointwise logarithmic
increments.  This algebraic identity is valid also at `n = 0`, using the totalized
convention documented above. -/
theorem truncatedLogPotential_sub_rawLogPotential
    {n : ℕ} (singularValues : Fin n → ℝ) (cutoff : ℝ) :
    truncatedLogPotential singularValues cutoff -
        rawLogPotential singularValues =
      (∑ i, (Real.log (max (singularValues i) cutoff) -
        Real.log (singularValues i))) / (n : ℝ) := by
  simp only [rawLogPotential, truncatedLogPotential,
    Finset.sum_sub_distrib, sub_div]

/-- Increasing the cutoff increases the truncated logarithmic potential whenever
the singular values are positive.  This includes `n = 0`, where both sides are zero.
-/
theorem truncatedLogPotential_mono_cutoff
    {n : ℕ} (singularValues : Fin n → ℝ)
    (hPositive : ∀ i, 0 < singularValues i) {cutoff₁ cutoff₂ : ℝ}
    (hCutoff : cutoff₁ ≤ cutoff₂) :
    truncatedLogPotential singularValues cutoff₁ ≤
      truncatedLogPotential singularValues cutoff₂ := by
  unfold truncatedLogPotential
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro i hi
  have hMaxPositive : 0 < max (singularValues i) cutoff₁ :=
    (hPositive i).trans_le (le_max_left _ _)
  exact Real.log_le_log hMaxPositive (max_le_max le_rfl hCutoff)

end FinitePotentials

section CircularTargets

/-- The circular-law logarithmic potential as a scalar function of the radius:
`U_cir(r) = (r² - 1) / 2` inside the unit disk and `log r` outside.

The intended input is a norm and is therefore nonnegative.  Keeping the definition on
all of `ℝ` makes it convenient to compose with any radial observable. -/
noncomputable def circularRadialPotential (radius : ℝ) : ℝ :=
  if radius ≤ 1 then (radius ^ 2 - 1) / 2 else Real.log radius

/-- The variance-`v` radial target
`U_v(r) = (1 / 2) log v + U_cir(r / sqrt v)`.

Its probabilistic interpretation assumes `0 < v`; as a scalar Lean definition it is
totalized for every real `v`. -/
noncomputable def varianceScaledRadialPotential
    (variance radius : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log variance +
    circularRadialPotential (radius / Real.sqrt variance)

theorem circularRadialPotential_of_le_one
    {radius : ℝ} (hRadius : radius ≤ 1) :
    circularRadialPotential radius = (radius ^ 2 - 1) / 2 := by
  simp [circularRadialPotential, hRadius]

theorem circularRadialPotential_of_one_lt
    {radius : ℝ} (hRadius : 1 < radius) :
    circularRadialPotential radius = Real.log radius := by
  simp [circularRadialPotential, not_le_of_gt hRadius]

@[simp]
theorem varianceScaledRadialPotential_one (radius : ℝ) :
    varianceScaledRadialPotential 1 radius =
      circularRadialPotential radius := by
  simp [varianceScaledRadialPotential]

end CircularTargets

end CircularLawSections56.Section6
