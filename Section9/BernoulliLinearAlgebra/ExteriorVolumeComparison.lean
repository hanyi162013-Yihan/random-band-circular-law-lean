import BernoulliLinearAlgebra.VolumeComparison
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Gram volume versus Frobenius compound growth

Lemma 7.8, equation (7.47), used with Section 9.5, compares

`det (I + Rᴴ R)¹⁄²`

with the largest exterior-power growth of `R`.  The paper uses operator norms
on exterior powers and obtains the dimension constant `2^(n/2)`.  Mathlib has
singular values for finite-dimensional linear maps, but currently provides no
theorem identifying the operator norm of the exterior-power map (or the
compound matrix) with the product of its largest singular values.

This file therefore records, with deliberately explicit names, the unconditional
Frobenius-compound analogue.  Equation (9.84) gives the exact identity

`gramVolume R² = ∑ k, ‖compound k R‖_F²`.

Consequently the largest Frobenius compound norm lies below the Gram volume,
and the Gram volume is at most `sqrt (n + 1)` times that maximum.  No
operator-norm statement is claimed here.
-/

open scoped BigOperators Matrix Matrix.Norms.Frobenius

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard

section FrobeniusMaximum

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- Maximum Frobenius norm among the compound matrices in the nonzero range
of exterior degrees `0, …, card ι`. -/
def maxCompoundFrobenius (R : Matrix ι ι ℂ) : ℝ :=
  (Finset.range (Fintype.card ι + 1)).sup'
    (by simp : (Finset.range (Fintype.card ι + 1)).Nonempty)
    (fun k ↦ ‖compound k R‖)

/-- Every compound degree occurring in the all-minor identity is bounded by
the maximum Frobenius compound norm. -/
theorem compound_frobenius_le_maxCompoundFrobenius
    (R : Matrix ι ι ℂ) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    ‖compound k R‖ ≤ maxCompoundFrobenius R := by
  unfold maxCompoundFrobenius
  exact Finset.le_sup' (f := fun q ↦ ‖compound q R‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/-- The maximum Frobenius compound norm is nonnegative. -/
theorem maxCompoundFrobenius_nonneg (R : Matrix ι ι ℂ) :
    0 ≤ maxCompoundFrobenius R := by
  exact (norm_nonneg (compound 0 R)).trans
    (compound_frobenius_le_maxCompoundFrobenius R (Nat.zero_le _))

/-- Each individual Frobenius compound norm is at most the Gram volume. -/
theorem compound_frobenius_le_gramVolume
    (R : Matrix ι ι ℂ) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    ‖compound k R‖ ≤ gramVolume R := by
  rw [← sq_le_sq₀ (norm_nonneg _) (gramVolume_nonneg R)]
  rw [gramVolume_sq, gramEnergy_eq_sum_compoundEnergyReal]
  change ‖compound k R‖ ^ 2 ≤
    ∑ q ∈ Finset.range (Fintype.card ι + 1), ‖compound q R‖ ^ 2
  exact Finset.single_le_sum
    (fun q _ ↦ sq_nonneg ‖compound q R‖)
    (by simpa [Nat.lt_succ_iff] using hk)

/-- Lower half of the Frobenius-compound comparison. -/
theorem maxCompoundFrobenius_le_gramVolume (R : Matrix ι ι ℂ) :
    maxCompoundFrobenius R ≤ gramVolume R := by
  unfold maxCompoundFrobenius
  rw [Finset.sup'_le_iff]
  intro k hk
  exact compound_frobenius_le_gramVolume R
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

/-- Energy-level upper estimate behind the Frobenius comparison. -/
theorem gramEnergy_le_card_succ_mul_maxCompoundFrobenius_sq
    (R : Matrix ι ι ℂ) :
    gramEnergy R ≤
      (Fintype.card ι + 1 : ℝ) * maxCompoundFrobenius R ^ 2 := by
  rw [gramEnergy_eq_sum_compoundEnergyReal]
  calc
    (∑ k ∈ Finset.range (Fintype.card ι + 1),
        compoundEnergyReal k R) ≤
        ∑ k ∈ Finset.range (Fintype.card ι + 1),
          maxCompoundFrobenius R ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      unfold compoundEnergyReal
      exact (sq_le_sq₀ (norm_nonneg _)
        (maxCompoundFrobenius_nonneg R)).2
        (compound_frobenius_le_maxCompoundFrobenius R
          (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    _ = (Fintype.card ι + 1 : ℝ) *
        maxCompoundFrobenius R ^ 2 := by
      simp [Finset.card_range, nsmul_eq_mul]

/-- Upper half of the unconditional Frobenius-compound comparison.  The
factor is the square root of the number of exterior degrees. -/
theorem gramVolume_le_sqrt_card_succ_mul_maxCompoundFrobenius
    (R : Matrix ι ι ℂ) :
    gramVolume R ≤
      Real.sqrt (Fintype.card ι + 1 : ℝ) * maxCompoundFrobenius R := by
  rw [← sq_le_sq₀ (gramVolume_nonneg R)
    (mul_nonneg (Real.sqrt_nonneg _) (maxCompoundFrobenius_nonneg R))]
  rw [gramVolume_sq, mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Fintype.card ι + 1)]
  exact gramEnergy_le_card_succ_mul_maxCompoundFrobenius_sq R

/-- Complete Frobenius-compound form of the local exterior-volume
comparison.  This theorem is unconditional and should not be confused with
the paper's operator-norm version with factor `2^(n/2)`. -/
theorem gramVolume_frobeniusCompound_two_sided (R : Matrix ι ι ℂ) :
    maxCompoundFrobenius R ≤ gramVolume R ∧
      gramVolume R ≤
        Real.sqrt (Fintype.card ι + 1 : ℝ) * maxCompoundFrobenius R :=
  ⟨maxCompoundFrobenius_le_gramVolume R,
    gramVolume_le_sqrt_card_succ_mul_maxCompoundFrobenius R⟩

end FrobeniusMaximum

end BernoulliLinearAlgebra
