import BernoulliLinearAlgebra.ExteriorVolumeComparison
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Nat.Choose.Sum

/-!
# Gram volume versus operator norms of compound matrices

This file proves Lemma 7.8, equation (7.47), the operator-norm form of the
exterior-volume comparison used with Section 9.5. The operator norm is the
Euclidean (`L²`) norm, expressed through
`Matrix.toEuclideanCLM`; keeping it as an explicit definition avoids ambiguity
with mathlib's several scoped matrix norm instances.
-/

open scoped BigOperators Matrix

noncomputable section

namespace BernoulliLinearAlgebra

open Matrix Set Set.powersetCard

section MatrixOperatorNorm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Euclidean operator norm of a square complex matrix. -/
def matrixL2OperatorNorm (A : Matrix n n ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖

/-- The squared Hilbert--Schmidt energy is at most the number of columns
times the squared Euclidean operator norm. -/
theorem sum_normSq_le_card_mul_matrixL2OperatorNorm_sq
    (A : Matrix n n ℂ) :
    (∑ i, ∑ j, Complex.normSq (A i j)) ≤
      (Fintype.card n : ℝ) * matrixL2OperatorNorm A ^ 2 := by
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ i, Complex.normSq (A i j)) =
        ∑ j, ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
          (WithLp.toLp 2 (Pi.single j 1))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single_one,
        EuclideanSpace.norm_sq_eq]
      simp [Complex.sq_norm]
    _ ≤ ∑ _j : n, matrixL2OperatorNorm A ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 <| by
        simpa [matrixL2OperatorNorm] using
          (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm
            (WithLp.toLp 2 (Pi.single j 1))
    _ = (Fintype.card n : ℝ) * matrixL2OperatorNorm A ^ 2 := by
      simp [nsmul_eq_mul]

/-- The Euclidean operator norm is bounded by the Hilbert--Schmidt norm,
written here without selecting a second matrix norm instance. -/
theorem matrixL2OperatorNorm_le_sqrt_sum_normSq (A : Matrix n n ℂ) :
    matrixL2OperatorNorm A ≤
      Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) := by
  let T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
  have hcols :
      (∑ j, ‖T (WithLp.toLp 2 (Pi.single j 1))‖ ^ 2) =
        ∑ i, ∑ j, Complex.normSq (A i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [show T (WithLp.toLp 2 (Pi.single j 1)) =
        WithLp.toLp 2 (A *ᵥ Pi.single j 1) by rfl,
      Matrix.mulVec_single_one, EuclideanSpace.norm_sq_eq]
    simp [Complex.sq_norm]
  unfold matrixL2OperatorNorm
  exact T.opNorm_le_bound (Real.sqrt_nonneg _) fun x ↦ by
    have hx : x = ∑ j, (x j) • WithLp.toLp 2 (Pi.single j 1) := by
      ext i
      simp [Pi.single_apply]
    calc
      ‖T x‖ = ‖T (∑ j, (x j) • WithLp.toLp 2 (Pi.single j 1))‖ :=
        congrArg norm (congrArg T hx)
      _ = ‖∑ j, (x j) • T (WithLp.toLp 2 (Pi.single j 1))‖ := by
        rw [map_sum]
        simp_rw [map_smul]
      _ ≤
          ∑ j, ‖x j‖ * ‖T (WithLp.toLp 2 (Pi.single j 1))‖ := by
        simpa [norm_smul] using
          (norm_sum_le Finset.univ
            (fun j ↦ (x j) • T (WithLp.toLp 2 (Pi.single j 1))))
      _ ≤ Real.sqrt (∑ j, ‖x j‖ ^ 2) *
          Real.sqrt (∑ j, ‖T (WithLp.toLp 2 (Pi.single j 1))‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
      _ = Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) * ‖x‖ := by
        rw [hcols, ← EuclideanSpace.norm_sq_eq x,
          Real.sqrt_sq (norm_nonneg x), mul_comm]

end MatrixOperatorNorm

section ExteriorOperatorMaximum

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- Largest Euclidean operator norm of the compound matrices in exterior
degrees `0, …, card ι`. -/
def maxExteriorOperatorGrowth (R : Matrix ι ι ℂ) : ℝ :=
  (Finset.range (Fintype.card ι + 1)).sup'
    (by simp : (Finset.range (Fintype.card ι + 1)).Nonempty)
    (fun k ↦ matrixL2OperatorNorm (compound k R))

/-- Every relevant compound operator norm is bounded by the maximum over
exterior degrees. -/
theorem compound_operator_le_maxExteriorOperatorGrowth
    (R : Matrix ι ι ℂ) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    matrixL2OperatorNorm (compound k R) ≤ maxExteriorOperatorGrowth R := by
  unfold maxExteriorOperatorGrowth
  exact Finset.le_sup' (f := fun q ↦ matrixL2OperatorNorm (compound q R))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

/-- The maximum exterior operator growth is nonnegative. -/
theorem maxExteriorOperatorGrowth_nonneg (R : Matrix ι ι ℂ) :
    0 ≤ maxExteriorOperatorGrowth R := by
  exact (norm_nonneg (Matrix.toEuclideanCLM (n := powersetCard ι 0)
    (𝕜 := ℂ) (compound 0 R))).trans
      (compound_operator_le_maxExteriorOperatorGrowth R (Nat.zero_le _))

/-- Every individual compound operator norm is at most the Gram volume. -/
theorem compound_operator_le_gramVolume
    (R : Matrix ι ι ℂ) {k : ℕ} (hk : k ≤ Fintype.card ι) :
    matrixL2OperatorNorm (compound k R) ≤ gramVolume R := by
  have hdegree : compoundEnergyReal k R ≤ gramEnergy R := by
    rw [gramEnergy_eq_sum_compoundEnergyReal]
    change compoundEnergyReal k R ≤
      ∑ q ∈ Finset.range (Fintype.card ι + 1), compoundEnergyReal q R
    exact Finset.single_le_sum
      (f := fun q : ℕ ↦ compoundEnergyReal q R)
      (s := Finset.range (Fintype.card ι + 1))
      (fun q _ ↦ by
        rw [compoundEnergyReal_eq_sum_normSq]
        exact Finset.sum_nonneg fun _ _ ↦
          Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _)
      (by simpa [Nat.lt_succ_iff] using hk)
  calc
    matrixL2OperatorNorm (compound k R) ≤
        Real.sqrt (compoundEnergyReal k R) := by
      rw [compoundEnergyReal_eq_sum_normSq]
      simpa only [compound_apply] using
        (matrixL2OperatorNorm_le_sqrt_sum_normSq (compound k R))
    _ ≤ Real.sqrt (gramEnergy R) := Real.sqrt_le_sqrt hdegree
    _ = gramVolume R := rfl

/-- Lower half of the operator-norm exterior-volume comparison. -/
theorem maxExteriorOperatorGrowth_le_gramVolume (R : Matrix ι ι ℂ) :
    maxExteriorOperatorGrowth R ≤ gramVolume R := by
  unfold maxExteriorOperatorGrowth
  rw [Finset.sup'_le_iff]
  intro k hk
  exact compound_operator_le_gramVolume R
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

/-- At exterior degree `k`, Hilbert--Schmidt energy is bounded by the
dimension `choose (card ι) k` times squared operator growth. -/
theorem compoundEnergyReal_le_choose_mul_operator_sq
    (R : Matrix ι ι ℂ) (k : ℕ) :
    compoundEnergyReal k R ≤
      (Nat.choose (Fintype.card ι) k : ℝ) *
        matrixL2OperatorNorm (compound k R) ^ 2 := by
  have hcard : Fintype.card (powersetCard ι k) =
      Nat.choose (Fintype.card ι) k := by
    rw [← Nat.card_eq_fintype_card, Set.powersetCard.card,
      Nat.card_eq_fintype_card]
  rw [compoundEnergyReal_eq_sum_normSq]
  simpa only [compound_apply, hcard] using
    (sum_normSq_le_card_mul_matrixL2OperatorNorm_sq (compound k R))

/-- Energy-level upper estimate with the exact binomial sum `2^(card ι)`. -/
theorem gramEnergy_le_two_pow_mul_maxExteriorOperatorGrowth_sq
    (R : Matrix ι ι ℂ) :
    gramEnergy R ≤
      (2 : ℝ) ^ Fintype.card ι * maxExteriorOperatorGrowth R ^ 2 := by
  rw [gramEnergy_eq_sum_compoundEnergyReal]
  calc
    (∑ k ∈ Finset.range (Fintype.card ι + 1), compoundEnergyReal k R) ≤
        ∑ k ∈ Finset.range (Fintype.card ι + 1),
          (Nat.choose (Fintype.card ι) k : ℝ) *
            maxExteriorOperatorGrowth R ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        compoundEnergyReal k R ≤
            (Nat.choose (Fintype.card ι) k : ℝ) *
              matrixL2OperatorNorm (compound k R) ^ 2 :=
          compoundEnergyReal_le_choose_mul_operator_sq R k
        _ ≤ (Nat.choose (Fintype.card ι) k : ℝ) *
              maxExteriorOperatorGrowth R ^ 2 := by
          apply mul_le_mul_of_nonneg_left
          · exact (sq_le_sq₀ (norm_nonneg _)
              (maxExteriorOperatorGrowth_nonneg R)).2
              (compound_operator_le_maxExteriorOperatorGrowth R
                (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
          · positivity
    _ = (2 : ℝ) ^ Fintype.card ι * maxExteriorOperatorGrowth R ^ 2 := by
      rw [← Finset.sum_mul]
      congr 1
      norm_cast
      exact Nat.sum_range_choose (Fintype.card ι)

/-- Squaring `(sqrt 2)^n` gives `2^n`. -/
theorem sqrt_two_pow_sq (n : ℕ) :
    ((Real.sqrt 2) ^ n) ^ 2 = (2 : ℝ) ^ n := by
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Upper half of the paper's operator-norm exterior-volume comparison. -/
theorem gramVolume_le_sqrt_two_pow_mul_maxExteriorOperatorGrowth
    (R : Matrix ι ι ℂ) :
    gramVolume R ≤
      (Real.sqrt 2) ^ Fintype.card ι * maxExteriorOperatorGrowth R := by
  rw [← sq_le_sq₀ (gramVolume_nonneg R)
    (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
      (maxExteriorOperatorGrowth_nonneg R))]
  rw [gramVolume_sq, mul_pow, sqrt_two_pow_sq]
  exact gramEnergy_le_two_pow_mul_maxExteriorOperatorGrowth_sq R

/-- Complete operator-norm form of the local boundary-volume versus exterior
growth comparison of Lemma 7.8, equation (7.47). -/
theorem gramVolume_operatorCompound_two_sided (R : Matrix ι ι ℂ) :
    maxExteriorOperatorGrowth R ≤ gramVolume R ∧
      gramVolume R ≤
        (Real.sqrt 2) ^ Fintype.card ι * maxExteriorOperatorGrowth R :=
  ⟨maxExteriorOperatorGrowth_le_gramVolume R,
    gramVolume_le_sqrt_two_pow_mul_maxExteriorOperatorGrowth R⟩

end ExteriorOperatorMaximum

section TwoBlockFactor

variable {W : Type*} [Fintype W]

/-- For two equally-sized index blocks, the paper's dimensional factor
`(sqrt 2)^(card (W ⊕ W))` is exactly `2^(card W)`. -/
theorem sqrt_two_pow_card_sum_self_eq_two_pow_card :
    (Real.sqrt 2) ^ Fintype.card (W ⊕ W) =
      (2 : ℝ) ^ Fintype.card W := by
  rw [Fintype.card_sum, pow_add, ← pow_two, sqrt_two_pow_sq]

end TwoBlockFactor

section TwoBlockSpecialization

variable {W : Type*} [Fintype W] [LinearOrder W]

local instance twoBlockSpecializationSumLinearOrder : LinearOrder (W ⊕ W) :=
  LinearOrder.lift' (fun x : W ⊕ W ↦ (toLex x : W ⊕ₗ W))
    (fun _ _ h ↦ toLex.injective h)

/-- Paper-specialized upper bound for a boundary matrix indexed by two blocks
of size `card W`; its constant is displayed as `2^(card W)`. -/
theorem gramVolume_le_two_pow_card_mul_maxExteriorOperatorGrowth_twoBlock
    (R : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    gramVolume R ≤
      (2 : ℝ) ^ Fintype.card W * maxExteriorOperatorGrowth R := by
  simpa only [sqrt_two_pow_card_sum_self_eq_two_pow_card] using
    (gramVolume_le_sqrt_two_pow_mul_maxExteriorOperatorGrowth R)

/-- Complete two-block version of the paper's comparison, with the upper
constant in the advertised form `2^(card W)`. -/
theorem gramVolume_operatorCompound_two_sided_twoBlock_two_pow
    (R : Matrix (W ⊕ W) (W ⊕ W) ℂ) :
    maxExteriorOperatorGrowth R ≤ gramVolume R ∧
      gramVolume R ≤
        (2 : ℝ) ^ Fintype.card W * maxExteriorOperatorGrowth R :=
  ⟨maxExteriorOperatorGrowth_le_gramVolume R,
    gramVolume_le_two_pow_card_mul_maxExteriorOperatorGrowth_twoBlock R⟩

end TwoBlockSpecialization

end BernoulliLinearAlgebra
