import ShortRingAnchor.HermitizationCounting
import Mathlib.Tactic.LinearCombination

/-!
# Lemma 3.5: the actual Hermitization resolvent and its Gram block

These are deterministic matrix identities. Invertibility is supplied by
the already proved upper-half-plane Hermitian resolvent theorem, not by
nonsingularity of the original matrix. Zero singular values are allowed.
-/

open scoped BigOperators ComplexConjugate
open Matrix

noncomputable section
namespace ShortRingAnchor

/-- v3 (3.1): the shifted Hermitization in explicit block form. -/
theorem hermitization_shift_eq_fromBlocks {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (eta : ℂ) :
    hermitization B - eta • 1 =
      Matrix.fromBlocks (-eta • 1) B Bᴴ (-eta • 1) := by
  ext i j
  cases i <;> cases j <;> simp [hermitization, Matrix.fromBlocks, Matrix.one_apply]

/-- Lemma 3.5: trace is the sum of the two diagonal block traces. -/
theorem trace_eq_diagonalBlock_traces {n : ℕ}
    (M : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ) :
    Matrix.trace M = Matrix.trace M.toBlocks₁₁ + Matrix.trace M.toBlocks₂₂ := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type,
    Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

/-- Lemma 3.5: three block equations extracted from the two-sided
resolvent identity; no invertibility of `B` is required. -/
theorem hermitization_inverse_block_equations {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (eta : ℂ)
    (M : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ)
    (hleft : (hermitization B - eta • 1) * M = 1)
    (hright : M * (hermitization B - eta • 1) = 1) :
    (-eta) • M.toBlocks₁₁ + B * M.toBlocks₂₁ = 1 ∧
      M.toBlocks₂₂ * Bᴴ = eta • M.toBlocks₂₁ ∧
      M.toBlocks₂₁ * B - eta • M.toBlocks₂₂ = 1 := by
  rw [hermitization_shift_eq_fromBlocks] at hleft hright
  have hM := Matrix.fromBlocks_toBlocks M
  rw [← hM, Matrix.fromBlocks_multiply] at hleft hright
  have h11 := congrArg Matrix.toBlocks₁₁ hleft
  have h21 := congrArg Matrix.toBlocks₂₁ hright
  have h22 := congrArg Matrix.toBlocks₂₂ hright
  have hone11 : (1 : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ).toBlocks₁₁ = 1 := by
    ext i j
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  have hone21 : (1 : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ).toBlocks₂₁ = 0 := by
    ext i j
    simp [Matrix.toBlocks₂₁, Matrix.one_apply]
  have hone22 : (1 : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ).toBlocks₂₂ = 1 := by
    ext i j
    simp [Matrix.toBlocks₂₂, Matrix.one_apply]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂, hone11, hone21,
    hone22, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one] at h11 h21 h22
  refine ⟨h11, ?_, ?_⟩
  · have h := eq_neg_of_add_eq_zero_right h21
    simpa using h
  · simpa only [neg_smul, ← sub_eq_add_neg] using h22

/-- Lemma 3.5: the two diagonal blocks of the Hermitization resolvent
have the same trace. Cyclicity of the finite matrix trace is sufficient. -/
theorem hermitization_inverse_diagonal_traces_eq {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) {eta : ℂ} (heta : eta ≠ 0)
    (M : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ)
    (hleft : (hermitization B - eta • 1) * M = 1)
    (hright : M * (hermitization B - eta • 1) = 1) :
    Matrix.trace M.toBlocks₁₁ = Matrix.trace M.toBlocks₂₂ := by
  obtain ⟨h11, _, h22⟩ := hermitization_inverse_block_equations B eta M hleft hright
  have ht11 := congrArg Matrix.trace h11
  have ht22 := congrArg Matrix.trace h22
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    smul_eq_mul, neg_mul] at ht11 ht22
  rw [Matrix.trace_mul_comm B M.toBlocks₂₁] at ht11
  apply mul_left_cancel₀ heta
  linear_combination ht22 - ht11

/-- Lemma 3.5: the lower diagonal resolvent block solves the Gram equation
`T (BᴴB - eta² I) = eta I`, including singular `B`. -/
theorem hermitization_inverse_lowerBlock_gram {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (eta : ℂ)
    (M : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ)
    (hleft : (hermitization B - eta • 1) * M = 1)
    (hright : M * (hermitization B - eta • 1) = 1) :
    M.toBlocks₂₂ * (Bᴴ * B - eta ^ 2 • 1) = eta • 1 := by
  obtain ⟨_, h21, h22⟩ := hermitization_inverse_block_equations B eta M hleft hright
  calc
    M.toBlocks₂₂ * (Bᴴ * B - eta ^ 2 • 1) =
        eta • (M.toBlocks₂₁ * B - eta • M.toBlocks₂₂) := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, h21, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.mul_one, smul_sub, smul_smul, pow_two]
    _ = eta • 1 := by rw [h22]

end ShortRingAnchor
