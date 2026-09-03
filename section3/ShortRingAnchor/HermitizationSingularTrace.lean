import ShortRingAnchor.HermitizationResolventBlocks
import ShortRingAnchor.PoissonSmoothingCDF
import Vendor.Arxiv2410.V3.Model
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Lemma 3.5: the Hermitization trace equals the symmetric singular-value transform

The proof uses the right singular-vector basis only. The block equations
give equal diagonal traces and determine the lower block on that basis.
No density argument, invertibility of the original matrix, or SVD interface
is assumed. The two inverse identities are supplied by the proved
Hermitian resolvent theorem in the final matrix adapter.
-/

open scoped BigOperators ComplexConjugate InnerProductSpace
open Matrix

noncomputable section
namespace ShortRingAnchor

/-- v3 (3.1): a real spectral value cannot equal an upper-half-plane parameter. -/
theorem real_sub_upperHalfPlane_ne_zero (s : ℝ) {eta : ℂ} (heta : 0 < eta.im) :
    (s : ℂ) - eta ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub] at hi
  linarith

/-- Lemma 3.5: the Gram resolvent denominators do not vanish, also when `s=0`. -/
theorem real_sq_sub_upperHalfPlane_sq_ne_zero (s : ℝ) {eta : ℂ} (heta : 0 < eta.im) :
    (s : ℂ) ^ 2 - eta ^ 2 ≠ 0 := by
  have hm := real_sub_upperHalfPlane_ne_zero s heta
  have hp : (s : ℂ) + eta ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.zero_im, zero_add] at hi
    linarith
  rw [sq_sub_sq]
  exact mul_ne_zero hp hm

/-- Lemma 3.5: pairing `+s` and `-s` gives the Gram resolvent scalar. -/
theorem symmetric_resolvent_pair (s : ℝ) {eta : ℂ} (heta : 0 < eta.im) :
    ((s : ℂ) - eta)⁻¹ + ((-s : ℝ) - eta : ℂ)⁻¹ =
      2 * (eta / ((s : ℂ) ^ 2 - eta ^ 2)) := by
  have hm := real_sub_upperHalfPlane_ne_zero s heta
  have hn := real_sub_upperHalfPlane_ne_zero (-s) heta
  have hq := real_sq_sub_upperHalfPlane_sq_ne_zero s heta
  simp only [Complex.ofReal_neg] at hn ⊢
  field_simp
  ring

/-- Lemma 3.5: the shifted Gram matrix acts diagonally on the already
constructed right singular-vector basis. -/
theorem gram_shift_apply_rightSingularVector {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (eta : ℂ) (i : Fin n) :
    (Bᴴ * B - eta ^ 2 • 1).toEuclideanLin (rightSingularVector B i) =
      (((matrixSingularValue B i : ℝ) : ℂ) ^ 2 - eta ^ 2) •
        rightSingularVector B i := by
  rw [map_sub, map_smul, Matrix.toLpLin_mul_same, Matrix.toLpLin_one]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply]
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    adjoint_apply_apply_rightSingularVector, sub_smul]

/-- Lemma 3.5: the Gram block equation determines the lower resolvent
block on every right singular vector. -/
theorem gram_solution_apply_rightSingularVector {n : ℕ}
    (B T : Matrix (Fin n) (Fin n) ℂ) {eta : ℂ} (heta : 0 < eta.im)
    (hgram : T * (Bᴴ * B - eta ^ 2 • 1) = eta • 1) (i : Fin n) :
    T.toEuclideanLin (rightSingularVector B i) =
      (eta / (((matrixSingularValue B i : ℝ) : ℂ) ^ 2 - eta ^ 2)) •
        rightSingularVector B i := by
  let q : ℂ := ((matrixSingularValue B i : ℝ) : ℂ) ^ 2 - eta ^ 2
  have hq : q ≠ 0 := real_sq_sub_upperHalfPlane_sq_ne_zero _ heta
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ =>
    A.toEuclideanLin (rightSingularVector B i)) hgram
  rw [Matrix.toLpLin_mul_same, map_smul, Matrix.toLpLin_one] at h
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
  rw [gram_shift_apply_rightSingularVector, map_smul] at h
  change q • T.toEuclideanLin (rightSingularVector B i) =
    eta • rightSingularVector B i at h
  calc
    T.toEuclideanLin (rightSingularVector B i) =
        q⁻¹ • (q • T.toEuclideanLin (rightSingularVector B i)) := by
      simp [smul_smul, hq]
    _ = q⁻¹ • (eta • rightSingularVector B i) := by rw [h]
    _ = (eta / q) • rightSingularVector B i := by
      rw [smul_smul]
      congr 1
      ring

/-- Lemma 3.5: compute the Gram-block trace in the right singular-vector
basis; all multiplicities and zero singular values are included. -/
theorem trace_gram_solution_eq_singular_sum {n : ℕ}
    (B T : Matrix (Fin n) (Fin n) ℂ) {eta : ℂ} (heta : 0 < eta.im)
    (hgram : T * (Bᴴ * B - eta ^ 2 • 1) = eta • 1) :
    Matrix.trace T = ∑ i : Fin n,
      eta / (((matrixSingularValue B i : ℝ) : ℂ) ^ 2 - eta ^ 2) := by
  let b := B.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvectorBasis
    (show Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = n by simp)
  have ht : T.toEuclideanLin.trace ℂ (EuclideanSpace ℂ (Fin n)) = Matrix.trace T := by
    simp [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [← ht, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℂ (rightSingularVector B i)
      (T.toEuclideanLin (rightSingularVector B i)) = _
  rw [gram_solution_apply_rightSingularVector B T heta hgram i, inner_smul_right]
  have hnorm : inner ℂ (rightSingularVector B i) (rightSingularVector B i) = 1 := by
    have hn : ‖rightSingularVector B i‖ = 1 := b.orthonormal.1 i
    simp [inner_self_eq_norm_sq_to_K, hn]
  rw [hnorm, mul_one]

/-- Lemma 3.5 and v3 (3.1): the exact normalized Hermitization inverse trace
is the symmetric singular-value transform, assuming only its two inverse
identities. The actual upper-half-plane inverse is instantiated separately. -/
theorem normalizedTrace_hermitization_inverse_eq_singularStieltjes {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) {eta : ℂ} (heta : 0 < eta.im)
    (M : Matrix (HermitizationIndex n) (HermitizationIndex n) ℂ)
    (hleft : (hermitization B - eta • 1) * M = 1)
    (hright : M * (hermitization B - eta • 1) = 1) :
    Arxiv2410V3.normalizedTrace M =
      Arxiv2410V3.empiricalStieltjes
        (symmetrizedSpectrum (fun i : Fin n => matrixSingularValue B i)) eta := by
  have heta0 : eta ≠ 0 := by
    intro h
    simp [h] at heta
  have heq := hermitization_inverse_diagonal_traces_eq B heta0 M hleft hright
  have hgram := hermitization_inverse_lowerBlock_gram B eta M hleft hright
  have htrace := trace_gram_solution_eq_singular_sum B M.toBlocks₂₂ heta hgram
  rw [Arxiv2410V3.normalizedTrace, trace_eq_diagonalBlock_traces M, heq, htrace]
  unfold Arxiv2410V3.empiricalStieltjes symmetrizedSpectrum
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  simp_rw [← Finset.sum_add_distrib, symmetric_resolvent_pair _ heta, two_mul]

end ShortRingAnchor
