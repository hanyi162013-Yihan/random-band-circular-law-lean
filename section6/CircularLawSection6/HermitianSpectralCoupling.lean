import CircularLawSection6.WeightedSpectralCoupling
import TaoVuReplacement.WeylSecondMoment
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Actual eigenvector coupling and its Hilbert--Schmidt cost

Squared overlaps of two orthonormal eigenbases have unit marginals. Their
quadratic eigenvalue transport cost equals the Hilbert--Schmidt square of
the operator difference. This reuses replacement's basis-free energy
identity and gives the spectral-average estimate without a sorting lemma.
-/

open scoped BigOperators InnerProductSpace
open TaoVuReplacement

noncomputable section

namespace CircularLawSection6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def orthonormalCoupling (u v : OrthonormalBasis ι ℂ E) (i j : ι) : ℝ :=
  ‖⟪u i, v j⟫_ℂ‖ ^ 2

theorem orthonormalCoupling_nonneg (u v : OrthonormalBasis ι ℂ E) (i j : ι) :
    0 ≤ orthonormalCoupling u v i j := sq_nonneg _

theorem orthonormalCoupling_row (u v : OrthonormalBasis ι ℂ E) (i : ι) :
    ∑ j, orthonormalCoupling u v i j = 1 := by
  simpa only [orthonormalCoupling, u.orthonormal.1 i, one_pow] using
    v.sum_sq_norm_inner_left (u i)

theorem orthonormalCoupling_column (u v : OrthonormalBasis ι ℂ E) (j : ι) :
    ∑ i, orthonormalCoupling u v i j = 1 := by
  simpa only [orthonormalCoupling, v.orthonormal.1 j, one_pow] using
    u.sum_sq_norm_inner_right (v j)

theorem crossBasis_energy_eq (u v : OrthonormalBasis ι ℂ E) (T : Module.End ℂ E) :
    (∑ i, ∑ j, ‖⟪u i, T (v j)⟫_ℂ‖ ^ 2) = operatorHilbertSchmidtSq T := by
  have hmatrix : hilbertSchmidtSq (LinearMap.toMatrix v.toBasis v.toBasis T) =
      ∑ j, ‖T (v j)‖ ^ 2 := by
    unfold hilbertSchmidtSq
    rw [Finset.sum_comm]
    simp_rw [toMatrix_orthonormalBasis_apply, v.sum_sq_norm_inner_right]
  calc
    _ = ∑ j, ∑ i, ‖⟪u i, T (v j)⟫_ℂ‖ ^ 2 := Finset.sum_comm
    _ = ∑ j, ‖T (v j)‖ ^ 2 := by simp_rw [u.sum_sq_norm_inner_right]
    _ = hilbertSchmidtSq (LinearMap.toMatrix v.toBasis v.toBasis T) := hmatrix.symm
    _ = _ := hilbertSchmidtSq_toMatrix_orthonormalBasis v T

theorem hermitian_eigenvector_coupling_cost (A B : Module.End ℂ E)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (∑ i, ∑ j, orthonormalCoupling (hA.eigenvectorBasis rfl) (hB.eigenvectorBasis rfl) i j *
      (hA.eigenvalues rfl i - hB.eigenvalues rfl j) ^ 2) = operatorHilbertSchmidtSq (A - B) := by
  let u := hA.eigenvectorBasis rfl
  let v := hB.eigenvectorBasis rfl
  have hinner (i j : Fin (Module.finrank ℂ E)) :
      ⟪u i, (A - B) (v j)⟫_ℂ =
        ((hA.eigenvalues rfl i - hB.eigenvalues rfl j : ℝ) : ℂ) * ⟪u i, v j⟫_ℂ := by
    rw [LinearMap.sub_apply, inner_sub_right, ← hA (u i) (v j)]
    dsimp only [u, v]
    rw [hA.apply_eigenvectorBasis rfl i, hB.apply_eigenvectorBasis rfl j]
    simp [inner_smul_left, inner_smul_right, Complex.ofReal_sub, sub_mul]
  calc
    _ = ∑ i, ∑ j, ‖⟪u i, (A - B) (v j)⟫_ℂ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hinner, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      unfold orthonormalCoupling
      ring
    _ = _ := crossBasis_energy_eq u v (A - B)

theorem hermitian_lipschitz_spectral_sum (A B : Module.End ℂ E)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (φ : ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ x y, |φ x - φ y| ≤ K * |x - y|) :
    |(∑ i, φ (hA.eigenvalues rfl i)) - (∑ j, φ (hB.eigenvalues rfl j))| ≤
      K * Real.sqrt ((Module.finrank ℂ E : ℝ) * operatorHilbertSchmidtSq (A - B)) := by
  have h := lipschitz_sum_difference_le_weighted_cost
    (orthonormalCoupling (hA.eigenvectorBasis rfl) (hB.eigenvectorBasis rfl))
    (orthonormalCoupling_nonneg _ _) (orthonormalCoupling_row _ _) (orthonormalCoupling_column _ _)
    (hA.eigenvalues rfl) (hB.eigenvalues rfl) φ hK hφ
  rw [hermitian_eigenvector_coupling_cost A B hA hB] at h
  simpa only [Fintype.card_fin] using h

end CircularLawSection6
