import CircularLawSection6.HermitianSpectralCoupling
import CircularLawSection6.PositiveSingularBasis

/-! # Singular-value Lipschitz comparison from the actual singular bases

Average the squared overlaps of the left and right bases. The resulting
coupling has unit marginals. A two-coefficient inequality bounds its
quadratic cost by the Hilbert--Schmidt square of the matrix difference.
This proves the needed average comparison without assuming Mirsky's
inequality or supplying an optimal matching.
-/

open scoped BigOperators InnerProductSpace
open TaoVuReplacement

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

theorem complex_two_coefficient_cost (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (a b : ℂ) :
    (‖a‖ ^ 2 + ‖b‖ ^ 2) * (s - t) ^ 2 ≤
      ‖(s : ℂ) * a - (t : ℂ) * b‖ ^ 2 +
        ‖(s : ℂ) * b - (t : ℂ) * a‖ ^ 2 := by
  have h := mul_nonneg (mul_nonneg hs ht)
    (add_nonneg (sq_nonneg (a.re - b.re)) (sq_nonneg (a.im - b.im)))
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem singular_basis_lipschitz_sum (A B : Module.End ℂ E)
    (u v p q : OrthonormalBasis ι ℂ E) (s t : ι → ℝ)
    (hs : ∀ i, 0 ≤ s i) (ht : ∀ i, 0 ≤ t i)
    (hAv : ∀ i, A (v i) = (s i : ℂ) • u i)
    (hAu : ∀ i, A.adjoint (u i) = (s i : ℂ) • v i)
    (hBq : ∀ j, B (q j) = (t j : ℂ) • p j)
    (hBp : ∀ j, B.adjoint (p j) = (t j : ℂ) • q j)
    (φ : ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ x y, |φ x - φ y| ≤ K * |x - y|) :
    |(∑ i, φ (s i)) - (∑ j, φ (t j))| ≤
      K * Real.sqrt ((Fintype.card ι : ℝ) * operatorHilbertSchmidtSq (A - B)) := by
  let w : ι → ι → ℝ := fun i j =>
    (orthonormalCoupling v q i j + orthonormalCoupling u p i j) / 2
  have hw (i j) : 0 ≤ w i j := div_nonneg
    (add_nonneg (orthonormalCoupling_nonneg _ _ _ _) (orthonormalCoupling_nonneg _ _ _ _))
    (by norm_num)
  have hrow (i) : ∑ j, w i j = 1 := by
    simp only [w]
    rw [← Finset.sum_div, Finset.sum_add_distrib, orthonormalCoupling_row,
      orthonormalCoupling_row]
    norm_num
  have hcol (j) : ∑ i, w i j = 1 := by
    simp only [w]
    rw [← Finset.sum_div, Finset.sum_add_distrib, orthonormalCoupling_column,
      orthonormalCoupling_column]
    norm_num
  have hx (i j) : ⟪u i, (A - B) (q j)⟫_ℂ =
      (s i : ℂ) * ⟪v i, q j⟫_ℂ - (t j : ℂ) * ⟪u i, p j⟫_ℂ := by
    rw [LinearMap.sub_apply, inner_sub_right, ← A.adjoint_inner_left, hAu, hBq,
      inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ)]
    rw [show (starRingEnd ℂ) (s i : ℂ) = (s i : ℂ) from Complex.conj_ofReal _]
  have hy (i j) : ⟪(A - B) (v i), p j⟫_ℂ =
      (s i : ℂ) * ⟪u i, p j⟫_ℂ - (t j : ℂ) * ⟪v i, q j⟫_ℂ := by
    rw [LinearMap.sub_apply, inner_sub_left, hAv, ← B.adjoint_inner_right, hBp,
      inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ)]
    rw [show (starRingEnd ℂ) (s i : ℂ) = (s i : ℂ) from Complex.conj_ofReal _]
  have hpair (i j) : w i j * (s i - t j) ^ 2 ≤
      (‖⟪u i, (A - B) (q j)⟫_ℂ‖ ^ 2 + ‖⟪p j, (A - B) (v i)⟫_ℂ‖ ^ 2) / 2 := by
    rw [norm_inner_symm (p j) ((A - B) (v i)), hx, hy]
    have h := complex_two_coefficient_cost (s i) (t j) (hs i) (ht j)
      ⟪v i, q j⟫_ℂ ⟪u i, p j⟫_ℂ
    dsimp only [w, orthonormalCoupling]
    linarith
  have hcost : (∑ i, ∑ j, w i j * (s i - t j) ^ 2) ≤
      operatorHilbertSchmidtSq (A - B) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpair i j))
    simp_rw [← Finset.sum_div, Finset.sum_add_distrib] at h
    rw [crossBasis_energy_eq u q, Finset.sum_comm (f := fun i j =>
      ‖⟪p j, (A - B) (v i)⟫_ℂ‖ ^ 2), crossBasis_energy_eq p v] at h
    linarith
  exact (lipschitz_sum_difference_le_weighted_cost w hw hrow hcol s t φ hK hφ).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg _))) hK)

theorem singularValues_lipschitz_sum (A B : Module.End ℂ E)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (φ : ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ x y, |φ x - φ y| ≤ K * |x - y|) :
    |(∑ i : Fin (Module.finrank ℂ E), φ (A.singularValues i)) -
        (∑ j : Fin (Module.finrank ℂ E), φ (B.singularValues j))| ≤
      K * Real.sqrt ((Module.finrank ℂ E : ℝ) * operatorHilbertSchmidtSq (A - B)) := by
  obtain ⟨u, v, hAv, hAu⟩ := exists_canonical_positive_singular_bases A hA
  obtain ⟨p, q, hBq, hBp⟩ := exists_canonical_positive_singular_bases B hB
  simpa only [Fintype.card_fin] using singular_basis_lipschitz_sum A B u v p q
    (fun i => A.singularValues i) (fun j => B.singularValues j)
    (fun i => A.singularValues_nonneg i) (fun j => B.singularValues_nonneg j)
    hAv hAu hBq hBp φ hK hφ

end CircularLawSection6
