import CircularLawSection6.RawPotentialScaling

/-! # Exact cutoff sums in singular bases and positive scaling

Comparing an operator with itself shows that every positive singular basis
gives the same Lipschitz spectral sum as the canonical singular values.
This proves the exact cutoff scaling identity, including its changing
threshold `a/r`, rather than assuming a singular-value scaling theorem.
-/

open scoped BigOperators
open TaoVuReplacement

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem singularValues_sum_eq_of_singular_bases (T : Module.End ℂ E)
    (hT : Function.Injective T)
    (u v : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E)
    (s : Fin (Module.finrank ℂ E) → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hTv : ∀ i, T (v i) = (s i : ℂ) • u i)
    (hTu : ∀ i, T.adjoint (u i) = (s i : ℂ) • v i)
    (φ : ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ x y, |φ x - φ y| ≤ K * |x - y|) :
    (∑ i : Fin (Module.finrank ℂ E), φ (T.singularValues i)) = ∑ i, φ (s i) := by
  obtain ⟨p, q, hTq, hTp⟩ := exists_canonical_positive_singular_bases T hT
  have h := singular_basis_lipschitz_sum T T p q u v
    (fun i => T.singularValues i) s (fun i => T.singularValues_nonneg i) hs
    hTq hTp hTv hTu φ hK hφ
  have hzero : operatorHilbertSchmidtSq (T - T) = 0 := by
    simp [operatorHilbertSchmidtSq]
  rw [hzero, mul_zero, Real.sqrt_zero, mul_zero] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

theorem log_max_positive_scale {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (s : ℝ) :
    Real.log (max (r * s) a) = Real.log r + Real.log (max s (a / r)) := by
  have hm : max (r * s) a = r * max s (a / r) := by
    rw [mul_max_of_nonneg _ _ hr.le, mul_div_cancel₀ _ hr.ne']
  rw [hm, Real.log_mul hr.ne' (ne_of_gt ((div_pos ha hr).trans_le (le_max_right _ _)))]

theorem operatorCutoffPotential_smul (T : Module.End ℂ E) (hT : Function.Injective T)
    (hdim : 0 < Module.finrank ℂ E) {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    operatorCutoffPotential ((r : ℂ) • T) a =
      Real.log r + operatorCutoffPotential T (a / r) := by
  obtain ⟨u, v, hTv, hTu⟩ := exists_canonical_positive_singular_bases T hT
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hscale : Function.Injective ((r : ℂ) • T) := by
    intro x y h
    apply hT
    exact (smul_right_injective E hrC) h
  have hv (i) : ((r : ℂ) • T) (v i) = ((r * T.singularValues i : ℝ) : ℂ) • u i := by
    simp only [LinearMap.smul_apply, hTv, smul_smul, Complex.ofReal_mul]
  have hu (i) : (((r : ℂ) • T).adjoint) (u i) =
      ((r * T.singularValues i : ℝ) : ℂ) • v i := by
    simp only [map_smulₛₗ, Complex.conj_ofReal, LinearMap.smul_apply, hTu,
      smul_smul, Complex.ofReal_mul]
  have hsum := singularValues_sum_eq_of_singular_bases ((r : ℂ) • T) hscale u v
    (fun i => r * T.singularValues i) (fun i => mul_nonneg hr.le (T.singularValues_nonneg i))
    hv hu (fun s => Real.log (max s a)) (inv_nonneg.mpr ha.le) (log_max_lipschitz ha)
  unfold operatorCutoffPotential
  rw [hsum]
  simp_rw [log_max_positive_scale hr ha]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hn : (Module.finrank ℂ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdim.ne'
  field_simp

theorem matrixCutoffPotential_smul {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    matrixCutoffPotential ((r : ℂ) • A) a =
      Real.log r + matrixCutoffPotential A (a / r) := by
  have hm : ((r : ℂ) • A).toEuclideanLin = (r : ℂ) • A.toEuclideanLin :=
    Matrix.toEuclideanLin.map_smul _ _
  unfold matrixCutoffPotential
  rw [hm]
  exact operatorCutoffPotential_smul A.toEuclideanLin
    (toEuclideanLin_injective_of_det_ne_zero A hA)
    (by simpa only [finrank_euclideanSpace] using Fintype.card_pos (α := ι)) hr ha

theorem matrixCutoffPotential_shifted_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℂ) (z : ℂ) {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hA : (A - (z / (r : ℂ)) • 1).det ≠ 0) :
    matrixCutoffPotential ((r : ℂ) • A - z • 1) a =
      Real.log r + matrixCutoffPotential (A - (z / (r : ℂ)) • 1) (a / r) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hm : (r : ℂ) • A - z • 1 = (r : ℂ) • (A - (z / (r : ℂ)) • 1) := by
    rw [smul_sub, smul_smul]
    congr 2
    field_simp
  rw [hm, matrixCutoffPotential_smul _ hA hr ha]

end CircularLawSection6
