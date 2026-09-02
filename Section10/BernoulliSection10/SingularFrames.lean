import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Singular frames constructed from the matrix

The unitary frames used when freezing the past in Section 10.5 are
constructed by diagonalizing the positive Gram matrix. They are not an
additional assumption on the physical model. This deterministic lemma
does not assert or need a measurable choice of frames.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace BernoulliSection10

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Singular-value decomposition of an invertible complex square matrix,
with positive singular values and actual unitary matrices. -/
theorem exists_positive_singular_frames
    (A : Matrix n n ℂ) (hA : IsUnit A.det) :
    ∃ U V : unitaryGroup n ℂ, ∃ σ : n → ℝ,
      (∀ i, 0 < σ i) ∧
        A = (U : Matrix n n ℂ) * diagonal (fun i => (σ i : ℂ)) *
          star (V : Matrix n n ℂ) := by
  have hG : (Aᴴ * A).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self A
      (Matrix.mulVec_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det A).mpr hA))
  let V := hG.isHermitian.eigenvectorUnitary
  let σ : n → ℝ := fun i => Real.sqrt (hG.isHermitian.eigenvalues i)
  have hσ (i : n) : 0 < σ i := Real.sqrt_pos.2 (hG.eigenvalues_pos i)
  have hσsq (i : n) : σ i * σ i = hG.isHermitian.eigenvalues i := by
    simpa only [← sq] using Real.sq_sqrt (hG.eigenvalues_pos i).le
  let D : Matrix n n ℂ := diagonal (fun i => (σ i : ℂ))
  let E : Matrix n n ℂ := diagonal (fun i => ((σ i)⁻¹ : ℝ))
  have hEstar : star E = E := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [E, Matrix.star_apply, Matrix.diagonal_apply]
    · simp [E, Matrix.star_apply, Matrix.diagonal_apply, hij, Ne.symm hij]
  have hED : E * D = 1 := by
    rw [show E * D = diagonal (fun i =>
      (((σ i)⁻¹ : ℝ) : ℂ) * (σ i : ℂ)) from diagonal_mul_diagonal _ _]
    convert (diagonal_one : diagonal (fun _ : n => (1 : ℂ)) = 1) using 1
    congr 1
    funext i
    norm_cast
    exact inv_mul_cancel₀ (ne_of_gt (hσ i))
  have hGram : star (V : Matrix n n ℂ) * (Aᴴ * A) * V =
      diagonal (fun i => (hG.isHermitian.eigenvalues i : ℂ)) := by
    simpa only [V, Unitary.conjStarAlgAut_star_apply, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal] using
      hG.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hEGE : E * diagonal (fun i => (hG.isHermitian.eigenvalues i : ℂ)) * E = 1 := by
    simp only [E, diagonal_mul_diagonal]
    convert (diagonal_one : diagonal (fun _ : n => (1 : ℂ)) = 1) using 1
    congr 1
    funext i
    norm_cast
    rw [← hσsq i]
    field_simp [ne_of_gt (hσ i)]
  let U₀ : Matrix n n ℂ := A * V * E
  have hU : U₀ ∈ unitaryGroup n ℂ := by
    rw [mem_unitaryGroup_iff']
    calc
      star U₀ * U₀ =
          E * (star (V : Matrix n n ℂ) * (Aᴴ * A) * V) * E := by
        simp only [U₀, star_mul, hEstar, star_eq_conjTranspose]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hGram, hEGE]
  refine ⟨⟨U₀, hU⟩, V, σ, hσ, ?_⟩
  have hV : (V : Matrix n n ℂ) * star (V : Matrix n n ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp V.property
  change A = (A * (V : Matrix n n ℂ) * E) * D * star (V : Matrix n n ℂ)
  rw [Matrix.mul_assoc (A * (V : Matrix n n ℂ)) E D, hED, Matrix.mul_one,
    Matrix.mul_assoc, hV, Matrix.mul_one]

end BernoulliSection10
