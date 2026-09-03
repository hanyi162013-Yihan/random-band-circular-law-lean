/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/ResolventPerturbation.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.HermitianStieltjes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The deterministic resolvent perturbation step in v3 formula (3.8)

This file formalizes the non-probabilistic part of the perturbation argument on
arXiv:2410.16457v3, TeX source lines 402--429.  In the notation there,
`Delta = 𝒴_z - 𝒴_zᵒ` and the algebraic identity is

`𝒢_z - 𝒢_zᵒ = -𝒢_z Delta 𝒢_zᵒ`.

The Gaussian maximum estimate for `‖Delta‖` is deliberately not asserted here.
-/

namespace Arxiv2410V3

open Matrix Complex
open scoped BigOperators Matrix.Norms.L2Operator

section AlgebraicResolventIdentity

variable {A : Type*} [Ring A]

/-- The purely algebraic inverse-difference identity in a noncommutative ring. -/
theorem inverse_sub_inverse_of_mul_eq_one
    (p q pInv qInv : A)
    (hp : pInv * p = 1) (hq : q * qInv = 1) :
    pInv - qInv = pInv * (q - p) * qInv := by
  calc
    pInv - qInv = pInv * (q * qInv) - (pInv * p) * qInv := by rw [hp, hq, mul_one, one_mul]
    _ = pInv * (q - p) * qInv := by noncomm_ring

/-- The resolvent identity used at v3 TeX line 421 (the sign corresponds to
`Delta = a - b`). -/
theorem resolvent_identity_of_mul_eq_one
    (a b shift rA rB : A)
    (hA : rA * (a - shift) = 1) (hB : (b - shift) * rB = 1) :
    rA - rB = -(rA * (a - b) * rB) := by
  rw [inverse_sub_inverse_of_mul_eq_one (a - shift) (b - shift) rA rB hA hB]
  noncomm_ring

end AlgebraicResolventIdentity

section NormedResolventIdentity

variable {A : Type*} [NormedRing A]

/-- Deterministic norm consequence of the algebraic resolvent identity. -/
theorem norm_resolvent_sub_le
    (a b shift rA rB : A)
    (hA : rA * (a - shift) = 1) (hB : (b - shift) * rB = 1) :
    ‖rA - rB‖ ≤ ‖rA‖ * ‖a - b‖ * ‖rB‖ := by
  rw [resolvent_identity_of_mul_eq_one a b shift rA rB hA hB, norm_neg]
  exact norm_mul_le _ _ |>.trans <|
    mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)

/-- The `v⁻²` form used in v3 formula (3.8), isolated from any probability estimate. -/
theorem norm_resolvent_sub_le_of_bounds
    (a b shift rA rB : A) {v : ℝ}
    (hA : rA * (a - shift) = 1) (hB : (b - shift) * rB = 1)
    (hv : 0 < v) (hrA : ‖rA‖ ≤ v⁻¹) (hrB : ‖rB‖ ≤ v⁻¹) :
    ‖rA - rB‖ ≤ ‖a - b‖ / v ^ 2 := by
  calc
    ‖rA - rB‖ ≤ ‖rA‖ * ‖a - b‖ * ‖rB‖ :=
      norm_resolvent_sub_le a b shift rA rB hA hB
    _ ≤ v⁻¹ * ‖a - b‖ * v⁻¹ := by gcongr
    _ = ‖a - b‖ / v ^ 2 := by field_simp

end NormedResolventIdentity

section HermitianResolvent

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Hermitian shift by an upper-half-plane parameter is two-sided invertible. -/
theorem shiftedHermitian_inv_mul_and_mul_inv
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) {eta : ℂ} (heta : 0 < eta.im) :
    (M - eta • (1 : Matrix ι ι ℂ))⁻¹ * (M - eta • 1) = 1 ∧
      (M - eta • (1 : Matrix ι ι ℂ)) * (M - eta • 1)⁻¹ = 1 := by
  let U : Matrix ι ι ℂ := hM.eigenvectorUnitary
  let d : ι → ℂ := fun i => (hM.eigenvalues i : ℂ) - eta
  let dinv : ι → ℂ := fun i => (d i)⁻¹
  have hdne (i : ι) : d i ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [d] at him
    linarith
  have hdiag : Matrix.diagonal d * Matrix.diagonal dinv =
      (1 : Matrix ι ι ℂ) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d, dinv, hdne]
    · simp [hij]
  have hdiag' : Matrix.diagonal dinv * Matrix.diagonal d =
      (1 : Matrix ι ι ℂ) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d, dinv, hdne]
    · simp [hij]
  have hstarunit : Uᴴ * U = 1 := by
    change star (hM.eigenvectorUnitary : Matrix ι ι ℂ) *
      (hM.eigenvectorUnitary : Matrix ι ι ℂ) = 1
    exact Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hunitstar : U * Uᴴ = 1 := by
    change (hM.eigenvectorUnitary : Matrix ι ι ℂ) *
      star (hM.eigenvectorUnitary : Matrix ι ι ℂ) = 1
    exact Unitary.coe_mul_star_self hM.eigenvectorUnitary
  rw [shiftedHermitian_inv_spectral_decomposition M hM heta,
    shiftedHermitian_spectral_decomposition M hM eta]
  change (U * Matrix.diagonal dinv * Uᴴ) * (U * Matrix.diagonal d * Uᴴ) = 1 ∧
    (U * Matrix.diagonal d * Uᴴ) * (U * Matrix.diagonal dinv * Uᴴ) = 1
  constructor
  · calc
      (U * Matrix.diagonal dinv * Uᴴ) * (U * Matrix.diagonal d * Uᴴ) =
          U * Matrix.diagonal dinv * (Uᴴ * U) * Matrix.diagonal d * Uᴴ := by
            noncomm_ring
      _ = U * Matrix.diagonal dinv * Matrix.diagonal d * Uᴴ := by
            rw [hstarunit]
            simp
      _ = U * (Matrix.diagonal dinv * Matrix.diagonal d) * Uᴴ := by
            noncomm_ring
      _ = 1 := by rw [hdiag', Matrix.mul_one, hunitstar]
  · calc
      (U * Matrix.diagonal d * Uᴴ) * (U * Matrix.diagonal dinv * Uᴴ) =
          U * Matrix.diagonal d * (Uᴴ * U) * Matrix.diagonal dinv * Uᴴ := by
            noncomm_ring
      _ = U * Matrix.diagonal d * Matrix.diagonal dinv * Uᴴ := by
            rw [hstarunit]
            simp
      _ = U * (Matrix.diagonal d * Matrix.diagonal dinv) * Uᴴ := by
            noncomm_ring
      _ = 1 := by rw [hdiag, Matrix.mul_one, hunitstar]

/-- The standard deterministic Hermitian resolvent estimate used at v3 TeX line 425. -/
theorem norm_shiftedHermitian_inv_le_inv_im
    [Nonempty ι]
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) {eta : ℂ} (heta : 0 < eta.im) :
    ‖(M - eta • (1 : Matrix ι ι ℂ))⁻¹‖ ≤ (eta.im)⁻¹ := by
  let U : Matrix ι ι ℂ := hM.eigenvectorUnitary
  let dinv : ι → ℂ := fun i => ((hM.eigenvalues i : ℂ) - eta)⁻¹
  rw [shiftedHermitian_inv_spectral_decomposition M hM heta]
  change ‖U * Matrix.diagonal dinv * Uᴴ‖ ≤ (eta.im)⁻¹
  calc
    ‖U * Matrix.diagonal dinv * Uᴴ‖ ≤ ‖Matrix.diagonal dinv‖ := by
      calc
        ‖U * Matrix.diagonal dinv * Uᴴ‖ ≤
            ‖U‖ * ‖Matrix.diagonal dinv‖ * ‖Uᴴ‖ :=
          norm_mul_le _ _ |>.trans <|
            mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ = ‖Matrix.diagonal dinv‖ := by
          rw [Matrix.l2_opNorm_conjTranspose]
          simp [U]
    _ = ‖dinv‖ := Matrix.l2_opNorm_diagonal dinv
    _ ≤ (eta.im)⁻¹ := by
      rw [pi_norm_le_iff_of_nonneg (inv_nonneg.mpr heta.le)]
      intro i
      rw [norm_inv]
      have him : eta.im ≤ |(((hM.eigenvalues i : ℂ) - eta).im)| := by simp [abs_of_pos heta]
      have hbound : eta.im ≤ ‖(hM.eigenvalues i : ℂ) - eta‖ :=
        him.trans (Complex.abs_im_le_norm _)
      have hne : (hM.eigenvalues i : ℂ) - eta ≠ 0 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        linarith
      exact (inv_le_inv₀ (norm_pos_iff.mpr hne) heta).2 hbound

end HermitianResolvent

section NormalizedTrace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every matrix entry is bounded by the `L²` operator norm.  This is the deterministic
input behind `|tr_N A| ≤ ‖A‖` at v3 TeX line 427. -/
theorem norm_matrix_entry_le_l2Operator
    (M : Matrix ι ι ℂ) (i j : ι) : ‖M i j‖ ≤ ‖M‖ := by
  let e : EuclideanSpace ℂ ι := WithLp.toLp 2 (Pi.single j 1)
  have happ : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M e) i = M i j := by
    change (M *ᵥ Pi.single j 1) i = M i j
    simp
  calc
    ‖M i j‖ = ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M e) i‖ := by rw [happ]
    _ ≤ ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M e‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M‖ * ‖e‖ :=
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M).le_opNorm e
    _ = ‖M‖ := by simp [e, Matrix.l2_opNorm_toEuclideanCLM]

/-- The normalized matrix trace is contractive for the `L²` operator norm. -/
theorem norm_normalizedTrace_le_l2Operator [Nonempty ι]
    (M : Matrix ι ι ℂ) : ‖normalizedTrace M‖ ≤ ‖M‖ := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by positivity
  rw [normalizedTrace, norm_div, Complex.norm_natCast]
  rw [div_le_iff₀ hcard]
  calc
    ‖Matrix.trace M‖ ≤ ∑ i : ι, ‖M i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖M‖ :=
      Finset.sum_le_sum fun i _ => norm_matrix_entry_le_l2Operator M i i
    _ = ‖M‖ * (Fintype.card ι : ℝ) := by simp [mul_comm]

omit [DecidableEq ι] in
/-- Linearity of the paper's normalized trace under subtraction. -/
theorem normalizedTrace_sub
    (M N : Matrix ι ι ℂ) :
    normalizedTrace (M - N) = normalizedTrace M - normalizedTrace N := by
  simp [normalizedTrace, Matrix.trace_sub, sub_div]

end NormalizedTrace

section MatrixSpecialization

variable {n : ℕ}

/-- The exact Green-matrix identity at v3 TeX line 421. -/
theorem greenFunction_sub_greenFunction
    (X Xo : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) :
    greenFunction X z eta - greenFunction Xo z eta =
      -(greenFunction X z eta * (hermitization X z - hermitization Xo z) *
        greenFunction Xo z eta) := by
  apply resolvent_identity_of_mul_eq_one
  · exact (shiftedHermitian_inv_mul_and_mul_inv
      (hermitization X z) (hermitization_isHermitian X z) heta).1
  · exact (shiftedHermitian_inv_mul_and_mul_inv
      (hermitization Xo z) (hermitization_isHermitian Xo z) heta).2

variable [NeZero n]

/-- The operator-norm perturbation inequality before inserting the Gaussian estimate in (3.8). -/
theorem norm_greenFunction_sub_le
    (X Xo : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) :
    ‖greenFunction X z eta - greenFunction Xo z eta‖ ≤
      ‖hermitization X z - hermitization Xo z‖ / eta.im ^ 2 := by
  apply norm_resolvent_sub_le_of_bounds
  · exact (shiftedHermitian_inv_mul_and_mul_inv
      (hermitization X z) (hermitization_isHermitian X z) heta).1
  · exact (shiftedHermitian_inv_mul_and_mul_inv
      (hermitization Xo z) (hermitization_isHermitian Xo z) heta).2
  · exact heta
  · exact norm_shiftedHermitian_inv_le_inv_im
      (hermitization X z) (hermitization_isHermitian X z) heta
  · exact norm_shiftedHermitian_inv_le_inv_im
      (hermitization Xo z) (hermitization_isHermitian Xo z) heta

/-- The normalized-trace half of v3 formula (3.8), before inserting the probabilistic
Gaussian maximum estimate for the Hermitization difference. -/
theorem norm_stieltjesTrace_sub_le
    (X Xo : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) :
    ‖stieltjesTrace X z eta - stieltjesTrace Xo z eta‖ ≤
      ‖hermitization X z - hermitization Xo z‖ / eta.im ^ 2 := by
  rw [stieltjesTrace, stieltjesTrace, ← normalizedTrace_sub]
  exact (norm_normalizedTrace_le_l2Operator _).trans
    (norm_greenFunction_sub_le X Xo z heta)

end MatrixSpecialization

end Arxiv2410V3
