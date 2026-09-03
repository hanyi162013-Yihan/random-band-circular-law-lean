/- Source snapshot: upstream-sources/arxiv-2410-16457-v3-prop-3-4-cor-3-5/Arxiv2410/V3/HermitianStieltjes.lean
   Local adaptation: import paths prefixed with Vendor; compatibility edits are documented separately. -/
import Vendor.Arxiv2410.V3.Model
import Vendor.Arxiv2410.V3.PoissonCounting
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hermitian resolvent trace as an empirical Stieltjes transform

This is the finite-dimensional spectral bridge used in the Poisson-kernel derivation of
v3 Corollary 3.5.  It is proved here rather than included in a probability interface.
-/

namespace Arxiv2410V3

open Matrix Complex
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Spectral decomposition of `A - eta I` for a Hermitian matrix. -/
theorem shiftedHermitian_spectral_decomposition
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (eta : ℂ) :
    A - eta • (1 : Matrix ι ι ℂ) =
      let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
      U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ) - eta) * Uᴴ := by
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  have hspec : A =
      U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ := by
    calc
      A = Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hA.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := hA.spectral_theorem
      _ = U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ := by
        rw [Unitary.conjStarAlgAut_apply]
        congr 2
  have hunit : U * Uᴴ = 1 := by
    change (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      star (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1
    exact Unitary.coe_mul_star_self hA.eigenvectorUnitary
  change A - eta • (1 : Matrix ι ι ℂ) =
    U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ) - eta) * Uᴴ
  calc
    A - eta • (1 : Matrix ι ι ℂ) =
        U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ - eta • 1 := by
          exact congrArg (fun M : Matrix ι ι ℂ => M - eta • 1) hspec
    _ =
        U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * Uᴴ -
          U * (eta • (1 : Matrix ι ι ℂ)) * Uᴴ := by
            simp [Matrix.mul_assoc, hunit]
    _ = U * (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) - eta • 1) * Uᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ) - eta) * Uᴴ := by
      congr 2
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]

/-- Invert the preceding spectral decomposition.  The upper-half-plane condition ensures that
no real eigenvalue equals `eta`. -/
theorem shiftedHermitian_inv_spectral_decomposition
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) {eta : ℂ} (heta : 0 < eta.im) :
    (A - eta • (1 : Matrix ι ι ℂ))⁻¹ =
      let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
      U * Matrix.diagonal (fun i => ((hA.eigenvalues i : ℂ) - eta)⁻¹) * Uᴴ := by
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  let d : ι → ℂ := fun i => (hA.eigenvalues i : ℂ) - eta
  let dinv : ι → ℂ := fun i => (d i)⁻¹
  change (A - eta • (1 : Matrix ι ι ℂ))⁻¹ =
    U * Matrix.diagonal dinv * Uᴴ
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
  have hstarunit : Uᴴ * U = 1 := by
    change star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1
    exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hunitstar : U * Uᴴ = 1 := by
    change (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      star (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1
    exact Unitary.coe_mul_star_self hA.eigenvectorUnitary
  apply Matrix.inv_eq_right_inv
  rw [shiftedHermitian_spectral_decomposition A hA eta]
  change (U * Matrix.diagonal d * Uᴴ) *
      (U * Matrix.diagonal dinv * Uᴴ) = 1
  calc
    (U * Matrix.diagonal d * Uᴴ) * (U * Matrix.diagonal dinv * Uᴴ) =
        U * Matrix.diagonal d * (Uᴴ * U) * Matrix.diagonal dinv * Uᴴ := by
      noncomm_ring
    _ = U * Matrix.diagonal d * Matrix.diagonal dinv * Uᴴ := by
      rw [hstarunit]
      simp
    _ = U * (Matrix.diagonal d * Matrix.diagonal dinv) * Uᴴ := by noncomm_ring
    _ = U * Uᴴ := by rw [hdiag, Matrix.mul_one]
    _ = 1 := hunitstar

/-- The exact trace/eigenvalue identity needed by v3 Corollary 3.5. -/
theorem normalizedTrace_resolvent_eq_empiricalStieltjes [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) {eta : ℂ} (heta : 0 < eta.im) :
    normalizedTrace ((A - eta • (1 : Matrix ι ι ℂ))⁻¹) =
      empiricalStieltjes hA.eigenvalues eta := by
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  let dinv : ι → ℂ := fun i => ((hA.eigenvalues i : ℂ) - eta)⁻¹
  rw [normalizedTrace, empiricalStieltjes,
    shiftedHermitian_inv_spectral_decomposition A hA heta]
  change Matrix.trace (U * Matrix.diagonal dinv * Uᴴ) /
      (Fintype.card ι : ℂ) = (∑ i, dinv i) / (Fintype.card ι : ℂ)
  congr 1
  rw [Matrix.trace_mul_cycle]
  have hstarunit : Uᴴ * U = 1 := by
    change star (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      (hA.eigenvectorUnitary : Matrix ι ι ℂ) = 1
    exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [hstarunit, Matrix.one_mul]
  simp [dinv]

/-- v3 formula (3.1) specialized to the actual Hermitization. -/
theorem stieltjesTrace_eq_empiricalHermitizationSpectrum
    {n : ℕ} [NeZero n]
    (X : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) {eta : ℂ} (heta : 0 < eta.im) :
    stieltjesTrace X z eta =
      empiricalStieltjes (hermitization_isHermitian X z).eigenvalues eta := by
  exact normalizedTrace_resolvent_eq_empiricalStieltjes
    (hermitization X z) (hermitization_isHermitian X z) heta

end Arxiv2410V3
