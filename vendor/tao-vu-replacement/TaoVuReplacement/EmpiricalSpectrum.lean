import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Finite non-Hermitian empirical spectra

The empirical spectral distribution is built from the roots of the
characteristic polynomial, counted with algebraic multiplicity.  This module
starts with finite root sums; the probability-measure wrapper is added after
the required cardinality and measurability lemmas are established.
-/

open scoped BigOperators

namespace TaoVuReplacement

open Matrix Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The multiset of eigenvalues of a complex square matrix, counted with
algebraic multiplicity. -/
noncomputable def eigenvalueMultiset (A : Matrix n n ℂ) : Multiset ℂ :=
  A.charpoly.roots

/-- The number of eigenvalues counted with algebraic multiplicity is the
matrix dimension. -/
theorem card_eigenvalueMultiset (A : Matrix n n ℂ) :
    (eigenvalueMultiset A).card = Fintype.card n := by
  simpa [eigenvalueMultiset] using
    (IsAlgClosed.card_roots_eq_natDegree (p := A.charpoly))

/-- An unnormalized finite spectral test sum. -/
noncomputable def spectralSum (A : Matrix n n ℂ) (f : ℂ → ℂ) : ℂ :=
  (eigenvalueMultiset A).map f |>.sum

/-- A constant test function is summed once for every eigenvalue, including
algebraic multiplicity. -/
theorem spectralSum_const (A : Matrix n n ℂ) (c : ℂ) :
    spectralSum A (fun _ ↦ c) = (Fintype.card n : ℂ) * c := by
  simp [spectralSum, card_eigenvalueMultiset, nsmul_eq_mul]

/-- Finite spectral test sums commute with pointwise addition. -/
theorem spectralSum_add (A : Matrix n n ℂ) (f g : ℂ → ℂ) :
    spectralSum A (fun w ↦ f w + g w) = spectralSum A f + spectralSum A g := by
  simp only [spectralSum, Multiset.sum_map_add]

/-- Finite spectral test sums commute with complex scalar multiplication. -/
theorem spectralSum_smul (A : Matrix n n ℂ) (c : ℂ) (f : ℂ → ℂ) :
    spectralSum A (fun w ↦ c • f w) = c • spectralSum A f := by
  simp only [spectralSum, smul_eq_mul, Multiset.sum_map_mul_left]

/-- The normalized empirical spectral test functional. -/
noncomputable def esdTest (A : Matrix n n ℂ) (f : ℂ → ℂ) : ℂ :=
  spectralSum A f / (Fintype.card n : ℂ)

/-- The normalized empirical spectral functional commutes with pointwise
addition. -/
theorem esdTest_add (A : Matrix n n ℂ) (f g : ℂ → ℂ) :
    esdTest A (fun w ↦ f w + g w) = esdTest A f + esdTest A g := by
  simp only [esdTest, spectralSum_add, add_div]

/-- The normalized empirical spectral functional commutes with complex scalar
multiplication. -/
theorem esdTest_smul (A : Matrix n n ℂ) (c : ℂ) (f : ℂ → ℂ) :
    esdTest A (fun w ↦ c • f w) = c • esdTest A f := by
  simp only [esdTest, spectralSum_smul]
  simp only [smul_eq_mul]
  ring

/-- Every constant test function integrates to that constant in positive
dimension. -/
theorem esdTest_const [Nonempty n] (A : Matrix n n ℂ) (c : ℂ) :
    esdTest A (fun _ ↦ c) = c := by
  rw [esdTest, spectralSum_const]
  have hcard : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_div_cancel_left₀ c hcard

/-- The empirical spectral functional has total mass one in positive
dimension. -/
theorem esdTest_one [Nonempty n] (A : Matrix n n ℂ) :
    esdTest A (fun _ ↦ 1) = 1 := by
  exact esdTest_const A 1

/-! ## Determinants and logarithmic root sums -/

/-- The determinant of `A - zI` is the product of `lambda - z` over all
eigenvalues `lambda` of `A`, counted with algebraic multiplicity.  This is the
finite-dimensional algebraic identity used by the logarithmic-potential side
of the replacement principle. -/
theorem det_sub_scalar_eq_prod_eigenvalue_sub
    (A : Matrix n n ℂ) (z : ℂ) :
    (A - z • (1 : Matrix n n ℂ)).det =
      ((eigenvalueMultiset A).map fun lambda ↦ lambda - z).prod := by
  have hscalar : Matrix.scalar n z = z • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar_apply]
    · simp [Matrix.scalar_apply, hij]
  have heval :
      A.charpoly.eval z = (z • (1 : Matrix n n ℂ) - A).det := by
    simpa only [hscalar] using Matrix.eval_charpoly A z
  have hfactor :
      A.charpoly.eval z =
        ((eigenvalueMultiset A).map fun lambda ↦ z - lambda).prod := by
    simpa only [eigenvalueMultiset] using
      (IsAlgClosed.splits A.charpoly).eval_eq_prod_roots_of_monic
        A.charpoly_monic z
  have hprodNeg :
      ((eigenvalueMultiset A).map fun lambda ↦ lambda - z).prod =
        (-1 : ℂ) ^ (eigenvalueMultiset A).card *
          ((eigenvalueMultiset A).map fun lambda ↦ z - lambda).prod := by
    simpa only [Multiset.map_map, Function.comp_apply, neg_sub,
      Multiset.card_map] using
        Multiset.prod_map_neg
          ((eigenvalueMultiset A).map fun lambda ↦ z - lambda)
  calc
    (A - z • (1 : Matrix n n ℂ)).det =
        (-(z • (1 : Matrix n n ℂ) - A)).det := by
      congr 1
      abel
    _ = (-1 : ℂ) ^ Fintype.card n *
        (z • (1 : Matrix n n ℂ) - A).det := Matrix.det_neg _
    _ = (-1 : ℂ) ^ Fintype.card n * A.charpoly.eval z := by rw [heval]
    _ = (-1 : ℂ) ^ Fintype.card n *
        ((eigenvalueMultiset A).map fun lambda ↦ z - lambda).prod := by
      rw [hfactor]
    _ = ((eigenvalueMultiset A).map fun lambda ↦ lambda - z).prod := by
      rw [hprodNeg, card_eigenvalueMultiset]

/-- The real-valued spectral sum used for logarithmic test functions. -/
noncomputable def realSpectralSum (A : Matrix n n ℂ) (f : ℂ → ℝ) : ℝ :=
  ((eigenvalueMultiset A).map f).sum

/-- The real-valued normalized empirical spectral test functional. -/
noncomputable def realEsdTest (A : Matrix n n ℂ) (f : ℂ → ℝ) : ℝ :=
  realSpectralSum A f / (Fintype.card n : ℝ)

/-- Real-valued constant test functions are counted with the algebraic
multiplicity of the spectrum. -/
theorem realSpectralSum_const (A : Matrix n n ℂ) (c : ℝ) :
    realSpectralSum A (fun _ ↦ c) = (Fintype.card n : ℝ) * c := by
  simp [realSpectralSum, card_eigenvalueMultiset, nsmul_eq_mul]

/-- Real-valued finite spectral sums commute with pointwise addition. -/
theorem realSpectralSum_add (A : Matrix n n ℂ) (f g : ℂ → ℝ) :
    realSpectralSum A (fun w ↦ f w + g w) =
      realSpectralSum A f + realSpectralSum A g := by
  simp only [realSpectralSum, Multiset.sum_map_add]

/-- Real-valued finite spectral sums commute with real scalar
multiplication. -/
theorem realSpectralSum_smul (A : Matrix n n ℂ) (c : ℝ) (f : ℂ → ℝ) :
    realSpectralSum A (fun w ↦ c • f w) = c • realSpectralSum A f := by
  simp only [realSpectralSum, smul_eq_mul, Multiset.sum_map_mul_left]

/-- The normalized real empirical spectral functional commutes with
pointwise addition. -/
theorem realEsdTest_add (A : Matrix n n ℂ) (f g : ℂ → ℝ) :
    realEsdTest A (fun w ↦ f w + g w) =
      realEsdTest A f + realEsdTest A g := by
  simp only [realEsdTest, realSpectralSum_add, add_div]

/-- The normalized real empirical spectral functional commutes with real
scalar multiplication. -/
theorem realEsdTest_smul (A : Matrix n n ℂ) (c : ℝ) (f : ℂ → ℝ) :
    realEsdTest A (fun w ↦ c • f w) = c • realEsdTest A f := by
  calc
    realEsdTest A (fun w ↦ c • f w) =
        realSpectralSum A (fun w ↦ c • f w) / (Fintype.card n : ℝ) := rfl
    _ = (c • realSpectralSum A f) / (Fintype.card n : ℝ) := by
      rw [realSpectralSum_smul]
    _ = c • (realSpectralSum A f / (Fintype.card n : ℝ)) := by
      simp only [smul_eq_mul]
      ring
    _ = c • realEsdTest A f := rfl

/-- Every real constant test function integrates to that constant in
positive dimension. -/
theorem realEsdTest_const [Nonempty n] (A : Matrix n n ℂ) (c : ℝ) :
    realEsdTest A (fun _ ↦ c) = c := by
  rw [realEsdTest, realSpectralSum_const]
  have hcard : (Fintype.card n : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_div_cancel_left₀ c hcard

private theorem norm_multiset_prod (s : Multiset ℂ) :
    ‖s.prod‖ = (s.map norm).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

/-- Away from the spectrum, the real logarithm of the determinant norm is the
sum of the logarithmic distances to all eigenvalues, with algebraic
multiplicity.  The nonzero premise is essential: Lean's real logarithm uses
the totalized convention `Real.log 0 = 0`, so the product-to-sum identity must
not be asserted at a zero of the determinant. -/
theorem log_norm_det_sub_scalar_eq_realSpectralSum
    (A : Matrix n n ℂ) (z : ℂ)
    (hdet : (A - z • (1 : Matrix n n ℂ)).det ≠ 0) :
    Real.log ‖(A - z • (1 : Matrix n n ℂ)).det‖ =
      realSpectralSum A (fun lambda ↦ Real.log ‖lambda - z‖) := by
  have hprod :
      ((eigenvalueMultiset A).map fun lambda ↦ lambda - z).prod ≠ 0 := by
    rw [← det_sub_scalar_eq_prod_eigenvalue_sub]
    exact hdet
  have hfactor : ∀ lambda ∈ eigenvalueMultiset A, ‖lambda - z‖ ≠ 0 := by
    intro lambda hlambda
    rw [norm_ne_zero_iff]
    intro hlambdaZero
    apply hprod
    apply Multiset.prod_eq_zero
    apply Multiset.mem_map.mpr
    exact ⟨lambda, hlambda, hlambdaZero⟩
  have hnorms : ∀ x ∈
      (eigenvalueMultiset A).map (fun lambda ↦ ‖lambda - z‖), x ≠ 0 := by
    intro x hx
    rcases Multiset.mem_map.mp hx with ⟨lambda, hlambda, rfl⟩
    exact hfactor lambda hlambda
  calc
    Real.log ‖(A - z • (1 : Matrix n n ℂ)).det‖ =
        Real.log ‖((eigenvalueMultiset A).map
          fun lambda ↦ lambda - z).prod‖ := by
      rw [det_sub_scalar_eq_prod_eigenvalue_sub]
    _ = Real.log (((eigenvalueMultiset A).map
          fun lambda ↦ ‖lambda - z‖).prod) := by
      rw [norm_multiset_prod]
      simp only [Multiset.map_map, Function.comp_apply]
    _ = ((eigenvalueMultiset A).map
          fun lambda ↦ Real.log ‖lambda - z‖).sum := by
      simpa only [Multiset.map_map, Function.comp_apply] using
        Real.log_multiset_prod hnorms
    _ = realSpectralSum A (fun lambda ↦ Real.log ‖lambda - z‖) := by
      rfl

/-- Normalized form of the preceding identity: away from the spectrum, the
normalized logarithmic determinant is exactly the empirical spectral test of
the logarithmic kernel. -/
theorem normalized_log_norm_det_sub_scalar_eq_realEsdTest
    (A : Matrix n n ℂ) (z : ℂ)
    (hdet : (A - z • (1 : Matrix n n ℂ)).det ≠ 0) :
    Real.log ‖(A - z • (1 : Matrix n n ℂ)).det‖ /
        (Fintype.card n : ℝ) =
      realEsdTest A (fun lambda ↦ Real.log ‖lambda - z‖) := by
  rw [realEsdTest, log_norm_det_sub_scalar_eq_realSpectralSum A z hdet]

end TaoVuReplacement

