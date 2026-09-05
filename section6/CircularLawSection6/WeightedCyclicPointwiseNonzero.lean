import CircularLawSection6.GaussianProfile
import ShortRingAnchor.DensityNonsingularity

/-! # Fixed-shift nonsingularity for weighted cyclic Gaussian matrices

The determinant is written as a polynomial in the independent cyclic atom
coordinates.  A nonzero diagonal weight makes this polynomial nonzero: set
the diagonal coordinates so that the matrix is `(z + 1) I`.  Product
nonatomicity then proves almost-sure nonsingularity for every fixed `z`.
This is the fixed-parameter replacement for the older Fubini-in-`z` lemma.
-/

open MeasureTheory ShortRingAnchor

noncomputable section
set_option autoImplicit false
set_option warningAsError true

namespace CircularLawSection6

def weightedCyclicPolynomialMatrix (N : ℕ) [NeZero N]
    (q : ZMod N → ℝ) :
    Matrix (ZMod N) (ZMod N) (MvPolynomial (ZMod N × ZMod N) ℂ) :=
  fun i j =>
    MvPolynomial.C (Real.sqrt (q (j - i)) : ℂ) * MvPolynomial.X (i, j - i)

def weightedCyclicShiftedDetPolynomial (N : ℕ) [NeZero N]
    (q : ZMod N → ℝ) (z : ℂ) :
    MvPolynomial (ZMod N × ZMod N) ℂ :=
  (weightedCyclicPolynomialMatrix N q -
    (MvPolynomial.C z : MvPolynomial (ZMod N × ZMod N) ℂ) •
      (1 : Matrix (ZMod N) (ZMod N) (MvPolynomial (ZMod N × ZMod N) ℂ))).det

theorem eval_weightedCyclicShiftedDetPolynomial
    (N : ℕ) [NeZero N] (q : ZMod N → ℝ) (z : ℂ)
    (ω : ZMod N × ZMod N → ℂ) :
    MvPolynomial.eval ω (weightedCyclicShiftedDetPolynomial N q z) =
      (weightedCyclicMatrix N q ω - z • (1 : Matrix (ZMod N) (ZMod N) ℂ)).det := by
  unfold weightedCyclicShiftedDetPolynomial
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [weightedCyclicPolynomialMatrix, weightedCyclicMatrix]
  · simp [weightedCyclicPolynomialMatrix, weightedCyclicMatrix, hij]

theorem weightedCyclicShiftedDetPolynomial_ne_zero
    (N : ℕ) [NeZero N] (q : ZMod N → ℝ) (hq : 0 < q 0) (z : ℂ) :
    weightedCyclicShiftedDetPolynomial N q z ≠ 0 := by
  let ω : ZMod N × ZMod N → ℂ := fun is =>
    if is.2 = 0 then (z + 1) / (Real.sqrt (q 0) : ℂ) else 0
  have hsqrt : (Real.sqrt (q 0) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  have hmatrix : weightedCyclicMatrix N q ω = (z + 1) • 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [weightedCyclicMatrix, sub_self, ω, if_pos, Matrix.smul_apply,
        Matrix.one_apply_eq]
      simpa only [smul_eq_mul, mul_one] using mul_div_cancel₀ (z + 1) hsqrt
    · have hji : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
      simp [weightedCyclicMatrix, ω, hji, hij]
  intro hp
  have heval := eval_weightedCyclicShiftedDetPolynomial N q z ω
  rw [hp] at heval
  simp only [map_zero] at heval
  rw [hmatrix] at heval
  have hshift : (z + 1) • (1 : Matrix (ZMod N) (ZMod N) ℂ) - z • 1 = 1 := by
    module
  rw [hshift, Matrix.det_one] at heval
  exact zero_ne_one heval

/-- A weighted cyclic matrix with a nonzero diagonal variance is almost
surely nonsingular after subtracting any prescribed scalar matrix. -/
theorem weightedCyclicMatrix_shifted_det_ne_zero
    (N : ℕ) [NeZero N] (q : ZMod N → ℝ) (hq : 0 < q 0)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] [NullSingletonClass ν] (z : ℂ) :
    ∀ᵐ ω ∂cyclicAtomLaw N ν,
      (weightedCyclicMatrix N q ω - z • (1 : Matrix (ZMod N) (ZMod N) ℂ)).det ≠ 0 := by
  have hpoly := mvPolynomial_ne_zero_ae_of_law_absolutelyContinuous
    (mu := cyclicAtomLaw N ν) (nu := cyclicAtomLaw N ν)
    (id : (ZMod N × ZMod N → ℂ) → (ZMod N × ZMod N → ℂ))
    measurable_id.aemeasurable
    (by rw [Measure.map_id])
    (by
      unfold cyclicAtomLaw
      exact hasNullMvPolynomialZeroSets_pi (fun _ : ZMod N × ZMod N => ν))
    (weightedCyclicShiftedDetPolynomial N q z)
    (weightedCyclicShiftedDetPolynomial_ne_zero N q hq z)
  filter_upwards [hpoly] with ω hω
  simpa only [id_eq, eval_weightedCyclicShiftedDetPolynomial] using hω

namespace NoncompactProfile

theorem gaussian_profile_det_nonzero (p : NoncompactProfile)
    (N : ℕ) [NeZero N] (W : ℝ) (z : ℂ) :
    ∀ᵐ ω ∂gaussianProfileLaw N, (p.matrix N W ω - z • 1).det ≠ 0 := by
  simpa only [gaussianProfileLaw, matrix] using
    weightedCyclicMatrix_shifted_det_ne_zero N (p.weight N W)
      (p.weight_pos N W 0) circularComplexGaussian z

theorem gaussian_core_det_nonzero (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) (z : ℂ) :
    ∀ᵐ ω ∂gaussianProfileLaw N, (p.coreMatrix N H W ω - z • 1).det ≠ 0 := by
  have hzero : 0 < maskedWeight (coreOffsets N H) (p.weight N W) 0 := by
    simp only [maskedWeight, if_pos (zero_mem_coreOffsets N H)]
    exact p.weight_pos N W 0
  simpa only [gaussianProfileLaw, coreMatrix] using
    weightedCyclicMatrix_shifted_det_ne_zero N
      (maskedWeight (coreOffsets N H) (p.weight N W)) hzero circularComplexGaussian z

theorem gaussian_unitCore_det_nonzero (p : NoncompactProfile)
    (N H : ℕ) [NeZero N] (W : ℝ) (z : ℂ) :
    ∀ᵐ ω ∂gaussianProfileLaw N, (p.unitCoreMatrix N H W ω - z • 1).det ≠ 0 := by
  have hzero : 0 < maskedWeight (coreOffsets N H) (p.normalizedCoreWeight N H W) 0 := by
    simp only [maskedWeight, if_pos (zero_mem_coreOffsets N H)]
    exact div_pos (p.positive _) (p.rawCoreMass_pos N H W)
  simpa only [gaussianProfileLaw, unitCoreMatrix] using
    weightedCyclicMatrix_shifted_det_ne_zero N
      (maskedWeight (coreOffsets N H) (p.normalizedCoreWeight N H W)) hzero
      circularComplexGaussian z

end NoncompactProfile
end CircularLawSection6
