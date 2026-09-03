import ShortRingAnchor.AlmostSureNonsingularity
import ShortRingAnchor.AtomLawAbsoluteContinuity
import ShortRingAnchor.NormalizedGinibre
import ShortRingAnchor.HighProbabilityTransfer

/-!
# Density and independence imply nonsingularity of the comparison process

This file supplies the nonsingularity step in the determinant/singular-value
translation used in Proposition 3.6, formulas (3.8) and (3.11)--(3.14).
The shift is any fixed `z : ℂ`.  No estimate uniform in `z` is asserted.
-/

open Filter Set
open scoped ENNReal Topology

noncomputable section

namespace ShortRingAnchor

open MeasureTheory ProbabilityTheory

/-- Proposition 3.6's geometric-probability step needs only independence
and nonatomic marginal laws.  The joint law is identified internally with
the product law, whose polynomial zero sets have already been proved null. -/
theorem mvPolynomial_ne_zero_ae_of_independent_nonatomic
    {Omega sigma : Type*} [MeasurableSpace Omega] [Fintype sigma]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (atom : sigma → Omega → ℂ)
    (hmeas : ∀ i, AEMeasurable (atom i) mu)
    (hindep : iIndepFun atom mu)
    [∀ i, NullSingletonClass (Measure.map (atom i) mu)]
    (p : MvPolynomial sigma ℂ) (hp : p ≠ 0) :
    ∀ᵐ sample ∂mu,
      MvPolynomial.eval (fun i => atom i sample) p ≠ 0 := by
  apply mvPolynomial_ne_zero_ae_of_law_absolutelyContinuous
    (fun sample i => atom i sample) (aemeasurable_pi_lambda _ hmeas)
    (nu := Measure.pi (fun i => Measure.map (atom i) mu))
  · simpa only [hindep.map_fun_eq_pi_map hmeas] using
      (Measure.AbsolutelyContinuous.rfl :
        Measure.pi (fun i => Measure.map (atom i) mu) ≪
          Measure.pi (fun i => Measure.map (atom i) mu))
  · exact hasNullMvPolynomialZeroSets_pi _
  · exact hp

/-- Both bounded-density alternatives in Assumption 2.1 imply the
nonatomicity needed above.  Real-valued atoms are not incorrectly assumed
to be absolutely continuous with respect to planar complex volume. -/
theorem mvPolynomial_ne_zero_ae_of_independent_density
    {Omega sigma : Type*} [MeasurableSpace Omega] [Fintype sigma]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (atom : sigma → Omega → ℂ)
    (hmeas : ∀ i, AEMeasurable (atom i) mu)
    (hindep : iIndepFun atom mu)
    (hdensity : ∀ i, AtomDensityAlternative21 mu (atom i))
    (p : MvPolynomial sigma ℂ) (hp : p ≠ 0) :
    ∀ᵐ sample ∂mu,
      MvPolynomial.eval (fun i => atom i sample) p ≠ 0 := by
  let : ∀ i, NullSingletonClass (Measure.map (atom i) mu) :=
    fun i => (hdensity i).nullSingletonClass (hmeas i)
  exact mvPolynomial_ne_zero_ae_of_independent_nonatomic atom hmeas hindep p hp

/-- The determinant step for independent entries with either real or
complex density, valid at every fixed complex shift in Proposition 3.6. -/
theorem shifted_det_ne_zero_ae_of_independent_density
    {Omega ι : Type*} [MeasurableSpace Omega] [Fintype ι] [DecidableEq ι]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (A : Omega → Matrix ι ι ℂ)
    (hmeas : ∀ ij : ι × ι,
      AEMeasurable (fun sample => A sample ij.1 ij.2) mu)
    (hindep : iIndepFun
      (fun (ij : ι × ι) sample => A sample ij.1 ij.2) mu)
    (hdensity : ∀ ij : ι × ι,
      AtomDensityAlternative21 mu (fun sample => A sample ij.1 ij.2))
    (z : ℂ) :
    ∀ᵐ sample ∂mu, (A sample - z • (1 : Matrix ι ι ℂ)).det ≠ 0 := by
  filter_upwards [mvPolynomial_ne_zero_ae_of_independent_density
    (fun (ij : ι × ι) sample => A sample ij.1 ij.2)
    hmeas hindep hdensity (shiftedDetPolynomial (ι := ι) z)
    (shiftedDetPolynomial_ne_zero z)] with sample hsample
  change matrixPolynomialEvaluation (shiftedDetPolynomial z) (A sample) ≠ 0 at hsample
  simpa only [matrixPolynomialEvaluation_shiftedDetPolynomial] using hsample

/-- The same independent-density argument applies directly to the active
band coordinates in model (3.1), without giving a density to its fixed
zero matrix entries. -/
theorem cyclicShortRing_shifted_det_ne_zero_ae_of_independent_density
    {Omega : Type*} [MeasurableSpace Omega]
    {M W : Nat} {c0 C0 : ℝ}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (weights : AdmissibleWeights W c0 C0)
    (hfit : 2 * W + 1 ≤ M)
    (entry : Omega → Fin M → BandOffset W → ℂ)
    (hmeas : ∀ is : Fin M × BandOffset W,
      AEMeasurable (fun sample => entry sample is.1 is.2) mu)
    (hindep : iIndepFun
      (fun (is : Fin M × BandOffset W) sample => entry sample is.1 is.2) mu)
    (hdensity : ∀ is : Fin M × BandOffset W,
      AtomDensityAlternative21 mu (fun sample => entry sample is.1 is.2))
    (z : ℂ) :
    ∀ᵐ sample ∂mu,
      (cyclicShortRingRandomMatrix weights hfit entry sample -
        z • (1 : Matrix (Fin M) (Fin M) ℂ)).det ≠ 0 := by
  filter_upwards [mvPolynomial_ne_zero_ae_of_independent_density
    (fun (is : Fin M × BandOffset W) sample => entry sample is.1 is.2)
    hmeas hindep hdensity (cyclicShortRingShiftedDetPolynomial weights hfit z)
    (cyclicShortRingShiftedDetPolynomial_ne_zero weights hfit z)]
    with sample hsample
  simpa only [cyclicShortRingRandomMatrix,
    eval_cyclicShortRingShiftedDetPolynomial] using hsample

/-- Proposition 3.6's dense normalization does not create a zero shifted
determinant: rescale the shift before dividing the whole matrix by `c`. -/
theorem det_div_sub_smul_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (z c : ℂ) (hc : c ≠ 0)
    (hdet : (A - (c * z) • (1 : Matrix ι ι ℂ)).det ≠ 0) :
    (Matrix.of (fun i j => A i j / c) -
      z • (1 : Matrix ι ι ℂ)).det ≠ 0 := by
  have hmatrix :
      Matrix.of (fun i j => A i j / c) - z • (1 : Matrix ι ι ℂ) =
        c⁻¹ • (A - (c * z) • (1 : Matrix ι ι ℂ)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    field_simp
  rw [hmatrix, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hc)) hdet

/-- Nonsingularity of the normalized dense comparison process in
Proposition 3.6, now derived from independence and Assumption 2.1 densities
instead of supplied as a separate matrix-probability hypothesis. -/
theorem normalizedDense_shifted_det_ne_zero_ae_of_independent_density
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat → Nat} {mu : Measure Omega} [IsProbabilityMeasure mu]
    (atom : ∀ n, Omega → Fin (M n) → Fin (M n) → ℂ)
    (hMpos : ∀ n, 0 < M n)
    (hmeas : ∀ n i j, AEMeasurable (fun sample => atom n sample i j) mu)
    (hindep : ∀ n, iIndepFun
      (fun (ij : Fin (M n) × Fin (M n)) sample => atom n sample ij.1 ij.2) mu)
    (hdensity : ∀ n i j,
      AtomDensityAlternative21 mu (fun sample => atom n sample i j))
    (z : ℂ) (n : Nat) :
    ∀ᵐ sample ∂mu,
      (normalizedDenseMatrixProcess atom n sample -
        z • (1 : Matrix (Fin (M n)) (Fin (M n)) ℂ)).det ≠ 0 := by
  have hc : (Real.sqrt (M n : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (Real.sqrt_pos.2 (by exact_mod_cast hMpos n)).ne'
  filter_upwards [shifted_det_ne_zero_ae_of_independent_density
    (atom n) (fun ij => hmeas n ij.1 ij.2) (hindep n)
    (fun ij => hdensity n ij.1 ij.2) ((Real.sqrt (M n : ℝ) : ℂ) * z)]
    with sample hsample
  exact det_div_sub_smul_ne_zero (atom n sample) z _ hc hsample

/-- The dense nonsingularity-in-probability premise used in Proposition
3.6 follows from the preceding per-dimension a.e. result, for every fixed
`z`; no geometric-measure or nonsingularity interface remains here. -/
theorem normalizedDense_shiftedNonsingularInProbability_of_independent_density
    {Omega : Type*} [MeasurableSpace Omega]
    {M : Nat → Nat} {mu : Measure Omega} [IsProbabilityMeasure mu]
    (atom : ∀ n, Omega → Fin (M n) → Fin (M n) → ℂ)
    (hMpos : ∀ n, 0 < M n)
    (hmeas : ∀ n i j, AEMeasurable (fun sample => atom n sample i j) mu)
    (hindep : ∀ n, iIndepFun
      (fun (ij : Fin (M n) × Fin (M n)) sample => atom n sample ij.1 ij.2) mu)
    (hdensity : ∀ n i j,
      AtomDensityAlternative21 mu (fun sample => atom n sample i j))
    (z : ℂ) :
    ShiftedNonsingularInProbability mu (normalizedDenseMatrixProcess atom) z :=
  shiftedNonsingularInProbability_of_ae _ z
    (normalizedDense_shifted_det_ne_zero_ae_of_independent_density
      atom hMpos hmeas hindep hdensity z)

end ShortRingAnchor
