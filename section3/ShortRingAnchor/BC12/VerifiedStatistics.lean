import ShortRingAnchor.BC12.VerifiedKernel
import Ginibre.AllDimensionsStatistics
import Mathlib.Probability.HasLaw

/-!
# Exact normalized Ginibre moments from Gaussian entries

BC12 Theorems 3.3--3.4, in the normalization used by Section 3.
The upstream covariance is an unnormalized algebraic second moment.
Here genuine L2 integrability is proved before converting it to the
centered-square integral and dividing by the square of the dimension.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace ShortRingAnchor.BC12

/-- BC12 actual spectrum on the independent Gaussian entry space. -/
def rawGinibreSpectrum (n : ℕ) (A : (Fin n × Fin n) → ℂ) : Fin n → ℂ :=
  Ginibre.schurSpectrum (Matrix.of A.curry)

/-- BC12 first moment, including integrability, before empirical normalization. -/
theorem verified_rawStatistic_integrable {n : ℕ} (hn : 0 < n)
    (f : ℂ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z => f z * Ginibre.ginibreIntensity n z)) :
    Integrable (fun A => Ginibre.linearStatistic n f (rawGinibreSpectrum n A))
      (Ginibre.gaussianMatrixLaw n n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  apply Ginibre.gaussianMatrix_integrable_linearStatistic m f hf
  simp_rw [Ginibre.kernelDet_one, Ginibre.kernel_diagonal_re]
  exact (Ginibre.integrable_finOne_iff _).mpr hi

/-- BC12 L2 domain: Cauchy--Schwarz bounds the squared sum by `n` times
the sum of squared tests. Thus an integral equality alone is never used
as evidence of integrability. -/
theorem verified_rawStatistic_memLp_two {n : ℕ} (hn : 0 < n)
    (f : ℂ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z => f z ^ 2 * Ginibre.ginibreIntensity n z)) :
    MemLp (fun A => Ginibre.linearStatistic n f (rawGinibreSpectrum n A)) 2
      (Ginibre.gaussianMatrixLaw n n) := by
  have hm : AEMeasurable (fun A => Ginibre.linearStatistic n f (rawGinibreSpectrum n A))
      (Ginibre.gaussianMatrixLaw n n) := by
    apply (show Measurable (Ginibre.linearStatistic n f) from
      Finset.measurable_sum _ (fun i _ => hf.comp (measurable_pi_apply i))).comp_aemeasurable
    exact Ginibre.aemeasurable_gaussianMatrix_spectrum n (by exact_mod_cast hn)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
  apply ((verified_rawStatistic_integrable hn (fun z => f z ^ 2)
    (hf.pow_const 2) hi).const_mul (n : ℝ)).mono' (hm.pow_const 2).aestronglyMeasurable
  filter_upwards with A
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Ginibre.linearStatistic] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin n => (1 : ℝ)) (fun i => f (rawGinibreSpectrum n A i)))

/-- BC12 normalized first moment, constructed on the actual entry law. -/
theorem verified_raw_firstMoment {n : ℕ} (hn : 0 < n)
    (f : ℂ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z => f z * ginibreOnePointDensity n z)) :
    Integrable (eigenvalueStatistic (rawGinibreSpectrum n) f) (Ginibre.gaussianMatrixLaw n n) ∧
      (∫ A, eigenvalueStatistic (rawGinibreSpectrum n) f A ∂Ginibre.gaussianMatrixLaw n n) =
        ∫ z, f z * ginibreOnePointDensity n z := by
  have hi' : Integrable (fun z => f z * Ginibre.ginibreIntensity n z) := by
    simpa only [Ginibre.ginibreIntensity, ← ginibreOnePointDensity_eq_verified,
      mul_left_comm] using hi.const_mul (n : ℝ)
  refine ⟨(verified_rawStatistic_integrable hn f hf hi').div_const _, ?_⟩
  change (∫ A, Ginibre.linearStatistic n f (rawGinibreSpectrum n A) / (n : ℝ)
    ∂Ginibre.gaussianMatrixLaw n n) = _
  rw [integral_div]
  simp only [rawGinibreSpectrum]
  rw [Ginibre.gaussianMatrix_integral_linearStatistic_all n f hf hi']
  have he : (fun z => f z * Ginibre.ginibreIntensity n z) =
      fun z => (n : ℝ) * (f z * ginibreOnePointDensity n z) := by
    funext z
    change f z * ((n : ℝ) * ginibreOnePointDensity n z) = _
    ring
  rw [he, integral_const_mul, mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne')]

/-- BC12 normalized centered second moment, with its full L1 domain. -/
theorem verified_raw_secondMoment {n : ℕ} (hn : 0 < n)
    (f : ℂ → ℝ) (hf : Measurable f)
    (hi : Integrable (fun z => f z ^ 2 * ginibreOnePointDensity n z)) :
    Integrable (fun A => (eigenvalueStatistic (rawGinibreSpectrum n) f A -
      ∫ B, eigenvalueStatistic (rawGinibreSpectrum n) f B ∂Ginibre.gaussianMatrixLaw n n) ^ 2)
      (Ginibre.gaussianMatrixLaw n n) ∧
    (∫ A, (eigenvalueStatistic (rawGinibreSpectrum n) f A -
      ∫ B, eigenvalueStatistic (rawGinibreSpectrum n) f B ∂Ginibre.gaussianMatrixLaw n n) ^ 2
      ∂Ginibre.gaussianMatrixLaw n n) =
      (∫ p : ℂ × ℂ, (f p.1 - f p.2) ^ 2 * ginibreKernelWeight n p) / (2 * (n : ℝ) ^ 2) := by
  letI := Ginibre.gaussianMatrixLaw_isProbability n (by exact_mod_cast hn : (0 : ℝ) < n)
  have hi' : Integrable (fun z => f z ^ 2 * Ginibre.ginibreIntensity n z) := by
    simpa only [Ginibre.ginibreIntensity, ← ginibreOnePointDensity_eq_verified,
      mul_left_comm] using hi.const_mul (n : ℝ)
  have hraw := verified_rawStatistic_memLp_two hn f hf hi'
  have hnorm : MemLp (eigenvalueStatistic (rawGinibreSpectrum n) f) 2
      (Ginibre.gaussianMatrixLaw n n) := by
    change MemLp (fun A => (∑ i, f (rawGinibreSpectrum n A i)) / (n : ℝ)) 2 _
    simpa only [Ginibre.linearStatistic, div_eq_mul_inv] using
      hraw.mul_const ((n : ℝ)⁻¹)
  refine ⟨(hnorm.sub (memLp_const _)).integrable_sq, ?_⟩
  rw [← variance_eq_integral hnorm.aemeasurable]
  change variance (fun A => Ginibre.linearStatistic n f (rawGinibreSpectrum n A) /
    (n : ℝ)) (Ginibre.gaussianMatrixLaw n n) = _
  simp only [div_eq_mul_inv]
  rw [variance_mul_const]
  have hv : variance (fun A => Ginibre.linearStatistic n f (rawGinibreSpectrum n A))
      (Ginibre.gaussianMatrixLaw n n) = Ginibre.gaussianEigenvalueVariance n f := by
    rw [variance_eq_sub hraw]
    simp only [Ginibre.gaussianEigenvalueVariance, Ginibre.gaussianEigenvalueCovariance,
      rawGinibreSpectrum, Pi.pow_apply, pow_two]
  rw [hv, Ginibre.gaussianEigenvalueVariance_all_energy n f hf hi']
  change (1 / 2 : ℝ) * (∫ p : ℂ × ℂ,
    (f p.1 - f p.2) ^ 2 * ginibreKernelWeight n p) * (n : ℝ)⁻¹ ^ 2 = _
  simp only [mul_inv_rev, inv_pow]
  ring

/-- BC12 finite correlation interface, proved from independent Gaussian entries. -/
theorem verifiedGinibreCorrelations {n : ℕ} (hn : 0 < n) :
    GinibreCorrelationFormulas (Ginibre.gaussianMatrixLaw n n) (rawGinibreSpectrum n) :=
  ⟨verified_raw_firstMoment hn, verified_raw_secondMoment hn⟩

/-- BC12 moments are invariant under realizing the same entry law on another space.
`HasLaw` specifies the model; it assumes no eigenvalue or correlation theorem. -/
theorem GinibreCorrelationFormulas.comp_hasLaw
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} {X : Ω → Ξ} (hX : HasLaw X ν μ)
    {n : ℕ} (hn : 0 < n) {eigenvalue : Ξ → Fin n → ℂ}
    (h : GinibreCorrelationFormulas ν eigenvalue) :
    GinibreCorrelationFormulas μ (fun sample => eigenvalue (X sample)) := by
  have integral_comp {g : Ξ → ℝ} (hg : Integrable g ν) :
      Integrable (g ∘ X) μ ∧ (∫ x, g (X x) ∂μ) = ∫ y, g y ∂ν := by
    refine ⟨?_, hX.integral_comp hg.aestronglyMeasurable⟩
    exact (hX.map_eq.symm ▸ hg : Integrable g (μ.map X)).comp_aemeasurable hX.aemeasurable
  constructor
  · intro f hf hi
    obtain ⟨hi', he⟩ := h.firstMoment f hf hi
    exact ⟨(integral_comp hi').1, (integral_comp hi').2.trans he⟩
  · intro f hf hi
    obtain ⟨hi', he⟩ := h.secondMoment f hf hi
    have hf1 : Integrable (fun z => f z * ginibreOnePointDensity n z) := by
      have hscaled : Integrable (fun z => f z ^ 2 * Ginibre.ginibreIntensity n z) := by
        simpa only [Ginibre.ginibreIntensity, ← ginibreOnePointDensity_eq_verified,
          mul_left_comm] using hi.const_mul (n : ℝ)
      have hl := (Ginibre.integrable_mul_ginibreIntensity_of_sq n f hf hscaled).div_const (n : ℝ)
      apply hl.congr
      filter_upwards with z
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      change f z * ((n : ℝ) * ginibreOnePointDensity n z) / (n : ℝ) = _
      field_simp [hn0]
    have hm := (integral_comp (h.firstMoment f hf hf1).1).2
    have ht := integral_comp hi'
    change (∫ x, eigenvalueStatistic (fun sample => eigenvalue (X sample)) f x ∂μ) = _ at hm
    simp only [hm]
    exact ⟨ht.1, ht.2.trans he⟩

end ShortRingAnchor.BC12
