import CircularLawSection6.PublishedStieltjesMean
import CircularLawSection6.HardEdgeLogLimit
import CircularLawSection6.CompactCutoffExpectation
import ShortRingAnchor.MatrixStieltjesSmoothing

/-! # The limiting singular law inherits the published free-transform bound

The input is bounded-test convergence for the actual matrices, not a Stieltjes
identity or a density bound for the limit. Finite spectral identities, bounded
expectation convergence, and the published BBV comparison prove that identity.
The resulting hard-edge constant is uniform in the spectral shift.
-/

open MeasureTheory Filter Topology Set Arxiv2410V3
open CircularLawSections56.Section5
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

def squaredPoissonTest (t x : ℝ) : ℝ := t / (max x 0 + t ^ 2)

theorem squaredPoissonTest_continuous {t : ℝ} (ht : 0 < t) :
    Continuous (squaredPoissonTest t) := by
  apply Continuous.div continuous_const (by fun_prop)
  intro x
  exact ne_of_gt (add_pos_of_nonneg_of_pos (le_max_right x 0) (sq_pos_of_pos ht))

theorem squaredPoissonTest_abs_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |squaredPoissonTest t x| ≤ 1 / t := by
  have hx : 0 ≤ max x 0 := le_max_right _ _
  unfold squaredPoissonTest
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_div_iff₀ (by positivity) ht).2
  nlinarith

theorem squaredPoissonTest_sq (t s : ℝ) :
    squaredPoissonTest t (s ^ 2) = singularPoissonKernel t s := by
  simp only [squaredPoissonTest, singularPoissonKernel, max_eq_left (sq_nonneg s)]

theorem empirical_symmetric_stieltjes_im {N : ℕ} [NeZero N]
    (s : Fin N → ℝ) (t : ℝ) :
    (empiricalStieltjes (ShortRingAnchor.symmetrizedSpectrum s) (spectralParameter 0 t)).im =
      (∑ i, singularPoissonKernel t (s i)) / N := by
  rw [empiricalStieltjes_im]
  simp only [ShortRingAnchor.symmetrizedSpectrum, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, sub_zero, poissonKernel, singularPoissonKernel,
    neg_sq, Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  field_simp

theorem matrix_stieltjes_im_eq_squaredPoissonAverage {N : ℕ} [NeZero N]
    (X : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    (stieltjesTrace X z (spectralParameter 0 t)).im =
      matrixSquaredSingularAverage (X - z • 1) (squaredPoissonTest t) := by
  rw [ShortRingAnchor.matrix_stieltjesTrace_eq_symmetric_singularValues X z
    (by simpa [spectralParameter] using ht),
    empirical_symmetric_stieltjes_im]
  unfold matrixSquaredSingularAverage
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = N := by simp
  symm
  refine congrArg₂ (fun x y : ℝ => x / y) ?_ (by exact_mod_cast hdim)
  apply Fintype.sum_equiv (finCongr hdim)
  intro i
  simp only [squaredPoissonTest_sq, ShortRingAnchor.shiftedSingularValueFamily,
    ShortRingAnchor.shiftedSingularValue, ShortRingAnchor.matrixSingularValue]

theorem mean_poisson_tendsto_of_squaredTests
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (X : ∀ n, Ω n → Matrix (Fin (N n)) (Fin (N n)) ℂ)
    (hX : ∀ n i j, Measurable (fun ω => X n ω i j)) (z : ℂ)
    (σ : Measure ℝ)
    (hweak : ∀ φ : ℝ → ℝ, Continuous φ → (∃ B : ℝ, ∀ x, |φ x| ≤ B) →
      TendstoInProbabilityTri μ
        (fun n ω => matrixSquaredSingularAverage (X n ω - z • 1) φ)
        (∫ s, φ (s ^ 2) ∂σ)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => ∫ ω, (stieltjesTrace (X n ω) z (spectralParameter 0 t)).im ∂μ n)
      atTop (𝓝 (∫ s, singularPoissonKernel t s ∂σ)) := by
  have heta : 0 < (spectralParameter 0 t).im := by simpa [spectralParameter] using ht
  have hp := hweak (squaredPoissonTest t) (squaredPoissonTest_continuous ht)
    ⟨1 / t, squaredPoissonTest_abs_le ht⟩
  simp_rw [squaredPoissonTest_sq, ← matrix_stieltjes_im_eq_squaredPoissonAverage _ _ ht] at hp
  apply tendsto_expectation_of_bounded_probability μ _
    (fun n => Complex.measurable_im.comp (measurable_stieltjesTrace (hX n) z _)) (1 / t)
    (∫ s, singularPoissonKernel t s ∂σ) _ hp
  intro n
  filter_upwards with ω
  exact (Complex.abs_im_le_norm _).trans (by
    simpa [spectralParameter, one_div] using
      norm_stieltjesTrace_le_inv_im (X n ω) z heta)

theorem published_dense_limiting_poisson_identity
    {Ω : ℕ → Type*} {Ξ : Type*} [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ξ]
    (μ : ∀ n, Measure (Ω n)) (ν : Measure Ξ)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop)
    (model : ∀ n, RandomMatrixModelV3 (N n) (Ω n) Ξ (μ n) ν)
    (z : ℂ) (σ : Measure ℝ) {C : ℝ} (hC : 8 ≤ C)
    (hB : ∀ n, IsBandwidth (model n).profile (N n : ℝ))
    (hthird : ∀ n, BVH.atomThirdMoment (model n) + BVH.complexGaussianThirdMomentConstant ≤ C)
    (hweak : ∀ φ : ℝ → ℝ, Continuous φ → (∃ B : ℝ, ∀ x, |φ x| ≤ B) →
      TendstoInProbabilityTri μ
        (fun n ω => matrixSquaredSingularAverage ((model n).matrix ω - z • 1) φ)
        (∫ s, φ (s ^ 2) ∂σ))
    {t : ℝ} (ht : 0 < t)
    (hBBV : ∀ n, External.BBVTheorem28GaussianFreeHypothesis
      (∫ ω, stieltjesTrace (BVH.canonicalCircularizedMatrix (model n) ω) z (spectralParameter 0 t)
        ∂BVH.canonicalGaussianMeasure (model n))
      (freeDysonStieltjes z (spectralParameter 0 t)) (N n : ℝ) t C) :
    (∫ s, singularPoissonKernel t s ∂σ) = (freeDysonStieltjes z (spectralParameter 0 t)).im := by
  have heta : 0 < (spectralParameter 0 t).im := by simpa [spectralParameter] using ht
  have hb : ∀ n, External.BBVTheorem28GaussianFreeHypothesis
      (∫ ω, stieltjesTrace (BVH.canonicalCircularizedMatrix (model n) ω) z (spectralParameter 0 t)
        ∂BVH.canonicalGaussianMeasure (model n))
      (freeDysonStieltjes z (spectralParameter 0 t)) (N n : ℝ) (spectralParameter 0 t).im C := by
    simpa [spectralParameter] using hBBV
  have hm := published_dense_meanStieltjes_tendsto μ ν N hN model z heta hC hB hthird hb
  have him := Complex.continuous_im.continuousAt.tendsto.comp hm
  have heq (n : ℕ) :
      (∫ ω, stieltjesTrace ((model n).matrix ω) z (spectralParameter 0 t) ∂μ n).im =
        ∫ ω, (stieltjesTrace ((model n).matrix ω) z (spectralParameter 0 t)).im ∂μ n := by
    simpa only [RCLike.im_eq_complex_im] using
      (integral_im ((model n).stieltjesTrace_integrable z heta)).symm
  change Tendsto (fun n => (∫ ω, stieltjesTrace ((model n).matrix ω) z
    (spectralParameter 0 t) ∂μ n).im) atTop
    (𝓝 (freeDysonStieltjes z (spectralParameter 0 t)).im) at him
  simp_rw [heq] at him
  exact tendsto_nhds_unique
    (mean_poisson_tendsto_of_squaredTests μ N (fun n => (model n).matrix)
      (fun n => (model n).entry_measurable) z σ hweak ht) him

theorem published_dense_limiting_hardEdge
    {Ω : ℕ → Type*} {Ξ : Type*} [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ξ]
    (μ : ∀ n, Measure (Ω n)) (ν : Measure Ξ)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    (N : ℕ → ℕ) [∀ n, NeZero (N n)] (hN : Tendsto N atTop atTop)
    (model : ∀ n, RandomMatrixModelV3 (N n) (Ω n) Ξ (μ n) ν)
    (z : ℂ) (σ : Measure ℝ) [IsFiniteMeasure σ] (hpos : ∀ᵐ s ∂σ, 0 ≤ s)
    {C : ℝ} (hC : 8 ≤ C)
    (hB : ∀ n, IsBandwidth (model n).profile (N n : ℝ))
    (hthird : ∀ n, BVH.atomThirdMoment (model n) + BVH.complexGaussianThirdMomentConstant ≤ C)
    (hweak : ∀ φ : ℝ → ℝ, Continuous φ → (∃ B : ℝ, ∀ x, |φ x| ≤ B) →
      TendstoInProbabilityTri μ
        (fun n ω => matrixSquaredSingularAverage ((model n).matrix ω - z • 1) φ)
        (∫ s, φ (s ^ 2) ∂σ))
    (hBBV : ∀ t, 0 < t → ∀ n, External.BBVTheorem28GaussianFreeHypothesis
      (∫ ω, stieltjesTrace (BVH.canonicalCircularizedMatrix (model n) ω) z (spectralParameter 0 t)
        ∂BVH.canonicalGaussianMeasure (model n))
      (freeDysonStieltjes z (spectralParameter 0 t)) (N n : ℝ) t C) :
    ∀ t, 0 < t → σ.real (Iic t) ≤ 2 * t := by
  intro t ht
  have hid := published_dense_limiting_poisson_identity μ ν N hN model z σ hC hB hthird
    hweak ht (hBBV t ht)
  have hp : (∫ s, singularPoissonKernel t s ∂σ) ≤ 1 := by
    rw [hid]
    exact freeDysonStieltjes_im_le_one z _ (by simpa [spectralParameter] using ht)
  simpa only [mul_one] using hardEdge_cdf_le_of_poisson_bound σ hpos ht hp

end CircularLawSection6
