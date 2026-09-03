import CircularLawSection6.GinibreRegularizedCalculus
import CircularLawSection6.GinibreBBVStieltjes
import CircularLawSection6.GinibreDysonDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual Ginibre regularized mean limits from BBV

The finite-matrix height derivative may be passed under expectation using
the deterministic bound `1 / t` on the Poisson average.  Dominated
convergence then gives the difference of the expected regularized
potentials between two positive heights.  The finite-matrix energy bound
and the proved Dyson large-height endpoint fix the integration constant.

The statements concern the actual Gaussian matrices, on both the common
Gaussian sequence and the finite cyclic sample spaces.  No raw-log limit,
limiting singular law, or eigenvalue correlation formula is assumed.
-/

open MeasureTheory Filter Topology Set Module Arxiv2410V3 TaoVuReplacement
open CircularLawSections56.Section5
open CircularLawSections56.Section5.PublishedSection3Concrete
  (BBVComparisonInput gaussianSequenceLaw ginibreOnSequence)
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6

-- Use the same entrywise measurable structure as the generic matrix
-- calculus.  The imported finite-Ginibre Borel instance is mathematically
-- equal but not definitionally equal to this product structure.
attribute [local instance 2000] CircularLawSection6.complexMatrixMeasurableSpace
  CircularLawSection6.complexMatrixBorelSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Joint measurability in height and the actual random matrix entries.
Division is total, so this measurability statement also includes height zero. -/
theorem measurable_matrixSquaredPoissonAverage_uncurry
    {Ω : Type*} [MeasurableSpace Ω] {A : Ω → Matrix ι ι ℂ} (hA : Measurable A) :
    Measurable (fun q : ℝ × Ω =>
      matrixSquaredSingularAverage (A q.2) (squaredPoissonTest q.1)) := by
  unfold matrixSquaredSingularAverage squaredPoissonTest
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  have hi : i.val < Fintype.card ι := by
    simpa only [finrank_euclideanSpace] using i.isLt
  have hs : Measurable (fun q : ℝ × Ω => (A q.2).toEuclideanLin.singularValues i) :=
    (continuous_matrix_singularValue (ι := ι) ⟨i.val, hi⟩).measurable.comp
      (hA.comp measurable_snd)
  exact measurable_fst.div
    (((hs.pow_const 2).max measurable_const).add (measurable_fst.pow_const 2))

theorem matrixSquaredPoissonAverage_abs_le [Nonempty ι]
    (A : Matrix ι ι ℂ) {t : ℝ} (ht : 0 < t) :
    |matrixSquaredSingularAverage A (squaredPoissonTest t)| ≤ 1 / t := by
  have hn : (finrank ℂ (EuclideanSpace ℂ ι) : ℝ) ≠ 0 := by
    simp only [finrank_euclideanSpace]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold matrixSquaredSingularAverage
  rw [abs_div, abs_of_nonneg
    (Nat.cast_nonneg (finrank ℂ (EuclideanSpace ℂ ι)) :
      (0 : ℝ) ≤ (finrank ℂ (EuclideanSpace ℂ ι) : ℝ))]
  calc
    _ ≤ (∑ i : Fin (finrank ℂ (EuclideanSpace ℂ ι)),
        |squaredPoissonTest t (A.toEuclideanLin.singularValues i ^ 2)|) /
          (finrank ℂ (EuclideanSpace ℂ ι) : ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
    _ ≤ (∑ _i : Fin (finrank ℂ (EuclideanSpace ℂ ι)), (1 / t : ℝ)) /
        (finrank ℂ (EuclideanSpace ℂ ι) : ℝ) :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun i _ => squaredPoissonTest_abs_le ht
          (A.toEuclideanLin.singularValues i ^ 2)) (Nat.cast_nonneg _)
    _ = 1 / t := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_div_cancel_left₀ _ hn

theorem measurable_integral_matrixSquaredPoissonAverage
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {A : Ω → Matrix ι ι ℂ} (hA : Measurable A) :
    Measurable (fun t => ∫ ω, matrixSquaredSingularAverage (A ω)
      (squaredPoissonTest t) ∂μ) :=
  (measurable_matrixSquaredPoissonAverage_uncurry hA).stronglyMeasurable.integral_prod_right'.measurable

theorem norm_integral_matrixSquaredPoissonAverage_le [Nonempty ι]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix ι ι ℂ) {t : ℝ} (ht : 0 < t) :
    ‖∫ ω, matrixSquaredSingularAverage (A ω) (squaredPoissonTest t) ∂μ‖ ≤ 1 / t := by
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (ae_of_all _ fun ω => show
      ‖matrixSquaredSingularAverage (A ω) (squaredPoissonTest t)‖ ≤ 1 / t by
        simpa only [Real.norm_eq_abs] using matrixSquaredPoissonAverage_abs_le (A ω) ht)
  simpa only [probReal_univ, mul_one] using h

/-- Differentiation under expectation uses a deterministic local bound
`2 / t` on the height derivative.  Only finite expected matrix energy is
needed to integrate the regularized potential itself. -/
theorem hasDerivAt_integral_matrixRegularizedPotential [Nonempty ι]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Ω → Matrix ι ι ℂ} (hA : Measurable A)
    (hE : Integrable (fun ω => hilbertSchmidtSq (A ω)) μ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => ∫ ω, matrixRegularizedPotential (A ω) u ∂μ)
      (∫ ω, matrixSquaredSingularAverage (A ω) (squaredPoissonTest t) ∂μ) t := by
  have hs : Ioi (t / 2) ∈ 𝓝 t := isOpen_Ioi.mem_nhds (by linarith)
  have hmeas : ∀ᶠ u in 𝓝 t,
      AEStronglyMeasurable (fun ω => matrixRegularizedPotential (A ω) u) μ := by
    filter_upwards [hs] with u hu
    exact ((measurable_matrixRegularizedPotential
      (lt_trans (half_pos ht) hu)).comp hA).aestronglyMeasurable
  have hderivMeas : AEStronglyMeasurable (fun ω =>
      matrixSquaredSingularAverage (A ω) (squaredPoissonTest t)) μ :=
    ((measurable_matrixSquaredPoissonAverage_uncurry hA).comp
      measurable_prodMk_left).aestronglyMeasurable
  have hbound : ∀ᵐ ω ∂μ, ∀ u ∈ Ioi (t / 2),
      ‖matrixSquaredSingularAverage (A ω) (squaredPoissonTest u)‖ ≤ 2 / t := by
    filter_upwards [] with ω
    intro u hu
    have hu0 : 0 < u := lt_trans (half_pos ht) hu
    have hratio : 1 / u ≤ 2 / t := by
      apply (div_le_div_iff₀ hu0 ht).2
      linarith
    have habs : ‖matrixSquaredSingularAverage (A ω) (squaredPoissonTest u)‖ ≤ 1 / u := by
      simpa only [Real.norm_eq_abs] using matrixSquaredPoissonAverage_abs_le (A ω) hu0
    exact habs.trans hratio
  have hdiff : ∀ᵐ ω ∂μ, ∀ u ∈ Ioi (t / 2),
      HasDerivAt (fun v => matrixRegularizedPotential (A ω) v)
        (matrixSquaredSingularAverage (A ω) (squaredPoissonTest u)) u := by
    filter_upwards [] with ω
    intro u hu
    exact hasDerivAt_matrixRegularizedPotential (A ω) (lt_trans (half_pos ht) hu)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ => 2 / t) hs hmeas
    (integrable_matrixRegularizedPotential hA hE ht) hderivMeas hbound
    (integrable_const (2 / t)) hdiff).2

theorem intervalIntegrable_integral_matrixSquaredPoissonAverage [Nonempty ι]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Ω → Matrix ι ι ℂ} (hA : Measurable A)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t => ∫ ω, matrixSquaredSingularAverage (A ω)
      (squaredPoissonTest t) ∂μ) volume a b := by
  apply (intervalIntegrable_const :
    IntervalIntegrable (fun _ : ℝ => 1 / min a b) volume a b).mono_fun'
      (measurable_integral_matrixSquaredPoissonAverage μ hA).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have hm : 0 < min a b := lt_min ha hb
  exact (norm_integral_matrixSquaredPoissonAverage_le μ A (hm.trans ht.1)).trans
    (one_div_le_one_div_of_le hm ht.1.le)

/-- Exact difference formula for the actual expected regularized
potential between any two positive heights. -/
theorem integral_expectedPoisson_eq_regularized_difference [Nonempty ι]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Ω → Matrix ι ι ℂ} (hA : Measurable A)
    (hE : Integrable (fun ω => hilbertSchmidtSq (A ω)) μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in a..b, ∫ ω, matrixSquaredSingularAverage (A ω) (squaredPoissonTest t) ∂μ) =
      (∫ ω, matrixRegularizedPotential (A ω) b ∂μ) -
        ∫ ω, matrixRegularizedPotential (A ω) a ∂μ := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _
    (intervalIntegrable_integral_matrixSquaredPoissonAverage μ hA ha hb)
  intro t ht
  exact hasDerivAt_integral_matrixRegularizedPotential μ hA hE ((lt_min ha hb).trans_le ht.1)

/-- Expected large-height error, with the exact normalized energy. -/
theorem abs_integral_matrixRegularizedPotential_sub_log_le [Nonempty ι]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A : Ω → Matrix ι ι ℂ} (hA : Measurable A)
    (hE : Integrable (fun ω => hilbertSchmidtSq (A ω)) μ)
    {t : ℝ} (ht : 0 < t) :
    |(∫ ω, matrixRegularizedPotential (A ω) t ∂μ) - Real.log t| ≤
      ((∫ ω, hilbertSchmidtSq (A ω) ∂μ) / (Fintype.card ι : ℝ)) / (2 * t ^ 2) := by
  have hi := integrable_matrixRegularizedPotential hA hE ht
  calc
    _ = |∫ ω, matrixRegularizedPotential (A ω) t - Real.log t ∂μ| := by
      rw [integral_sub hi (integrable_const (Real.log t))]
      simp
    _ ≤ ∫ ω, |matrixRegularizedPotential (A ω) t - Real.log t| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω, hilbertSchmidtSq (A ω) / (2 * (Fintype.card ι : ℝ) * t ^ 2) ∂μ :=
      integral_mono_ae (hi.sub (integrable_const (Real.log t))).abs (hE.div_const _)
        (ae_of_all _ fun ω => abs_matrixRegularizedPotential_sub_log_le (A ω) ht)
    _ = _ := by
      rw [integral_div]
      ring

/-- Differences at finite heights and a common large-height anchor
determine the remaining additive constant. -/
theorem tendsto_of_height_differences_and_largeHeight
    (U : ℕ → ℝ → ℝ) (V E : ℝ → ℝ) (t : ℝ)
    (hdiff : ∀ b, 0 < b → Tendsto (fun n => U n b - U n t)
      atTop (𝓝 (V b - V t)))
    (hanchor : ∀ b, 0 < b → ∀ n, |U n b - Real.log b| ≤ E b)
    (hE : Tendsto E atTop (𝓝 0))
    (hV : Tendsto (fun b => V b - Real.log b) atTop (𝓝 0)) :
    Tendsto (fun n => U n t) atTop (𝓝 (V t)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  have hsmall : ∀ᶠ b in atTop,
      0 < b ∧ E b < ε / 3 ∧ |V b - Real.log b| < ε / 3 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      hE.eventually (gt_mem_nhds hthird),
      hV.abs.eventually (gt_mem_nhds (by simpa only [abs_zero] using hthird))]
      with b hb hEb hVb
    exact ⟨hb, hEb, hVb⟩
  obtain ⟨b, hb, hEb, hVb⟩ := hsmall.exists
  filter_upwards [(hdiff b hb).eventually
    (Metric.ball_mem_nhds (V b - V t) hthird)] with n hn
  have hndiff : |(U n b - U n t) - (V b - V t)| < ε / 3 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hn
  have htriangle : |U n t - V t| ≤ |U n b - Real.log b| + |V b - Real.log b| +
      |(U n b - U n t) - (V b - V t)| := by
    calc
      _ = |(U n b - Real.log b) - (V b - Real.log b) -
          ((U n b - U n t) - (V b - V t))| := by
        congr 1
        ring
      _ ≤ |(U n b - Real.log b) - (V b - Real.log b)| +
          |(U n b - U n t) - (V b - V t)| := abs_sub _ _
      _ ≤ _ := add_le_add (abs_sub _ _) le_rfl
  rw [Real.dist_eq]
  linarith [hanchor b hb n]

namespace GinibreReferenceSources

theorem ginibreOnSequence_measurable (N : ℕ) : Measurable (ginibreOnSequence N) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply _).div_const _

/-- Exact energy transport through the actual cyclic coordinate map. -/
theorem cyclicSamples_shifted_energy (N : ℕ) [NeZero N] (ω : ℕ → ℂ) (z : ℂ) :
    hilbertSchmidtSq (ginibreMatrix N (cyclicSamples N ω) - z • 1) =
      hilbertSchmidtSq (ginibreOnSequence N ω - z • 1) := by
  rw [← cyclicSamples_shifted_matrix N ω z]
  exact (CircularLawSections56.Section6.hilbertSchmidtSq_reindex
    (ZMod.finEquiv N).toEquiv _).symm

theorem ginibreOnSequence_shifted_expected_energy (N : ℕ) [NeZero N] (z : ℂ) :
    Integrable (fun ω => hilbertSchmidtSq (ginibreOnSequence N ω - z • 1))
      gaussianSequenceLaw ∧
      (∫ ω, hilbertSchmidtSq (ginibreOnSequence N ω - z • 1) ∂gaussianSequenceLaw) /
        (N : ℝ) ≤ 2 + 2 * ‖z‖ ^ 2 := by
  have hE := ginibre_shifted_expected_energy N z
  have hi := (cyclicSamples_measurePreserving N).integrable_comp_of_integrable hE.1
  have he := integral_comp_of_measurePreserving_aes (cyclicSamples_measurePreserving N)
    (fun ω => hilbertSchmidtSq (ginibreMatrix N ω - z • 1)) hE.1.aestronglyMeasurable
  simp only [Function.comp_def, cyclicSamples_shifted_energy] at hi he
  exact ⟨hi, by rw [he]; exact hE.2⟩

/-- Exact regularized-potential transport, not merely equality of a
chosen limiting scalar. -/
theorem cyclicSamples_regularized (N : ℕ) [NeZero N] (ω : ℕ → ℂ) (z : ℂ) (t : ℝ) :
    matrixRegularizedPotential (ginibreMatrix N (cyclicSamples N ω) - z • 1) t =
      matrixRegularizedPotential (ginibreOnSequence N ω - z • 1) t := by
  have h := matrixSquaredSingularAverage_reindex (ZMod.finEquiv N).toEquiv.symm
    (ginibreMatrix N (cyclicSamples N ω) - z • 1) (regularizedSquaredLog t)
  change matrixSquaredSingularAverage
    ((ginibreMatrix N (cyclicSamples N ω) - z • 1).submatrix
      (ZMod.finEquiv N) (ZMod.finEquiv N)) (regularizedSquaredLog t) = _ at h
  rw [cyclicSamples_shifted_matrix N ω z] at h
  exact h.symm

theorem ginibre_regularizedMean_eq_cyclic (N : ℕ) [NeZero N] (z : ℂ)
    {t : ℝ} (ht : 0 < t) :
    (∫ ω, matrixRegularizedPotential (ginibreOnSequence N ω - z • 1) t
      ∂gaussianSequenceLaw) =
      ∫ ω, matrixRegularizedPotential (ginibreMatrix N ω - z • 1) t
        ∂cyclicAtomLaw N circularComplexGaussian := by
  have hm : AEStronglyMeasurable (fun ω =>
      matrixRegularizedPotential (ginibreMatrix N ω - z • 1) t)
      (cyclicAtomLaw N circularComplexGaussian) :=
    ((measurable_matrixRegularizedPotential ht).comp
      ((ginibreMatrix_measurable N).sub measurable_const)).aestronglyMeasurable
  have h := integral_comp_of_measurePreserving_aes (cyclicSamples_measurePreserving N)
    (fun ω => matrixRegularizedPotential (ginibreMatrix N ω - z • 1) t) hm
  simpa only [cyclicSamples_regularized] using h

end GinibreReferenceSources

namespace GinibreBBV

open GinibreReferenceSources GinibreDyson

/-- BBV gives the expected derivative of the actual regularized
potential at each positive height. -/
theorem ginibre_meanSquaredPoisson_tendsto_of_bbv
    (hBBV : BBVComparisonInput) (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => ∫ ω, matrixSquaredSingularAverage
      (ginibreOnSequence (N n) ω - z • 1) (squaredPoissonTest t) ∂gaussianSequenceLaw)
      atTop (𝓝 (dysonV z t)) := by
  have heta : 0 < (Complex.I * (t : ℂ)).im := by simpa using ht
  have h := ginibre_meanStieltjes_tendsto_of_bbv hBBV N (fun n => NeZero.pos (N n))
    hN z (Complex.I * (t : ℂ)) heta
  have him := Complex.continuous_im.continuousAt.tendsto.comp h
  change Tendsto (fun n =>
    (∫ ω, stieltjesTrace (ginibreOnSequence (N n) ω) z (Complex.I * (t : ℂ))
      ∂gaussianSequenceLaw).im) atTop (𝓝 (dysonV z t)) at him
  have heq (n : ℕ) :
      (∫ ω, stieltjesTrace (ginibreOnSequence (N n) ω) z (Complex.I * (t : ℂ))
        ∂gaussianSequenceLaw).im =
        ∫ ω, matrixSquaredSingularAverage (ginibreOnSequence (N n) ω - z • 1)
          (squaredPoissonTest t) ∂gaussianSequenceLaw := by
    have hi := integrable_stieltjesTrace (mu := gaussianSequenceLaw)
      (X := ginibreOnSequence (N n))
      (fun i j => show Measurable (fun ω => ginibreOnSequence (N n) ω i j) from
        (measurable_pi_apply _).div_const _) z heta
    calc
      _ = ∫ ω, (stieltjesTrace (ginibreOnSequence (N n) ω) z
          (Complex.I * (t : ℂ))).im ∂gaussianSequenceLaw := by
        simpa only [RCLike.im_eq_complex_im] using (integral_im hi).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simpa only [spectralParameter, Complex.ofReal_zero, zero_add, mul_comm] using
          matrix_stieltjes_im_eq_squaredPoissonAverage (ginibreOnSequence (N n) ω) z ht
  simpa only [heq] using him

/-- Integration of the BBV mean Stieltjes limit between positive heights.
The interval is bounded away from zero, so the deterministic domination
is independent of the matrix size. -/
theorem ginibre_regularizedMean_difference_tendsto_of_bbv
    (hBBV : BBVComparisonInput) (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (z : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n =>
      (∫ ω, matrixRegularizedPotential (ginibreOnSequence (N n) ω - z • 1) b
        ∂gaussianSequenceLaw) -
      ∫ ω, matrixRegularizedPotential (ginibreOnSequence (N n) ω - z • 1) a
        ∂gaussianSequenceLaw) atTop (𝓝 (dysonPotential z b - dysonPotential z a)) := by
  have hm : 0 < min a b := lt_min ha hb
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := a) (b := b) (l := atTop)
    (F := fun n t => ∫ ω, matrixSquaredSingularAverage
      (ginibreOnSequence (N n) ω - z • 1) (squaredPoissonTest t) ∂gaussianSequenceLaw)
    (f := dysonV z) (fun _ => 1 / min a b)
    (Eventually.of_forall fun n =>
      (measurable_integral_matrixSquaredPoissonAverage gaussianSequenceLaw
        ((ginibreOnSequence_measurable (N n)).sub measurable_const)).aestronglyMeasurable)
    (Eventually.of_forall fun n => ae_of_all _ fun t ht =>
      (norm_integral_matrixSquaredPoissonAverage_le gaussianSequenceLaw
        (fun ω => ginibreOnSequence (N n) ω - z • 1) (hm.trans ht.1)).trans
          (one_div_le_one_div_of_le hm ht.1.le))
    intervalIntegrable_const
    (ae_of_all _ fun t ht => ginibre_meanSquaredPoisson_tendsto_of_bbv hBBV N hN z
      (hm.trans ht.1))
  have hid (n : ℕ) := integral_expectedPoisson_eq_regularized_difference gaussianSequenceLaw
    ((ginibreOnSequence_measurable (N n)).sub measurable_const)
    (ginibreOnSequence_shifted_expected_energy (N n) z).1 ha hb
  simpa only [hid, integral_dysonV_eq_sub z ha hb] using hDCT

/-- The actual Ginibre regularized mean at every fixed positive height,
with its integration constant determined by the large-height energy anchor. -/
theorem ginibre_regularizedMean_tendsto_of_bbv
    (hBBV : BBVComparisonInput) (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => ∫ ω, matrixRegularizedPotential
      (ginibreOnSequence (N n) ω - z • 1) t ∂gaussianSequenceLaw)
      atTop (𝓝 (dysonPotential z t)) := by
  have hrate : Tendsto (fun b : ℝ => (2 + 2 * ‖z‖ ^ 2) / (2 * b ^ 2))
      atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_div_atTop
      ((2 + 2 * ‖z‖ ^ 2) / 2)
    apply h.congr'
    exact Eventually.of_forall fun b => by ring
  apply tendsto_of_height_differences_and_largeHeight
    (fun n b => ∫ ω, matrixRegularizedPotential
      (ginibreOnSequence (N n) ω - z • 1) b ∂gaussianSequenceLaw)
    (dysonPotential z) (fun b => (2 + 2 * ‖z‖ ^ 2) / (2 * b ^ 2)) t
    (fun b hb => ginibre_regularizedMean_difference_tendsto_of_bbv hBBV N hN z ht hb)
    _ hrate (tendsto_dysonPotential_sub_log_atTop z)
  intro b hb n
  have h := abs_integral_matrixRegularizedPotential_sub_log_le gaussianSequenceLaw
    ((ginibreOnSequence_measurable (N n)).sub measurable_const)
    (ginibreOnSequence_shifted_expected_energy (N n) z).1 hb
  simp only [Fintype.card_fin] at h
  exact h.trans (div_le_div_of_nonneg_right
    (ginibreOnSequence_shifted_expected_energy (N n) z).2 (by positivity))

/-- The same every-shift mean limit on the actual finite cyclic sample
spaces used by the Section 6 logarithmic moment and cutoff modules. -/
theorem ginibre_cyclic_regularizedMean_tendsto_of_bbv
    (hBBV : BBVComparisonInput) (N : ℕ → ℕ) [∀ n, NeZero (N n)]
    (hN : Tendsto N atTop atTop) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => ∫ ω, matrixRegularizedPotential
      (ginibreMatrix (N n) ω - z • 1) t ∂cyclicAtomLaw (N n) circularComplexGaussian)
      atTop (𝓝 (dysonPotential z t)) := by
  have h := ginibre_regularizedMean_tendsto_of_bbv hBBV N hN z ht
  apply h.congr'
  exact Eventually.of_forall fun n => ginibre_regularizedMean_eq_cyclic (N n) z ht

end GinibreBBV

end CircularLawSection6
