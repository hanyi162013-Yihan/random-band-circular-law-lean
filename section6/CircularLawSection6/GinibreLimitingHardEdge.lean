import CircularLawSection6.PublishedGaussianModel
import CircularLawSection6.SingularValueReindexing
import CircularLawSection6.UniformCyclicSourceBridge

/-! # Linear hard edge for the actual normalized Ginibre limiting law

The existing bounded-test input on cyclic Gaussian samples is transported by
an exact matrix/singular-value identity. All model, moment and density data are
proved. The only extra comparison source is the named BBV literature instance.
-/

open MeasureTheory Filter Topology Set Arxiv2410V3
open CircularLawSections56.Section5
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace CircularLawSection6

def GinibreBBVInput (M : ℕ → ℕ+) (z : ℂ) (comparisonConstant : ℝ) : Prop :=
  ∀ t, 0 < t → ∀ n, External.BBVTheorem28GaussianFreeHypothesis
    (∫ ω, stieltjesTrace (BVH.canonicalCircularizedMatrix (publishedGinibreModel (M n)) ω)
      z (spectralParameter 0 t) ∂BVH.canonicalGaussianMeasure (publishedGinibreModel (M n)))
    (freeDysonStieltjes z (spectralParameter 0 t)) (M n : ℝ) t
    (gaussianSection3ComparisonConstant comparisonConstant)

theorem GinibreSquaredTestInput.toPublished (M : ℕ → ℕ+) (z : ℂ) (σ : Measure ℝ)
    (hweak : GinibreSquaredTestInput M z σ) :
    ∀ φ : ℝ → ℝ, Continuous φ → (∃ B : ℝ, ∀ x, |φ x| ≤ B) →
      TendstoInProbabilityTri (fun n => cyclicAtomLaw (M n) circularComplexGaussian)
        (fun n ω => matrixSquaredSingularAverage ((publishedGinibreModel (M n)).matrix ω - z • 1) φ)
        (∫ s, φ (s ^ 2) ∂σ) := by
  intro φ hφ hbound
  have heq (n : ℕ) (ω : ZMod (M n) × ZMod (M n) → ℂ) :
      matrixSquaredSingularAverage ((publishedGinibreModel (M n)).matrix ω - z • 1) φ =
        matrixSquaredSingularAverage (ginibreMatrix (M n) ω - z • 1) φ := by
    rw [publishedGinibreModel_matrix]
    exact matrixSquaredSingularAverage_shifted_reindex (ZMod.finEquiv (M n)).symm
      (ginibreMatrix (M n) ω) z φ
  exact tendstoInProbabilityTri_congr_ae
    (fun n => cyclicAtomLaw (M n) circularComplexGaussian)
    (fun n ω => matrixSquaredSingularAverage (ginibreMatrix (M n) ω - z • 1) φ)
    (fun n ω => matrixSquaredSingularAverage ((publishedGinibreModel (M n)).matrix ω - z • 1) φ)
    (fun n => ae_of_all _ (fun ω => (heq n ω).symm)) _ (hweak φ hφ hbound)

theorem ginibre_limiting_linearHardEdge (M : ℕ → ℕ+)
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop) (z : ℂ)
    (σ : Measure ℝ) [IsFiniteMeasure σ] (hpos : ∀ᵐ s ∂σ, 0 ≤ s)
    (hweak : GinibreSquaredTestInput M z σ) {comparisonConstant : ℝ}
    (hBBV : GinibreBBVInput M z comparisonConstant) :
    ∀ t, 0 < t → σ.real (Iic t) ≤ 2 * t :=
  published_dense_limiting_hardEdge
    (fun n => cyclicAtomLaw (M n) circularComplexGaussian) circularComplexGaussian
    (fun n => (M n : ℕ)) hM (fun n => publishedGinibreModel (M n)) z σ hpos
    (gaussianSection3ComparisonConstant_ge_eight comparisonConstant)
    (fun n => publishedGinibreModel_bandwidth (M n))
    (fun n => publishedGinibreModel_thirdMoment_bound (M n) comparisonConstant)
    (GinibreSquaredTestInput.toPublished M z σ hweak) hBBV

theorem ginibre_limiting_log_integrable (M : ℕ → ℕ+)
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop) (z : ℂ)
    (σ : Measure ℝ) [IsFiniteMeasure σ] (hpos : ∀ᵐ s ∂σ, 0 ≤ s)
    (hsecond : Integrable (fun s : ℝ => s ^ 2) σ)
    (hweak : GinibreSquaredTestInput M z σ) {comparisonConstant : ℝ}
    (hBBV : GinibreBBVInput M z comparisonConstant) :
    Integrable Real.log σ :=
  integrable_log_of_hardEdge_secondMoment σ (a₀ := 1) (by norm_num) (by norm_num)
    (fun t ht _ => ginibre_limiting_linearHardEdge M hM z σ hpos hweak hBBV t ht) hsecond

theorem ginibre_limiting_logCutoff_identity (M : ℕ → ℕ+)
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop) (z : ℂ)
    (σ : Measure ℝ) [IsFiniteMeasure σ] (hpos : ∀ᵐ s ∂σ, 0 ≤ s)
    (hsecond : Integrable (fun s : ℝ => s ^ 2) σ)
    (hweak : GinibreSquaredTestInput M z σ) {comparisonConstant : ℝ}
    (hBBV : GinibreBBVInput M z comparisonConstant)
    {a : ℝ} (ha : 0 < a) :
    (∫ s, Real.log (max s a) ∂σ) - (∫ s, Real.log s ∂σ) =
      ∫ t in Ioc 0 a, σ.real (Iic t) / t :=
  logCutoff_identity_of_hardEdge_secondMoment σ ha (by norm_num)
    (fun t ht _ => ginibre_limiting_linearHardEdge M hM z σ hpos hweak hBBV t ht)
    hsecond ha le_rfl

theorem ginibre_limiting_logCutoff_error (M : ℕ → ℕ+)
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop) (z : ℂ)
    (σ : Measure ℝ) [IsFiniteMeasure σ] (hpos : ∀ᵐ s ∂σ, 0 ≤ s)
    (hsecond : Integrable (fun s : ℝ => s ^ 2) σ)
    (hweak : GinibreSquaredTestInput M z σ) {comparisonConstant : ℝ}
    (hBBV : GinibreBBVInput M z comparisonConstant)
    {a : ℝ} (ha : 0 < a) :
    0 ≤ (∫ s, Real.log (max s a) ∂σ) - (∫ s, Real.log s ∂σ) ∧
      (∫ s, Real.log (max s a) ∂σ) - (∫ s, Real.log s ∂σ) ≤ 2 * a :=
  logCutoff_error_of_hardEdge_secondMoment σ ha (by norm_num)
    (fun t ht _ => ginibre_limiting_linearHardEdge M hM z σ hpos hweak hBBV t ht)
    hsecond ha le_rfl

end CircularLawSection6
