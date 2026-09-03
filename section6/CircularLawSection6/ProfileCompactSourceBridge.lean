import CircularLawSection6.CompactSourceAssembly
import CircularLawSection6.GaussianProfile

/-! # The sampled unit core inherits the compact source cutoff limit

The block amplitudes are constructed from the original sampled profile,
with the inverse width equivalence explicitly applied. Positivity and
normalization are proved, and the actual core law is transported through
the routed matrix. The source inputs concern these concrete small blocks.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CircularLawSection6.NoncompactProfile

theorem coreBandWeight_pos (p : NoncompactProfile) (N d : ℕ) [NeZero N]
    (center : Fin (d + 1)) (W : ℝ) (s : Fin (d + 2)) : 0 < p.coreBandWeight N d center W s :=
  div_pos (p.positive _) (p.rawCoreMass_pos N center.val W)

def coreRoutedAmplitude (p : NoncompactProfile) (N d H : ℕ) [NeZero N]
    (hwidth : d + 2 = 2 * H + 1) (center : Fin (d + 1)) (W : ℝ)
    (s : Fin (2 * H + 1)) : ℂ :=
  (Real.sqrt (p.coreBandWeight N d center W ((finCongr hwidth).symm s)) : ℂ)

theorem coreRoutedAmplitude_normalized (p : NoncompactProfile) (N d H : ℕ) [NeZero N]
    (hwidth : d + 2 = 2 * H + 1) (hfit : d + 2 ≤ N)
    (center : Fin (d + 1)) (hcenter : center.val = H) (W : ℝ) :
    ∑ s, ‖p.coreRoutedAmplitude N d H hwidth center W s‖ ^ 2 = 1 := by
  have hsym : d + 1 = 2 * center.val := by omega
  calc
    _ = ∑ s, p.coreBandWeight N d center W ((finCongr hwidth).symm s) := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [coreRoutedAmplitude, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (p.coreBandWeight_pos N d center W _).le]
    _ = ∑ s, p.coreBandWeight N d center W s := (finCongr hwidth).symm.sum_comp _
    _ = 1 := p.sum_coreBandWeight N d hfit center hsym W

theorem unitCore_cutoff_limit_of_section3_inputs_ae (p : NoncompactProfile)
    (q H m₀ d : ℕ → ℕ) (len : ∀ n, Fin (q n) → ℕ)
    [∀ n j, NeZero (len n j)] [∀ n, NeZero (∑ j, len n j)]
    (hm₀ : ∀ n, 0 < m₀ n) (hfit : ∀ n, 2 * H n + 1 ≤ m₀ n)
    (hsize : ∀ n j, m₀ n ≤ len n j ∧ len n j ≤ 2 * m₀ n)
    (hwidth : ∀ n, d n + 2 = 2 * H n + 1)
    (hglobal : ∀ n, d n + 2 ≤ ∑ j, len n j)
    (center : ∀ n, Fin (d n + 1)) (hcenter : ∀ n, (center n).val = H n)
    (W : ℕ → ℝ) (hratio : Tendsto (fun n => (H n : ℝ) / m₀ n) atTop (𝓝 0))
    {a : ℝ} (ha : 0 < a) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ σ : Measure ℝ, IsProbabilityMeasure σ →
      (∀ᵐ s ∂σ, 0 ≤ s) → Integrable (fun s : ℝ => s ^ 2) σ →
      (∀ M : ℕ → ℕ+, (∀ n, m₀ n ≤ (M n : ℕ) ∧ (M n : ℕ) ≤ 2 * m₀ n) →
        CyclicGinibreCdfInput M H
          (fun n => p.coreRoutedAmplitude (∑ j, len n j) (d n) (H n) (hwidth n) (center n) (W n)) z ∧
        GinibreSquaredTestInput M z σ) →
      Tendsto (fun n => ∫ ω, matrixCutoffPotential
        (p.unitCoreMatrix (∑ j, len n j) (H n) (W n) ω - z • 1) a ∂gaussianProfileLaw (∑ j, len n j))
        atTop (𝓝 (∫ s, Real.log (max s a) ∂σ)) := by
  let b (n : ℕ) := p.coreRoutedAmplitude (∑ j, len n j) (d n) (H n) (hwidth n) (center n) (W n)
  have hb (n : ℕ) : ∑ s, ‖b n s‖ ^ 2 = 1 :=
    p.coreRoutedAmplitude_normalized (∑ j, len n j) (d n) (H n) (hwidth n) (hglobal n)
      (center n) (hcenter n) (W n)
  have htransport := ae_all_iff.2 (fun n => p.unitCore_expected_cutoff_eq_fullBlock_ae
    (len n) (d n) (H n) (hwidth n) (hglobal n) (center n) (hcenter n) (W n) circularComplexGaussian)
  filter_upwards [fullBlock_cutoff_limit_of_section3_inputs_ae q H m₀ len hm₀ hfit hsize b hb hratio ha,
    htransport] with z hz heq
  intro σ hσ hσpos hσ2 hsource
  apply (hz σ hσ hσpos hσ2 hsource).congr'
  exact Eventually.of_forall fun n => (heq n a ha).symm

end CircularLawSection6.NoncompactProfile
