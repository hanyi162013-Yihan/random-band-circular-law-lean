import CircularLawSection6.GinibreLimitingHardEdge
import CircularLawSection6.GinibreIteratedCutoff

/-! # The limiting singular logarithm equals the classical Ginibre potential

The limits are taken in the correct order: matrix size first, cutoff second.
The bounded singular-law limit, the proved hard edge, and the explicit BC12
raw/inverse-moment sources identify the full logarithmic integral.
-/

open MeasureTheory Filter Topology
open CircularLawSections56.Section5
noncomputable section

namespace CircularLawSection6

theorem iterated_cutoff_identifies_limit (F : ℕ → ℕ → ℝ) (raw G : ℕ → ℝ)
    (target L : ℝ)
    (hF : ∀ R, Tendsto (F R) atTop (𝓝 (G R)))
    (hraw : Tendsto raw atTop (𝓝 target)) (hG : Tendsto G atTop (𝓝 L))
    (hlower : ∀ R, ∀ᶠ n in atTop, raw n ≤ F R n)
    (hupper : ∀ ε, 0 < ε → ∀ᶠ R in atTop, ∀ᶠ n in atTop, F R n ≤ raw n + ε) :
    L = target := by
  apply le_antisymm
  · by_contra h
    have hgap : 0 < (L - target) / 2 := by linarith
    have hb : ∀ᶠ R in atTop, G R ≤ target + (L - target) / 2 := by
      filter_upwards [hupper _ hgap] with R hR
      exact le_of_tendsto_of_tendsto (hF R) (hraw.add_const _) hR
    have hle := le_of_tendsto hG hb
    linarith
  · apply ge_of_tendsto hG
    exact Eventually.of_forall fun R => le_of_tendsto_of_tendsto hraw (hF R) (hlower R)

theorem ginibre_limiting_logPotential_eq_raw_limit_ae (M : ℕ → ℕ+)
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ σ : Measure ℝ, IsProbabilityMeasure σ →
      (∀ᵐ s ∂σ, 0 ≤ s) → Integrable (fun s : ℝ => s ^ 2) σ →
      GinibreSquaredTestInput M z σ → ∀ comparisonConstant : ℝ,
      GinibreBBVInput M z comparisonConstant →
      ∀ target : ℝ,
        TendstoInProbabilityTri (fun n => cyclicAtomLaw (M n) circularComplexGaussian)
          (fun n ω => matrixRawPotential (ginibreMatrix (M n) ω - z • 1)) target →
        ∀ p : ℝ, 0 < p → BC12GinibreNegativeMomentTightnessTri (fun n => (M n : ℕ)) z p →
          (∫ s, Real.log s ∂σ) = target := by
  have hdet := ae_all_iff.2 (fun n => ae_shifted_matrix_det_ne_zero
    (cyclicAtomLaw (M n) circularComplexGaussian) (ginibreMatrix (M n)) (ginibreMatrix_measurable (M n)))
  filter_upwards [hdet, ginibre_fixedCutoff_mean_of_squared_test_ae (fun n => (M n : ℕ)),
    ginibre_iterated_cutoff_error_ae (fun n => (M n : ℕ)) hM] with z hdz hfixed hiter
  intro σ hσ hpos hsecond hweak comparisonConstant hBBV target hraw p hp hnegative
  let : IsProbabilityMeasure σ := hσ
  let a (R : ℕ) : ℝ := 1 / (R + 1 : ℝ)
  have ha (R : ℕ) : 0 < a R := by dsimp [a]; positivity
  have ha1 (R : ℕ) : a R ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < R + 1)).2
    nlinarith [Nat.cast_nonneg (α := ℝ) R]
  have ha0 : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hloglimit := logCutoff_tendsto_of_hardEdge σ (a₀ := 1) (by norm_num) (by norm_num)
    (fun t ht _ => ginibre_limiting_linearHardEdge M hM z σ hpos hweak hBBV t ht)
    hsecond a ha ha0
  apply iterated_cutoff_identifies_limit
    (fun R n => ∫ ω, matrixCutoffPotential (ginibreMatrix (M n) ω - z • 1) (a R)
      ∂cyclicAtomLaw (M n) circularComplexGaussian)
    (fun n => ∫ ω, matrixRawPotential (ginibreMatrix (M n) ω - z • 1)
      ∂cyclicAtomLaw (M n) circularComplexGaussian)
    (fun R => ∫ s, Real.log (max s (a R)) ∂σ) target (∫ s, Real.log s ∂σ)
    (fun R => hfixed σ hσ hpos hsecond hweak (a R) (ha R))
    (ginibre_raw_mean_of_probability (fun n => (M n : ℕ)) hM z hraw) hloglimit
  · intro R
    filter_upwards with n
    apply integral_mono_ae
      ((ginibre_raw_memLp (M n) z).integrable (by norm_num : (1 : ENNReal) ≤ 2))
      (integrable_matrixCutoffPotential (cyclicAtomLaw (M n) circularComplexGaussian)
        (fun ω => ginibreMatrix (M n) ω - z • 1)
        ((ginibreMatrix_measurable (M n)).sub measurable_const) (hdz n)
        (ginibre_shifted_expected_energy (M n) z).1 (ha R))
    filter_upwards [hdz n] with ω hω
    exact matrixRawPotential_le_cutoff _ hω _
  · exact hiter target hraw p hp hnegative a ha ha1 ha0

end CircularLawSection6
