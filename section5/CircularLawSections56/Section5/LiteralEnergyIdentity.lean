import CircularLawSections56.Section5.LiteralEnergyTightness
import CircularLawSections56.Section5.LiteralFreshMeanBound
import CircularLawSections56.Section5.TaperLiteralProfile

/-! # Exact expected energy and normalized Hilbert--Schmidt tightness

For normalized atoms the mean energy is exactly one, not merely bounded.
The square root of energy is exactly the normalized Hilbert--Schmidt norm
appearing in the manuscript. Neither assertion needs bounded density.
-/

open Filter MeasureTheory Topology
open scoped ENNReal BigOperators

noncomputable section
set_option maxHeartbeats 1200000
set_option autoImplicit false

namespace CircularLawSections56.Section5
open Section6 TaoVuReplacement CircularLawSection4

theorem literalIndicatorMatrix_expected_energy
    (k d : ℕ) (hsize : d + 2 ≤ k + 1) (center : Fin (d + 1))
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν) :
    Integrable (fun ω => physicalEnergy (literalIndicatorMatrix k d center profile.b ω))
      (iidMeasure ν ((k + 1) * (d + 2))) ∧
    (∫ ω, physicalEnergy (literalIndicatorMatrix k d center profile.b ω)
      ∂iidMeasure ν ((k + 1) * (d + 2))) = ∫ u : ℂ, ‖u‖ ^ 2 ∂ν := by
  let μ := iidMeasure ν ((k + 1) * (d + 2))
  have hMP (i : ZMod (k + 1)) (s : Fin (d + 2)) :
      MeasurePreserving (fun ω => ω (paperIndicatorFlatIndex (k + 1) d i s)) μ ν :=
    ⟨measurable_pi_apply _, iidMeasure_map_coordinate ν _⟩
  have hterm (i : ZMod (k + 1)) (s : Fin (d + 2)) :
      Integrable (fun ω => profile.q s * ‖ω (paperIndicatorFlatIndex (k + 1) d i s)‖ ^ 2) μ := by
    simpa only [Function.comp_apply] using
      ((hMP i s).integrable_comp_of_integrable hInt).const_mul (profile.q s)
  have hsum : Integrable (fun ω => ∑ i : ZMod (k + 1), ∑ s : Fin (d + 2),
      profile.q s * ‖ω (paperIndicatorFlatIndex (k + 1) d i s)‖ ^ 2) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun s _ => hterm i s
  simp_rw [literalIndicatorMatrix_energy_eq k d hsize center profile hc₀]
  refine ⟨hsum.div_const _, ?_⟩
  rw [integral_div, integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun s _ => hterm i s))]
  have heq (i : ZMod (k + 1)) :
      (∫ ω, ∑ s : Fin (d + 2),
        profile.q s * ‖ω (paperIndicatorFlatIndex (k + 1) d i s)‖ ^ 2 ∂μ) =
        ∫ u : ℂ, ‖u‖ ^ 2 ∂ν := by
    rw [integral_finsetSum _ (fun s _ => hterm i s)]
    simp_rw [integral_const_mul,
      integral_comp_measurePreserving_eq (hMP i _) (fun u : ℂ => ‖u‖ ^ 2) hInt]
    rw [← Finset.sum_mul, profile.normalized, one_mul]
  simp_rw [heq]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp

theorem literalIndicatorMatrix_expected_energy_one
    (k d : ℕ) (hsize : d + 2 ≤ k + 1) (center : Fin (d + 1))
    {c₀ C₀ : ℝ} (profile : PaperIndicatorWeights (d + 1) c₀ C₀) (hc₀ : 0 < c₀)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν = 1) :
    (∫ ω, physicalEnergy (literalIndicatorMatrix k d center profile.b ω)
      ∂iidMeasure ν ((k + 1) * (d + 2))) = 1 :=
  (literalIndicatorMatrix_expected_energy k d hsize center profile hc₀ ν hInt).2.trans hSecond

def normalizedHilbertSchmidtNorm {k : ℕ}
    (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ℝ :=
  Real.sqrt (hilbertSchmidtSq X) / Real.sqrt (k + 1 : ℝ)

theorem normalizedHilbertSchmidtNorm_eq_sqrt_energy {k : ℕ}
    (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    normalizedHilbertSchmidtNorm X = Real.sqrt (physicalEnergy X) := by
  exact (Real.sqrt_div (hilbertSchmidtSq_nonneg X) _).symm

theorem boundedInProbability_sqrt
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hX : BoundedInProbability P X) :
    BoundedInProbability P (fun n ω => Real.sqrt (X n ω)) := by
  intro ε hε
  obtain ⟨C, hC, htail⟩ := hX ε hε
  refine ⟨Real.sqrt C, Real.sqrt_nonneg C, ?_⟩
  filter_upwards [htail] with n hn
  apply lt_of_le_of_lt (measure_mono ?_) hn
  intro ω hω
  change Real.sqrt C < ‖Real.sqrt (X n ω)‖ at hω
  have hs : Real.sqrt C < Real.sqrt (X n ω) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hω
  exact ((Real.sqrt_lt_sqrt_iff hC).1 hs).trans_le (le_abs_self _)

theorem literal_indicator_normalized_hilbertSchmidt_tight
    (d : ℕ → ℕ) (center : ∀ n, Fin (d n + 1))
    {c₀ C₀ : ℕ → ℝ} (profile : ∀ n, PaperIndicatorWeights (d n + 1) (c₀ n) (C₀ n))
    (hc₀ : ∀ n, 0 < c₀ n)
    (ν : ℕ → Measure ℂ) [∀ n, IsProbabilityMeasure (ν n)]
    (hInt : ∀ n, Integrable (fun u : ℂ => ‖u‖ ^ 2) (ν n))
    (hSecond : ∀ n, ∫ u : ℂ, ‖u‖ ^ 2 ∂ν n ≤ 1)
    (hfit : ∀ᶠ n in atTop, d n + 2 ≤ n + 1) :
    BoundedInProbability
      (Measure.infinitePi (fun n => iidMeasure (ν n) ((n + 1) * (d n + 2))))
      (fun n ω => normalizedHilbertSchmidtNorm
        (literalIndicatorMatrix n (d n) (center n) (profile n).b (ω n))) := by
  simp_rw [normalizedHilbertSchmidtNorm_eq_sqrt_energy]
  exact boundedInProbability_sqrt _ _
    (literal_indicator_energy_bounded_in_probability d center profile hc₀ ν hInt hSecond hfit)

theorem taperedMatrix_expected_energy_one
    (p : PolynomialTaperProfile) (k W : ℕ) (hW : 0 < W) (hfit : 2 * W + 1 ≤ k + 1)
    (ν : Measure ℂ) [IsProbabilityMeasure ν]
    (hInt : Integrable (fun u : ℂ => ‖u‖ ^ 2) ν)
    (hSecond : ∫ u : ℂ, ‖u‖ ^ 2 ∂ν = 1) :
    (∫ ω, physicalEnergy (p.literalMatrix k W hW ω)
      ∂iidMeasure ν ((k + 1) * (taperStateDimension W + 2))) = 1 :=
  literalIndicatorMatrix_expected_energy_one k (taperStateDimension W)
    ((PolynomialTaperProfile.literalMatrix_band_fits k W hW).2 hfit)
    (taperCenter W hW) (p.literalWeights W hW) (p.lowerParameter_pos W) ν hInt hSecond

end CircularLawSections56.Section5
